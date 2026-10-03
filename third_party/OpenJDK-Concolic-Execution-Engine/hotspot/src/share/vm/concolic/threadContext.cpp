#ifdef ENABLE_CONCOLIC

#include "concolic/threadContext.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/fieldTraverser.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/reference/symbolicObject.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/reference/symbolicBigDecimal.hpp"
#include "concolic/reference/symbolicStream.hpp"
#include "utilities/exceptions.hpp"
#include "classfile/javaClasses.hpp"
#include "runtime/osThread.hpp"

#include <algorithm>

namespace {

/**
 * Opens one concolic envelope.
 *
 * Every envelope this file publishes starts with the same five members: the
 * schema it conforms to, its kind, the session whose ids it names, and
 * whether the context that produced it is still recording.  A NULL context is
 * a legitimate producer -- "no context is attached" -- and answers all of
 * them, which is what lets the live and the no-context shapes be one writer
 * rather than two that drift.
 */
void begin_envelope(rapidjson::Writer<rapidjson::StringBuffer> &writer,
                    const char *kind, const ThreadContext *context) {
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String(kind);
  // The symbolic universe these ids belong to.  An id is only comparable
  // against another id minted by the same session, so every envelope that
  // carries ids names the session that minted them.
  writer.Key("sessionId");
  writer.Int64(GlobalSymbolicSession::session_id());
  writer.Key("active");
  writer.Bool(context != NULL && !context->is_aborted());
  writer.Key("aborted");
  writer.Bool(context != NULL && context->is_aborted());
  writer.Key("abortReason");
  writer.String(context == NULL ? "" : context->get_abort_reason().c_str());
}

/** Closes one envelope, emitting its expression table when it has one. */
void end_envelope(rapidjson::Writer<rapidjson::StringBuffer> &writer,
                  VmExpressionArtifactScope *artifact) {
  if (artifact != NULL) artifact->write_table(writer);
  writer.EndObject();
}

} // anonymous namespace

ThreadContext::ThreadContext(JavaThread *jt, jlong context_id)
    : _thread(jt), _s_stack(jt),
      _path_condition_enabled(true), _path_condition_admitted(true),
      _path_condition_pause_depth(0),
      _aborted(false),
      _context_id(context_id),
      _owner_java_thread_id(jt == NULL || jt->threadObj() == NULL
          ? 0 : java_lang_Thread::thread_id(jt->threadObj())),
      _owner_os_thread_id(jt == NULL || jt->osthread() == NULL
          ? 0 : (jlong) jt->osthread()->thread_id()),
      _pending_branch_active(false),
      _pending_branch_event_id(0), _pending_branch_owner_frame(NULL),
      _pending_branch_occurrence(0) {
  _pending_view_removal_argument = NULL;
  _streams = NULL;
  guarantee(GlobalSymbolicSession::is_open(),
            "a thread context requires an open symbolic session");
}

bool ThreadContext::branch_site_decided(const std::string &site_id) const {
  if (site_id.empty() || _region_stack.empty()) return false;
  const RegionFrame *frame = _region_stack.back();
  for (size_t index = 0; index < frame->branch_events.size(); ++index) {
    if (frame->branch_events[index].site_id == site_id) return true;
  }
  return false;
}

bool ThreadContext::path_guarded() const {
  return !_region_stack.empty()
      && _region_stack.back()->branch_path_condition.size() > 0;
}

Expression *ThreadContext::path_guard() {
  return _region_stack.empty()
      ? NULL : _region_stack.back()->branch_path_condition.conjunction();
}

void ThreadContext::push_region(const char *region_id, const char *task_id) {
  RegionFrame *frame = new RegionFrame();
  frame->region_id = region_id == NULL ? "" : region_id;
  frame->task_id = task_id == NULL ? "" : task_id;
  _region_stack.push_back(frame);
}

int ThreadContext::pop_region() {
  if (!_region_stack.empty()) {
    RegionFrame *frame = _region_stack.back();
    _region_stack.pop_back();
    // RegionFrame destroys only its Condition wrappers and serialization
    // caches.  Their Expression nodes remain owned by the symbolic session.
    delete frame;
  }
  return (int) _region_stack.size();
}

const std::string &ThreadContext::get_region_id() const {
  static const std::string NO_REGION;
  return _region_stack.empty() ? NO_REGION : _region_stack.back()->region_id;
}

const std::string &ThreadContext::get_task_id() const {
  static const std::string NO_TASK;
  return _region_stack.empty() ? NO_TASK : _region_stack.back()->task_id;
}

void ThreadContext::set_region_enter_event(jlong event_id) {
  if (_region_stack.empty()) return;
  _region_stack.back()->enter_event_id = event_id;
}

jlong ThreadContext::region_enter_event() const {
  return _region_stack.empty() ? 0 : _region_stack.back()->enter_event_id;
}

std::string ThreadContext::serialize_path_condition_range(
    ThreadContext *context, int start, int end) {
  using namespace rapidjson;
  const int watermark =
      context == NULL ? 0 : context->_path_condition.size();
  if (start < 0) start = 0;
  if (end > watermark) end = watermark;
  if (end < start) end = start;

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  VmExpressionArtifactScope expression_artifact;
  begin_envelope(writer, "CONCOLIC_PATH_CONDITION_RANGE", context);
  writer.Key("contextId");
  writer.Int64(context == NULL ? 0 : context->_context_id);
  writer.Key("ownerJavaThreadId");
  writer.Int64(context == NULL ? 0 : context->_owner_java_thread_id);
  writer.Key("startIndex");
  writer.Int(start);
  writer.Key("endIndex");
  writer.Int(end);
  writer.Key("pathConditionWatermark");
  writer.Int(watermark);
  writer.Key("conditionCount");
  writer.Int(end - start);
  // This window's conjunction is not restated here.  It is by construction the
  // left fold of `conditions` in the order they appear, so inlining it copied
  // every condition of the window a second time into the same document --
  // measured at 3,291,838 of 6,591,143 characters for one whole-thread window
  // -- and built one op_land node per condition to do it.  Nothing is dropped
  // and nothing is sampled: `conditions` is the complete window and
  // `conditionCount` its exact length, so a reader that wants the guard folds
  // what it already has, and an empty window folds to `true`.
  writer.Key("conditions");
  int emitted_range_conditions = 0;
  if (context == NULL) {
    writer.StartArray();
    writer.EndArray();
  } else {
    emitted_range_conditions =
        context->_path_condition.serialize_range(writer, start, end);
  }
  // What `conditions` actually holds.  serialize_range() emits one entry per
  // index it visits -- a truncated or absent expression becomes a named
  // TruncatedExpression rather than a hole -- so this equals conditionCount
  // whenever the requested window lies inside the recorded prefix, and is
  // short only when the caller asked past the watermark.  A reader that
  // checks cardinality checks it against this, and never has to infer
  // truncation from a length.
  writer.Key("emittedConditionCount");
  writer.Int(emitted_range_conditions);
  writer.Key("authority");
  writer.String("VM_THREAD_PATH_CONDITION_RANGE_V1");
  end_envelope(writer, &expression_artifact);
  return std::string(buffer.GetString(), buffer.GetLength());
}

void ThreadContext::abort_symbolic_execution(const char *reason) {
  if (_aborted) {
    return;
  }
  _aborted = true;
  _abort_reason = reason == NULL ? "UNSPECIFIED" : reason;
  _path_condition_enabled = false;
  _path_condition_admitted = false;
  cancel_pending_branch();
}

jlong ThreadContext::mark_branch(const char *site_id, int occurrence) {
  // A malformed/missed after-hook must not let an old marker authorize a
  // later branch.  Replacing the single pending slot is deterministic and
  // fail-closed: only the newly returned id can be claimed by Java.
  const ZeroFrame *owner_frame = _s_stack.marker_owner_frame();
  if (owner_frame == NULL) {
    cancel_pending_branch();
    return 0;
  }
  _pending_branch_event_id = GlobalSymbolicSession::next_event_id();
  _pending_branch_site_id = site_id == NULL ? "" : site_id;
  _pending_branch_occurrence = occurrence;
  _pending_branch_owner_frame = owner_frame;
  _pending_branch_active = true;
  return _pending_branch_event_id;
}

void ThreadContext::cancel_pending_branch() {
  _pending_branch_active = false;
  _pending_branch_event_id = 0;
  _pending_branch_owner_frame = NULL;
  _pending_branch_site_id.clear();
  _pending_branch_occurrence = 0;
}

void ThreadContext::cancel_pending_branch_for_frame(
    const ZeroFrame *owner_frame) {
  if (_pending_branch_active && owner_frame != NULL
      && _pending_branch_owner_frame == owner_frame) {
    cancel_pending_branch();
  }
}

void ThreadContext::record_branch_condition(Expression *expression,
                                             bool outcome, int opcode) {
  exp_list_t expressions;
  if (expression != NULL) {
    expressions.push_back(expression);
  }
  record_branch_conditions(expressions, outcome, opcode);
}

void ThreadContext::record_branch_conditions(const exp_list_t &expressions,
                                              bool outcome, int opcode) {
  if (_aborted || !_path_condition_enabled || !_path_condition_admitted
      || _path_condition_pause_depth > 0 || _region_stack.empty()) {
    // A marker identifies one concrete branch execution, not the next branch
    // after recording happens to resume.
    cancel_pending_branch();
    return;
  }

  RegionFrame *frame = _region_stack.back();

  std::vector<int> direct_indices;
  for (size_t index = 0; index < expressions.size(); ++index) {
    if (expressions[index] != NULL) {
      direct_indices.push_back(_path_condition.add(expressions[index]));
    }
  }

  // The VM marker is issued through a native System call.  Only a branch in
  // its non-native Java caller may claim it.  Nested accessors are allowed to
  // return a symbolic guard value, but their own implementation branches (or
  // Throwable construction branches) are unrelated to the marked site.
  if (_pending_branch_active
      && _s_stack.is_current_frame(_pending_branch_owner_frame)) {
    // The full path condition above keeps every solver fact.  The writer
    // guard is a distinct channel: only a branch marker owned by this frame
    // proves that these predicates selected control flow in the region.
    Expression *guard = NULL;
    for (size_t index = 0; index < expressions.size(); ++index) {
      if (expressions[index] != NULL) {
        frame->branch_path_condition.add(expressions[index]);
        // The guard of a control-dependent container removal is this marked
        // branch's predicate.  A site with several conjuncts folds to their
        // conjunction; the common case is a single comparison.
        guard = guard == NULL ? expressions[index]
            : (Expression *) new OpSymExpression(guard, expressions[index],
                                                 op_land);
      }
    }
    // Arm the current iteration element (if any) with this predicate.  Only a
    // marked branch reaches here, so an unmarked internal comparison during
    // iteration never turns an ordinary remove into a conditional one.
    note_conditional_removal_guard(guard);
    BranchEvent event;
    event.event_id = _pending_branch_event_id;
    event.site_id = _pending_branch_site_id;
    event.occurrence = _pending_branch_occurrence;
    event.outcome = outcome;
    event.opcode = opcode;
    event.code_position = get_current_code_pos();
    event.condition_indices = direct_indices;
    frame->branch_events.push_back(event);
    cancel_pending_branch();
  }

}

std::string ThreadContext::serialize_branch_events(
    const ThreadContext *context) {
  return serialize_branch_events_from(context, 0);
}

std::string ThreadContext::serialize_unread_branch_events(
    ThreadContext *context) {
  RegionFrame *frame = (context == NULL || context->_region_stack.empty())
      ? NULL : context->_region_stack.back();
  if (frame == NULL) return serialize_branch_events_from(context, 0);
  std::string unread =
      serialize_branch_events_from(context, frame->branch_events_read);
  frame->branch_events_read = frame->branch_events.size();
  return unread;
}

std::string ThreadContext::serialize_branch_events_from(
    const ThreadContext *context, size_t first) {
  using namespace rapidjson;
  const RegionFrame *frame =
      (context == NULL || context->_region_stack.empty())
          ? NULL : context->_region_stack.back();
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  begin_envelope(writer, "CONCOLIC_THREAD_BRANCH_EVENTS", context);
  writer.Key("contextId");
  writer.Int64(context == NULL ? 0 : context->_context_id);
  writer.Key("ownerJavaThreadId");
  writer.Int64(context == NULL ? 0 : context->_owner_java_thread_id);
  writer.Key("ownerOsThreadId");
  writer.Int64(context == NULL ? 0 : context->_owner_os_thread_id);
  writer.Key("regionId");
  writer.String(context == NULL ? "" : context->get_region_id().c_str());
  writer.Key("taskId");
  writer.String(context == NULL ? "" : context->get_task_id().c_str());
  writer.Key("regionDepth");
  writer.Int(context == NULL ? 0 : context->region_depth());
  writer.Key("events");
  writer.StartArray();
  const size_t event_count = frame == NULL ? 0 : frame->branch_events.size();
  for (size_t index = first; index < event_count; ++index) {
    const BranchEvent &event = frame->branch_events[index];
    writer.StartObject();
    writer.Key("eventId");
    writer.Int64(event.event_id);
    writer.Key("siteId");
    writer.String(event.site_id.c_str());
    writer.Key("occurrence");
    writer.Int(event.occurrence);
    writer.Key("outcome");
    writer.Bool(event.outcome);
    writer.Key("opcode");
    writer.Int(event.opcode);
    writer.Key("codePosition");
    writer.String(event.code_position.c_str());
    writer.Key("conditionIndices");
    writer.StartArray();
    for (size_t condition = 0;
         condition < event.condition_indices.size(); ++condition) {
      writer.Int(event.condition_indices[condition]);
    }
    writer.EndArray();
    writer.Key("conditionCount");
    writer.Int((int) event.condition_indices.size());
    writer.Key("authority");
    writer.String("VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1");
    writer.EndObject();
  }
  writer.EndArray();
  // No expressions are serialized here: an event names path-condition indices
  // rather than nodes, so this envelope carries no expression table.
  end_envelope(writer, NULL);
  return std::string(buffer.GetString(), buffer.GetLength());
}

ThreadContext::~ThreadContext() {
  // Only this thread's own execution state is released here.  Object shadows,
  // detached identities and container states belong to the session and must
  // survive one thread finishing its region.
  while (!_region_stack.empty()) {
    RegionFrame *frame = _region_stack.back();
    _region_stack.pop_back();
    delete frame;
  }
  _path_condition.gc();
  delete _streams;
}

StreamTable *ThreadContext::streams(bool create) {
  if (_streams == NULL && create) _streams = new StreamTable();
  return _streams;
}

void ThreadContext::note_model_gap(const std::string &name) {
  if (_region_stack.empty()) return;
  RegionFrame *frame = _region_stack.back();
  const std::pair<std::string, std::string> gap(name, get_current_code_pos());
  // A bounded list: a model in a loop names its gap once per site.
  if (frame->model_gaps.size() >= 64
      || std::find(frame->model_gaps.begin(), frame->model_gaps.end(), gap)
         != frame->model_gaps.end()) {
    return;
  }
  frame->model_gaps.push_back(gap);
}

std::string ThreadContext::serialize_model_gaps() const {
  using namespace rapidjson;
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartArray();
  if (!_region_stack.empty()) {
    const RegionFrame *frame = _region_stack.back();
    for (size_t index = 0; index < frame->model_gaps.size(); ++index) {
      writer.StartObject();
      writer.Key("name");
      writer.String(frame->model_gaps[index].first.c_str());
      writer.Key("site");
      writer.String(frame->model_gaps[index].second.c_str());
      writer.EndObject();
    }
  }
  writer.EndArray();
  return std::string(buffer.GetString(), buffer.GetLength());
}

// ---------------------------------------------------------------------------
// Shadow-heap forwarders
//
// Object shadows, detached identities and container states describe objects,
// not threads, so the session owns them (sessionSymbolicHeap.hpp).  These
// forwarders keep the thread context as the single entry point every existing
// call site already uses, which is what lets those call sites reach a shared
// heap without being rewritten.
// ---------------------------------------------------------------------------

SessionSymbolicHeap &ThreadContext::heap() const {
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  guarantee(heap != NULL, "the symbolic session owning this context is closed");
  return *heap;
}

Expression *ThreadContext::track_container(
    oop container, const char *shape, const std::string &prefix) {
  return heap().track_container(container, shape, prefix);
}

Expression *ThreadContext::container_state(oop container, const char *shape) {
  return heap().container_state(container, shape);
}

sym_rid_t ThreadContext::canonical_container_id(oop container) const {
  return heap().canonical_container_id(container);
}

Expression *ThreadContext::find_container_state(oop container) const {
  return heap().find_container_state(container);
}

void ThreadContext::set_container_state(oop container, Expression *state) {
  heap().set_container_state(container, state);
}

void ThreadContext::forget_container_state(oop container) {
  heap().forget_container_state(container);
}

void ThreadContext::write_array_element(arrayOop array, int index,
                                        Expression *expression,
                                        const ElementWord &word) {
  heap().write_array_element(array, index, expression, word);
}

void ThreadContext::alias_container(oop derived, oop owner) {
  heap().alias_container(derived, owner);
}

int ThreadContext::next_container_position(oop cursor) {
  return heap().next_container_position(cursor);
}

int ThreadContext::current_container_position(oop cursor) {
  return heap().current_container_position(cursor);
}

int ThreadContext::current_container_index(oop cursor) {
  return heap().current_container_index(cursor);
}

int ThreadContext::next_container_removal_position(oop cursor) {
  return heap().next_container_removal_position(cursor);
}

sym_rid_t ThreadContext::name_reference(oop obj) {
  return heap().name_reference(obj);
}

SymInstance *ThreadContext::get_or_alloc_sym_inst(oop obj) {
  return heap().get_or_alloc_sym_inst(obj);
}

SymInstance *ThreadContext::alloc_sym_inst(oop obj) {
  return heap().alloc_sym_inst(obj);
}

SymInstance *ThreadContext::get_sym_inst(sym_rid_t sym_rid) {
  return heap().get_sym_inst(sym_rid);
}

SymInstance *ThreadContext::find_sym_inst(oop obj) const {
  return heap().find_sym_inst(obj);
}

bool ThreadContext::requires_detached_object_shadow(oop obj) const {
  return heap().requires_detached_object_shadow(obj);
}

SymArr *ThreadContext::get_or_alloc_sym_array(arrayOop array,
                                              Expression *length_exp,
                                              bool named) {
  return heap().get_or_alloc_sym_array(array, length_exp, named);
}

SymArr *ThreadContext::alloc_sym_array(arrayOop array, Expression *length_exp) {
  return heap().alloc_sym_array(array, length_exp);
}

SymArr *ThreadContext::get_sym_array(sym_rid_t sym_rid) {
  return heap().get_sym_array(sym_rid);
}

SymArr *ThreadContext::find_sym_array(arrayOop array_obj) const {
  return heap().find_sym_array(array_obj);
}

void ThreadContext::symbolize_recursive(oop obj) {
  if (jvm_shared_object(obj)) return;
  FieldSymbolizer field_symbolzier(obj, *this);
  field_symbolzier.do_recursive();
  if (obj != NULL && obj->is_array()) {
    SymArr *array = find_sym_array((arrayOop)obj);
    if (array != NULL) array->mark_semantic_expression();
  } else if (obj != NULL) {
    SymInstance *instance = find_sym_inst(obj);
    if (instance != NULL) instance->mark_semantic_expression();
  }
}

void ThreadContext::symbolize_recursive(oop obj, std::string prefix) {
  // A JVM-shared identity never carries a shadow (jvm_shared_object): no
  // mint, no mark on one another use made, and the region's gate stays as
  // it was.  A mint is an input: only then does the gate open.
  if (jvm_shared_object(obj)) return;
  set_pc_admitted(true);
  FieldSymbolizer field_symbolzier(obj, *this, prefix);
  field_symbolzier.do_recursive();
  if (obj != NULL && obj->is_array()) {
    SymArr *array = find_sym_array((arrayOop)obj);
    if (array != NULL) {
      array->set_ref_exp(new FieldSymbolExp(
          array->get_sym_rid(), prefix, T_ARRAY));
      array->mark_semantic_expression();
    }
  } else if (obj != NULL) {
    SymInstance *instance = find_sym_inst(obj);
    if (instance != NULL) instance->mark_semantic_expression();
    ResourceMark rm;
    BasicType boxed_type = primitive_target(
        std::string(obj->klass()->name()->as_C_string()));
    if (instance != NULL
        && obj->klass()->name() != vmSymbols::java_lang_String()
        && boxed_type == T_ILLEGAL) {
      // A boxed primitive's SymPrimitive::_exp is its value shadow.  The
      // recursive field walk above has already assigned that shadow the
      // wrapper's primitive type; replacing it with an object-typed identity
      // makes intValue()/booleanValue()/... return a reference expression.
      // Only ordinary objects need this prefix-based reference identity.
      instance->set_ref_exp(new FieldSymbolExp(
          instance->get_sym_rid(), prefix, T_OBJECT));
    }
  }
}

void ThreadContext::symbolize_field(Handle handle, std::string field_name,
                                    std::string prefix) {
  if (jvm_shared_object(handle())) return;
  set_pc_admitted(true);
  FieldSymbolizer field_symbolizer(handle(), *this, prefix, field_name);
  field_symbolizer.do_once();
  SymInstance *owner = find_sym_inst(handle());
  if (owner != NULL) owner->mark_semantic_expression();
}

void ThreadContext::symbolize_exact_field(
    Handle owner, std::string declaring_class, std::string field_name,
    std::string descriptor, std::string prefix) {
  if (jvm_shared_object(owner())) return;
  set_pc_admitted(true);
  FieldSymbolizer field_symbolizer(
      owner(), *this, prefix, declaring_class, field_name, descriptor);
  field_symbolizer.do_once();
  SymInstance *instance = find_sym_inst(owner());
  if (instance != NULL) instance->mark_semantic_expression();
}

bool ThreadContext::current_code_site(CodeSite *site) {
  if (site == NULL) return false;
  *site = CodeSite();
  ShadowStack &stack = get_shadow_stack();
  if (!stack.has_frames()) return false;
  // The innermost frame that HAS a bytecode position.  A native frame is
  // skipped rather than reported with bci -1: an event published from inside
  // a VM entry (`System.symbolizeExactField`, `System.attachExpression`)
  // stands on that entry's *call site*, which is the bytecode the consumer's
  // woven site id names too, and `java/lang/System.symbolizeExactField:-1`
  // would name no site at all while looking like one.
  const ZeroFrame *zero_frame = stack.get_last_frame().get_zero_frame();
  Method *method = NULL;
  address bcp = NULL;
  while (zero_frame != NULL) {
    if (zero_frame->is_interpreter_frame()) {
      interpreterState istate =
          zero_frame->as_interpreter_frame()->interpreter_state();
      Method *candidate = istate->method();
      if (candidate != NULL && !candidate->is_native()
          && istate->bcp() != NULL) {
        method = candidate;
        bcp = istate->bcp();
        break;
      }
    }
    zero_frame = zero_frame->next();
  }
  if (method == NULL || method->method_holder() == NULL) return false;
  ResourceMark rm;
  Symbol *holder = method->method_holder()->name();
  Symbol *name = method->name();
  Symbol *descriptor = method->signature();
  if (holder == NULL || name == NULL || descriptor == NULL) return false;
  site->class_name = holder->as_C_string();
  site->method_name = name->as_C_string();
  site->method_descriptor = descriptor->as_C_string();
  site->bci = method->bci_from(bcp);
  return true;
}

std::string ThreadContext::get_current_code_pos() {
  // Stack-local, not static: several attached threads reach this from
  // record_branch_conditions at the same time, and one process-global buffer
  // would let them interleave each other's code positions.
  static const int SIZE = 1024;
  char buf[SIZE];

  stringStream ss(buf, SIZE);

  const ZeroFrame *zero_frame = get_shadow_stack().get_last_frame().get_zero_frame();
  while (!zero_frame->is_interpreter_frame()) {
    zero_frame = zero_frame->next();
  }
  interpreterState istate = zero_frame->as_interpreter_frame()->interpreter_state();
  address bcp = istate->bcp();

  Method *method = istate->method();
  int bci = -1;
  if (bcp != NULL) {
    bci = method->bci_from(bcp);
  }

  method->print_name(&ss);
  ss.print(":%d", bci);

  return std::string(buf, ss.size());
}

PathCondition &ThreadContext::get_path_condition() {
  return _path_condition;
}

void ThreadContext::set_pc_admitted(bool pathConditionAdmitted) {
  if (!_aborted) {
    _path_condition_admitted = pathConditionAdmitted;
  }
}

int ThreadContext::pause_path_condition_recording() {
  ++_path_condition_pause_depth;
  return _path_condition_pause_depth;
}

int ThreadContext::resume_path_condition_recording() {
  if (_path_condition_pause_depth > 0) {
    --_path_condition_pause_depth;
  }
  return _path_condition_pause_depth;
}

#endif
