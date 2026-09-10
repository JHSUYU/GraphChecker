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
#include "utilities/vmError.hpp"
#include "utilities/exceptions.hpp"
#include "concolic/reference/symbolicNDFunc.hpp"
#include "classfile/javaClasses.hpp"
#include "runtime/osThread.hpp"
#include <cstdio>

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
      _branch_sequence(0),
      _pending_branch_active(false),
      _pending_branch_event_id(0), _pending_branch_owner_frame(NULL),
      _pending_branch_occurrence(0) {
  guarantee(GlobalSymbolicSession::is_open(),
            "a thread context requires an open symbolic session");
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

std::string ThreadContext::get_path_condition_range(int start, int end) {
  using namespace rapidjson;
  const int watermark = _path_condition.size();
  if (start < 0) start = 0;
  if (end > watermark) end = watermark;
  if (end < start) end = start;

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  VmExpressionArtifactScope expression_artifact;
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("CONCOLIC_PATH_CONDITION_RANGE");
  writer.Key("active");
  writer.Bool(!_aborted);
  writer.Key("aborted");
  writer.Bool(_aborted);
  writer.Key("abortReason");
  writer.String(_abort_reason.c_str());
  writer.Key("contextId");
  writer.Int64(_context_id);
  writer.Key("ownerJavaThreadId");
  writer.Int64(_owner_java_thread_id);
  writer.Key("startIndex");
  writer.Int(start);
  writer.Key("endIndex");
  writer.Int(end);
  writer.Key("pathConditionWatermark");
  writer.Int(watermark);
  writer.Key("conditionCount");
  writer.Int(end - start);
  writer.Key("conditions");
  const int emitted_range_conditions =
      _path_condition.serialize_range(writer, start, end);
  // What `conditions` actually holds.  serialize_range() emits one entry per
  // index it visits -- a truncated or absent expression becomes a named
  // TruncatedExpression rather than a hole -- so this equals conditionCount
  // whenever the requested window lies inside the recorded prefix, and is
  // short only when the caller asked past the watermark.  A reader that
  // checks cardinality checks it against this, and never has to infer
  // truncation from a length.
  writer.Key("emittedConditionCount");
  writer.Int(emitted_range_conditions);
  // Where this window's conjunction is, rather than a second copy of it.
  //
  // The fold used to be inlined here as `conjunction`, and it is by
  // construction the left fold of `conditions` in the order they appear:
  // both walk exactly the recorded conditions of [startIndex, endIndex), in
  // index order, and the fold combines them with `&&` associating to the
  // left.  Inlining it therefore restated every condition of the window a
  // second time in the same document -- measured at 3,291,838 of 6,591,143
  // characters for one whole-thread window, with 277 `&&` nodes -- and built
  // one op_land node per condition to do it.
  //
  // Nothing is dropped and nothing is sampled: `conditions` is the complete
  // window and `conditionCount` its exact length, so a reader that wants the
  // guard folds what it already has, and an empty window folds to the empty
  // conjunction -- which denotes `true` and needs no node.
  writer.Key("conjunctionInline");
  writer.Bool(false);
  writer.Key("conjunctionSource");
  writer.String("conditions[0,conditionCount) folded left with &&");
  writer.Key("conjunctionAuthority");
  writer.String("VM_THREAD_PATH_CONDITION_RANGE_FOLD_V1");
  writer.Key("authority");
  writer.String("VM_THREAD_PATH_CONDITION_RANGE_V1");
  writer.Key("expressionEncoding");
  writer.String("VM_SESSION_DAG_V1");
  expression_artifact.write_table(writer);
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

std::string ThreadContext::get_auxiliary_path_conditions() {
  using namespace rapidjson;
  RegionFrame *frame = _region_stack.empty() ? NULL : _region_stack.back();
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  VmExpressionArtifactScope expression_artifact;
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("CONCOLIC_AUXILIARY_PATH_CONDITION");
  writer.Key("active");
  writer.Bool(!_aborted);
  writer.Key("aborted");
  writer.Bool(_aborted);
  writer.Key("abortReason");
  writer.String(_abort_reason.c_str());
  writer.Key("pathConditionWatermark");
  writer.Int(_path_condition.size());
  writer.Key("conditionCount");
  writer.Int(frame == NULL
      ? 0 : (int)frame->auxiliary_path_condition_indices.size());
  writer.Key("pathConditionIndices");
  writer.StartArray();
  if (frame != NULL) {
    for (size_t index = 0;
         index < frame->auxiliary_path_condition_indices.size(); ++index) {
      writer.Int(frame->auxiliary_path_condition_indices[index]);
    }
  }
  writer.EndArray();
  writer.Key("conditions");
  int emitted_auxiliary_conditions = 0;
  if (frame == NULL) {
    writer.StartArray();
    writer.EndArray();
  } else {
    emitted_auxiliary_conditions =
        frame->auxiliary_path_condition.serialize(writer);
  }
  // conditionCount above is the length of pathConditionIndices; this is the
  // length of `conditions`.  They are recorded in lockstep by
  // record_path_condition(), and serialize() emits one entry per recorded
  // condition even when it will not expand the expression, so the two agree
  // by construction.  Reporting it makes that an assertion the reader can
  // make rather than an invariant it has to trust -- the byte bound used to
  // break it silently (240 declared, 200 emitted).
  writer.Key("emittedConditionCount");
  writer.Int(emitted_auxiliary_conditions);
  writer.Key("authority");
  writer.String("VM_THREAD_AUXILIARY_PATH_CONDITION_V1");
  writer.Key("expressionEncoding");
  writer.String("VM_SESSION_DAG_V1");
  expression_artifact.write_table(writer);
  writer.EndObject();
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
  _pending_branch_event_id = ++_branch_sequence;
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
    event.context_id = _context_id;
    event.owner_java_thread_id = _owner_java_thread_id;
    event.owner_os_thread_id = _owner_os_thread_id;
    // The current frame owns both this identity and this event.  Popping the
    // frame releases the event after its summary has been serialized.
    event.region_id = frame->region_id;
    event.task_id = frame->task_id;
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

std::string ThreadContext::get_branch_events() const {
  using namespace rapidjson;
  const RegionFrame *frame =
      _region_stack.empty() ? NULL : _region_stack.back();
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("CONCOLIC_THREAD_BRANCH_EVENTS");
  writer.Key("active");
  writer.Bool(!_aborted);
  writer.Key("aborted");
  writer.Bool(_aborted);
  writer.Key("abortReason");
  writer.String(_abort_reason.c_str());
  writer.Key("contextId");
  writer.Int64(_context_id);
  writer.Key("ownerJavaThreadId");
  writer.Int64(_owner_java_thread_id);
  writer.Key("ownerOsThreadId");
  writer.Int64(_owner_os_thread_id);
  writer.Key("regionId");
  writer.String(get_region_id().c_str());
  writer.Key("taskId");
  writer.String(get_task_id().c_str());
  writer.Key("regionDepth");
  writer.Int(region_depth());
  writer.Key("events");
  writer.StartArray();
  const size_t event_count = frame == NULL ? 0 : frame->branch_events.size();
  for (size_t index = 0; index < event_count; ++index) {
    const BranchEvent &event = frame->branch_events[index];
    writer.StartObject();
    writer.Key("eventId");
    writer.Int64(event.event_id);
    writer.Key("contextId");
    writer.Int64(event.context_id);
    writer.Key("ownerJavaThreadId");
    writer.Int64(event.owner_java_thread_id);
    writer.Key("ownerOsThreadId");
    writer.Int64(event.owner_os_thread_id);
    writer.Key("regionId");
    writer.String(event.region_id.c_str());
    writer.Key("taskId");
    writer.String(event.task_id.c_str());
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
  writer.EndObject();
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

void ThreadContext::write_array_element(arrayOop array, int index,
                                        Expression *expression) {
  heap().write_array_element(array, index, expression);
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
                                              Expression *length_exp) {
  return heap().get_or_alloc_sym_array(array, length_exp);
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
//  tty->print_cr(obj->klass()->signature_name());
//  tty->print_cr(obj->klass()->name()->as_C_string());
//  SimpleFieldPrinter field_printer(obj);
//   field_printer.do_recursive();

  FieldSymbolizer field_symbolzier(obj, *this);
  field_symbolzier.do_recursive();
  if (obj != NULL && obj->is_array()) {
    SymArr *array = find_sym_array((arrayOop)obj);
    if (array != NULL) array->mark_semantic_expression();
  } else if (obj != NULL) {
    SymInstance *instance = find_sym_inst(obj);
    if (instance != NULL) instance->mark_semantic_expression();
  }
  // OopTraverser oop_traverser;
  // tty->print_cr(CL_CYAN"================================================================="CNONE);
  // obj->oop_iterate(&oop_traverser);
  // tty->print_cr(CL_CYAN"================================================================="CNONE);
}

void ThreadContext::symbolize_recursive(oop obj, std::string prefix) {
//  tty->print_cr(obj->klass()->signature_name());
//  tty->print_cr(obj->klass()->name()->as_C_string());
//  SimpleFieldPrinter field_printer(obj);
//   field_printer.do_recursive();

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
  // OopTraverser oop_traverser;
  // tty->print_cr(CL_CYAN"================================================================="CNONE);
  // obj->oop_iterate(&oop_traverser);
  // tty->print_cr(CL_CYAN"================================================================="CNONE);
}

void ThreadContext::symbolize_field(Handle handle, std::string field_name,
                                    std::string prefix) {
  FieldSymbolizer field_symbolizer(handle(), *this, prefix, field_name);
  field_symbolizer.do_once();
  SymInstance *owner = find_sym_inst(handle());
  if (owner != NULL) owner->mark_semantic_expression();
}

void ThreadContext::symbolize_exact_field(
    Handle owner, std::string declaring_class, std::string field_name,
    std::string descriptor, std::string prefix) {
  FieldSymbolizer field_symbolizer(
      owner(), *this, prefix, declaring_class, field_name, descriptor);
  field_symbolizer.do_once();
  SymInstance *instance = find_sym_inst(owner());
  if (instance != NULL) instance->mark_semantic_expression();
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

static void print_method_name_and_line(const ZeroFrame *zero_frame, stringStream *ss) {
  interpreterState istate = zero_frame->as_interpreter_frame()->interpreter_state();
  Method *method = istate->method();
  address bcp = istate->bcp();

  method->print_name(ss);
  if (bcp) {
    int bci = method->bci_from(bcp);
    int line = method->line_number_from_bci(bci);
    ss->print(":%d", line);
  }
}

std::string ThreadContext::get_code_pos_for_first(const std::string &str) {
  // Stack-local for the same reason as get_current_code_pos above.
  static const int SIZE = 2048;
  char buf[SIZE];

  stringStream ss(buf, SIZE);

  const char *c_str = str.c_str();
  const ZeroFrame *zero_frame = get_shadow_stack().get_last_frame().get_zero_frame();

  // generate top method name and line string
  while (!zero_frame->is_interpreter_frame()) {
    zero_frame = zero_frame->next();
  }
  print_method_name_and_line(zero_frame, &ss);
  std::string top_name(buf, ss.size());
  tty->print_cr("trying: %s", top_name.c_str());

  // if not containing, use a loop to find it
  if (!strstr(ss.as_string(), c_str)) {
    zero_frame = zero_frame->next();
    while (zero_frame) {
      while (zero_frame && !zero_frame->is_interpreter_frame()) {
        zero_frame = zero_frame->next();
      }
      if (!zero_frame) {
        break;
      }
      ss.reset();
      print_method_name_and_line(zero_frame, &ss);
      // tty->print_cr("trying: %s", ss.as_string());
      if (strstr(ss.as_string(), c_str)) {
        break;
      }
      zero_frame = zero_frame->next();
    }
  }

  return std::string(buf, ss.size());
}

void ThreadContext::print() {
  _path_condition.print();
}

void ThreadContext::print_stack_trace() {
  char buf[O_BUFLEN];
  VMError::print_stack_trace(tty, _thread, buf, sizeof(buf));
//  this->get_shadow_stack().print();
}

void ThreadContext::memory_leak_check() {
  tty->print_cr("Session holds %lu expressions...",
                (unsigned long) GlobalSymbolicSession::expression_count());
}

PathCondition &ThreadContext::get_path_condition() {
  return _path_condition;
}

void ThreadContext::set_pc_enabled(bool pathConditionEnabled) {
  if (!_aborted) {
    _path_condition_enabled = pathConditionEnabled;
  }
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
