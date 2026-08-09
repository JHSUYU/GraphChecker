#ifdef ENABLE_CONCOLIC

#include "concolic/threadContext.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/fieldTraverser.hpp"
#include "concolic/jdbc/reference/symbolicResultSet.hpp"
#include "concolic/jdbc/reference/symbolicStatement.hpp"
#include "concolic/reference/symbolicObject.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/reference/symbolicBigDecimal.hpp"
#include "concolic/reference/symbolicTimestamp.hpp"
#include "concolic/reference/symbolicDate.hpp"
#include "concolic/jdbc/reference/symbolicHibernateKey.hpp"
#include "utilities/vmError.hpp"
#include "utilities/exceptions.hpp"
#include "concolic/reference/symbolicNDFunc.hpp"
#include "classfile/javaClasses.hpp"
#include "runtime/osThread.hpp"
#include "runtime/safepoint.hpp"
#include "runtime/vm_operations.hpp"
#include "runtime/vmThread.hpp"

// An object closure to reset symbolic ids
class RestoreSymbolicClosure : public ObjectClosure {
public:
  void do_object(oop o) {
    if (o != NULL) {
      o->set_sym_rid(NULL_SYM_RID);
    }
  }
};

// Clearing the oop header extension requires a stable heap.  MiniDFSCluster
// keeps many mutator threads alive while a captured region finishes, so a raw
// safe_object_iterate from that Java thread can race allocation or GC.  Run
// the cleanup as a blocking VM operation instead.
class VM_RestoreConcolicSymbolicIds : public VM_Operation {
public:
  virtual VMOp_Type type() const { return VMOp_Dummy; }

  virtual void doit() {
    assert(SafepointSynchronize::is_at_safepoint(),
           "concolic oop cleanup requires a safepoint");
    RestoreSymbolicClosure closure;
    CollectedHeap* heap = Universe::heap();
    heap->ensure_parsability(false);
    heap->safe_object_iterate(&closure);
  }
};

ThreadContext::ThreadContext(JavaThread *jt, jlong context_id)
    : _thread(jt), _s_stack(jt), _sym_rid_counter(), _sym_tmp_id_counter(),
      _path_condition_enabled(true), _path_condition_pause_depth(0),
      _aborted(false),
      _context_id(context_id),
      _owner_java_thread_id(jt == NULL || jt->threadObj() == NULL
          ? 0 : java_lang_Thread::thread_id(jt->threadObj())),
      _owner_os_thread_id(jt == NULL || jt->osthread() == NULL
          ? 0 : (jlong) jt->osthread()->thread_id()),
      _branch_sequence(0), _pending_branch_active(false),
      _pending_branch_event_id(0), _pending_branch_owner_frame(NULL),
      _pending_branch_occurrence(0) {
  init_sym_rid_counter();
  init_sym_tmp_id_counter();

  Expression::init_gc_helper();
  SymbolExpression::init_single_instances();
}

void ThreadContext::abort_symbolic_execution(const char *reason) {
  if (_aborted) {
    return;
  }
  _aborted = true;
  _abort_reason = reason == NULL ? "UNSPECIFIED" : reason;
  _path_condition_enabled = false;
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
  if (_aborted || !_path_condition_enabled
      || _path_condition_pause_depth > 0) {
    // A marker identifies one concrete branch execution, not the next branch
    // after recording happens to resume.
    cancel_pending_branch();
    return;
  }

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
    BranchEvent event;
    event.event_id = _pending_branch_event_id;
    event.context_id = _context_id;
    event.owner_java_thread_id = _owner_java_thread_id;
    event.owner_os_thread_id = _owner_os_thread_id;
    event.region_id = _region_id;
    event.task_id = _task_id;
    event.site_id = _pending_branch_site_id;
    event.occurrence = _pending_branch_occurrence;
    event.outcome = outcome;
    event.opcode = opcode;
    event.code_position = get_current_code_pos();
    event.condition_indices = direct_indices;
    _branch_events.push_back(event);
    cancel_pending_branch();
  }

}

std::string ThreadContext::get_branch_events() const {
  using namespace rapidjson;
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
  writer.String(_region_id.c_str());
  writer.Key("taskId");
  writer.String(_task_id.c_str());
  writer.Key("events");
  writer.StartArray();
  for (size_t index = 0; index < _branch_events.size(); ++index) {
    const BranchEvent &event = _branch_events[index];
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
  for (ContainerStateStore::iterator state = _container_states.begin();
       state != _container_states.end(); ++state) {
    Expression::gc(state->second);
  }
  _container_states.clear();

  // DetachedObjectStore does not own its SymInstance values.  Release its GC
  // roots before deleting the instances from SymStore so no stale oop can be
  // resolved during the remaining teardown.
  DetachedObjectStore::iterator detached_it;
  for (detached_it = _detached_object_store.begin();
       detached_it != _detached_object_store.end(); ++detached_it) {
    guarantee(detached_it->second != NULL,
              "Detached symbolic object should not be null");
    JNIHandles::destroy_global(detached_it->first);
  }
  _detached_object_store.clear();

  for (SymStore::iterator iter = _sym_refs.begin(); iter != _sym_refs.end();
       ++iter) {
    guarantee(iter->second != NULL, "Sym instance should not be null");
    delete iter->second;
  }
  _sym_refs.clear();

  int size = _sym_tmp_exps.size();
  for (int i = 1; i != size; ++i) {
    Expression::gc(_sym_tmp_exps[i]);
  }
  _sym_tmp_exps.clear();
  _path_condition.gc();
  SymbolicNDFunc::gc();

  VM_RestoreConcolicSymbolicIds restore;
  VMThread::execute(&restore);

  Expression::finalize_dangling_objects();
  SymStmt::resetGlobalCounter();
}

Expression *ThreadContext::track_container(
    oop container, const char *shape, const std::string &prefix) {
  if (container == NULL || shape == NULL || prefix.empty()) return NULL;
  Expression *existing = find_container_state(container);
  if (existing != NULL) return existing;

  if (container->is_array()) {
    SymArr *array = get_or_alloc_sym_array((arrayOop)container);
    if (array == NULL) return NULL;
    array->set_ref_exp(new FieldSymbolExp(
        array->get_sym_rid(), prefix, T_ARRAY));
  } else {
    SymInstance *instance = get_or_alloc_sym_inst(container);
    if (instance == NULL) return NULL;
    instance->set_ref_exp(new FieldSymbolExp(
        instance->get_sym_rid(), prefix, T_OBJECT));
  }
  return container_state(container, shape);
}

Expression *ThreadContext::container_state(oop container,
                                           const char *shape) {
  if (container == NULL) return NULL;
  sym_rid_t id;
  Expression *identity;
  SymArr *array = NULL;
  if (container->is_array()) {
    array = get_or_alloc_sym_array((arrayOop)container);
    if (array == NULL) return NULL;
    id = array->get_sym_rid();
    identity = array->get_ref_exp();
    if (identity == NULL) {
      identity = new ArraySymbolExp(id, array->get_version(), T_OBJECT);
    }
  } else {
    SymInstance *instance = get_or_alloc_sym_inst(container);
    if (instance == NULL) return NULL;
    id = instance->get_sym_rid();
    identity = instance->get_or_create_ref_exp(container);
  }
  ContainerOwnerStore::const_iterator owner = _container_owners.find(id);
  if (owner != _container_owners.end()) id = owner->second;
  ContainerStateStore::iterator existing = _container_states.find(id);
  if (existing != _container_states.end()) return existing->second;
  if (owner != _container_owners.end()) return NULL;

  exp_list_t state_arguments;
  if (container->is_array()) {
    Expression *declared_length = array->get_length_exp();
    state_arguments.push_back(declared_length == NULL
        ? (Expression *)new ConExpression(
            (jint)((arrayOop)container)->length())
        : declared_length);
  }
  Expression *state = new ContainerExpression(shape, "STATE",
      identity, state_arguments);
  state->inc_ref();
  _container_states[id] = state;
  return state;
}

Expression *ThreadContext::find_container_state(oop container) const {
  if (container == NULL) return NULL;
  sym_rid_t id = NULL_SYM_RID;
  if (container->is_array()) {
    if (!container->is_symbolic()) return NULL;
    id = container->get_sym_rid();
  } else {
    SymInstance *instance = find_sym_inst(container);
    if (instance == NULL) return NULL;
    id = instance->get_sym_rid();
  }
  ContainerOwnerStore::const_iterator owner = _container_owners.find(id);
  if (owner != _container_owners.end()) id = owner->second;
  ContainerStateStore::const_iterator state = _container_states.find(id);
  return state == _container_states.end() ? NULL : state->second;
}

void ThreadContext::set_container_state(oop container, Expression *state) {
  if (container == NULL || state == NULL) return;
  sym_rid_t id;
  if (container->is_array()) {
    SymArr *array = get_or_alloc_sym_array((arrayOop)container);
    if (array == NULL) return;
    id = array->get_sym_rid();
  } else {
    SymInstance *instance = get_or_alloc_sym_inst(container);
    if (instance == NULL) return;
    id = instance->get_sym_rid();
  }
  ContainerOwnerStore::const_iterator owner = _container_owners.find(id);
  if (owner != _container_owners.end()) id = owner->second;
  ContainerStateStore::iterator existing = _container_states.find(id);
  if (existing != _container_states.end()) {
    Expression::gc(existing->second);
    existing->second = state;
  } else {
    _container_states[id] = state;
  }
  state->inc_ref();
}

void ThreadContext::write_array_element(arrayOop array, int index,
                                        Expression *expression) {
  if (array == NULL || expression == NULL || index < 0
      || index >= array->length()) return;
  SymArr *symbolic = get_or_alloc_sym_array(array);
  if (symbolic == NULL) return;
  exp_list_t arguments;
  arguments.push_back(new ConExpression((jint)index));
  arguments.push_back(expression);
  Expression *next = new ContainerExpression(
      "INDEXED", "WRITE", container_state(array, "INDEXED"), arguments);
  set_container_state(array, next);
  symbolic->store();
}

void ThreadContext::alias_container(oop derived, oop owner) {
  if (derived == NULL || owner == NULL || derived->is_array()
      || owner->is_array()) return;
  SymInstance *derived_instance = get_or_alloc_sym_inst(derived);
  SymInstance *owner_instance = get_or_alloc_sym_inst(owner);
  if (derived_instance == NULL || owner_instance == NULL) return;
  sym_rid_t owner_id = owner_instance->get_sym_rid();
  ContainerOwnerStore::const_iterator canonical =
      _container_owners.find(owner_id);
  if (canonical != _container_owners.end()) owner_id = canonical->second;
  _container_owners[derived_instance->get_sym_rid()] = owner_id;
}

int ThreadContext::next_container_position(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return -1;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return -1;
  sym_rid_t id = instance->get_sym_rid();
  int position = _container_positions[id];
  _container_positions[id] = position + 1;
  return position;
}

int ThreadContext::current_container_position(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return 0;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return 0;
  return _container_positions[instance->get_sym_rid()];
}

int ThreadContext::next_container_removal_position(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return -1;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return -1;
  sym_rid_t id = instance->get_sym_rid();
  int traversal_position = _container_positions[id];
  int removed = _container_removals[id];
  if (traversal_position <= 0) return -1;
  _container_removals[id] = removed + 1;
  return traversal_position - 1 - removed;
}

SymInstance *ThreadContext::get_or_alloc_sym_inst(oop obj) {
  if (obj == NULL) return NULL;
  SymInstance *existing = find_sym_inst(obj);
  return existing == NULL ? this->alloc_sym_inst(obj) : existing;
}

SymInstance *ThreadContext::alloc_sym_inst(oop obj) {
  if (obj == NULL || obj->is_array()) return NULL;
  SymInstance *existing = find_sym_inst(obj);
  if (existing != NULL) return existing;

  sym_rid_t sym_rid = get_next_sym_rid();
  SymInstance *sym_inst = NULL;
  ResourceMark rm;

  Symbol *klass_symbol = obj->klass()->name();
  if (klass_symbol == NULL) {
    guarantee(false, "unexpected null class");
    sym_inst = new SymResSet(sym_rid);
    obj->set_sym_rid(sym_rid);
    this->set_sym_ref(sym_rid, sym_inst);
//  _allocated_objs.insert(obj);
    return sym_inst;
  }
  std::string class_name(klass_symbol->as_C_string());
//  tty->print_cr("alloc_sym_inst for %s", klass_symbol->as_C_string());

  bool detached_from_oop_header = requires_detached_object_shadow(obj);
  if (klass_symbol->equals(SymString::TYPE_NAME)) {
    if (detached_from_oop_header) {
      // Intern-table entries are VM-global and may be concurrently shared by
      // unrelated Java code.  Never write this context's sym_rid into that
      // shared oop.  A ThreadContext-local, GC-stable shadow gives the value a
      // symbolic identity without changing Java reference/content semantics.
    }
    sym_inst = new SymString(sym_rid);
  } else if (klass_symbol->equals(SymStrBuilder::TYPE_NAME)) {
    sym_inst = new SymStrBuilder(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jchar>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jchar>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jboolean>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jboolean>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jbyte>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jbyte>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jint>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jint>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jshort>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jshort>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jlong>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jlong>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jfloat>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jfloat>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<double>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jdouble>(sym_rid);
  } else if (klass_symbol->equals(SymBigDecimal::TYPE_NAME)) {
    sym_inst = new SymBigDecimal(sym_rid, obj);
  } else if (klass_symbol->equals(SymTimestamp::TYPE_NAME)) {
    sym_inst = new SymTimestamp(sym_rid, obj);
  } else if (klass_symbol->equals(SymbolicDate::TYPE_NAME)) {
    sym_inst = new SymbolicDate(sym_rid, obj);
  } else if (SymStmt::target(class_name)) {
    sym_inst = new SymStmt(sym_rid);
  } else if (SymResSet::target(class_name)) {
    sym_inst = new SymResSet(sym_rid);
  }
//  else if (SymHibernateKey::target(class_name)) {
//    sym_inst = new SymHibernateKey(sym_rid);
//  }
  else {
    sym_inst = new SymObj(sym_rid);
  }

  if (sym_inst == NULL) {
    tty->print_cr("Warning: failed to allocate symbolic object shadow");
    return NULL;
  }

  if (detached_from_oop_header) {
    Handle stable_oop(_thread, obj);
    jobject stable_handle = JNIHandles::make_global(stable_oop);
    if (stable_handle == NULL) {
      // Do not publish a partial shadow.  Callers treat NULL as an
      // unsupported symbolic value and continue with concrete semantics.
      delete sym_inst;
      tty->print_cr("Warning: failed to retain interned String shadow");
      return NULL;
    }
    this->set_sym_ref(sym_rid, sym_inst);
    _detached_object_store.insert(
        std::make_pair(stable_handle, sym_inst));
    return sym_inst;
  }

  obj->set_sym_rid(sym_rid);
  this->set_sym_ref(sym_rid, sym_inst);
//  _allocated_objs.insert(obj);
  return sym_inst;
}

SymInstance *ThreadContext::get_sym_inst(sym_rid_t sym_rid) {
  SymInstance *ret = (SymInstance *) _sym_refs[sym_rid];
  /**
   * When this assertion is broken,
   * it means that the target object is not initialized with NULL_SYM_RID
   */
  guarantee(ret != NULL, "Unexpected null symbolic object. The object might not properly symbolized.");
  return ret;
}

SymInstance *ThreadContext::find_sym_inst(oop obj) const {
  if (obj == NULL || obj->is_array()) return NULL;
  if (obj->is_symbolic()) {
    SymStore::const_iterator found = _sym_refs.find(obj->get_sym_rid());
    if (found != _sym_refs.end()) {
      return static_cast<SymInstance *>(found->second);
    }
  }
  for (DetachedObjectStore::const_iterator found =
           _detached_object_store.begin();
       found != _detached_object_store.end(); ++found) {
    if (JNIHandles::resolve(found->first) == obj) return found->second;
  }
  return NULL;
}

bool ThreadContext::requires_detached_object_shadow(oop obj) const {
  if (obj == NULL || obj->is_array() || obj->klass() == NULL
      || obj->klass()->name() == NULL) {
    return false;
  }
  // Keep this policy in ThreadContext so bytecode producers do not need to
  // know which VM-managed objects are unsafe to annotate in their oop header.
  return obj->klass()->name()->equals(SymString::TYPE_NAME)
      && OopUtils::is_java_string_interned(obj);
}

SymArr *ThreadContext::get_or_alloc_sym_array(arrayOop array,
                                              Expression *length_exp) {
  if (array->is_symbolic()) {
    return this->get_sym_array(array->get_sym_rid());
  } else {
    return this->alloc_sym_array(array, length_exp);
  }
}

SymArr *ThreadContext::alloc_sym_array(arrayOop array, Expression *length_exp) {
  sym_rid_t sym_rid = get_next_sym_rid();
  array->set_sym_rid(sym_rid);

  // if (length_exp == NULL) {
  //   length_exp = new ConExpression(array->length());
  // }

  SymArr *sym_arr = new SymArr(sym_rid, length_exp);
  this->set_sym_ref(sym_rid, sym_arr);

//  _allocated_objs.insert(array);
  return sym_arr;
}

SymArr *ThreadContext::get_sym_array(sym_rid_t sym_rid) {
  SymArr *ret = (SymArr *) _sym_refs[sym_rid];
  /**
   * When this assertion is broken,
   * it means that the target object is not initialized with NULL_SYM_RID
   */
  assert(ret != NULL, "null sym obj?");
  return ret;
}

SymArr *ThreadContext::find_sym_array(arrayOop array_obj) const {
  if (array_obj == NULL || !array_obj->is_symbolic()) return NULL;
  SymStore::const_iterator found = _sym_refs.find(array_obj->get_sym_rid());
  if (found == _sym_refs.end()) return NULL;
  return static_cast<SymArr *>(found->second);
}

void ThreadContext::symbolize_recursive(oop obj) {
//  tty->print_cr(obj->klass()->signature_name());
//  tty->print_cr(obj->klass()->name()->as_C_string());
//  SimpleFieldPrinter field_printer(obj);
//   field_printer.do_recursive();

  FieldSymbolizer field_symbolzier(obj, *this);
  field_symbolzier.do_recursive();
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
    }
  } else if (obj != NULL) {
    SymInstance *instance = find_sym_inst(obj);
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
}

void ThreadContext::symbolize_exact_field(
    Handle owner, std::string declaring_class, std::string field_name,
    std::string descriptor, std::string prefix) {
  FieldSymbolizer field_symbolizer(
      owner(), *this, prefix, declaring_class, field_name, descriptor);
  field_symbolizer.do_once();
}

sym_tmp_id_t ThreadContext::get_next_sym_tmp_id(Expression *sym_exp) {
  sym_rid_t sym_tmp_id = _sym_tmp_id_counter++;
  sym_exp->inc_ref();
  _sym_tmp_exps.push_back(sym_exp);
  assert(_sym_tmp_exps.size() == sym_tmp_id + 1, "sanity check");
  assert(sym_tmp_id < MAX_SYM_RID, "sym_tmp_id limitted");
  return sym_tmp_id;
}

void ThreadContext::detach_tmp_exp(sym_tmp_id_t sym_tmp_id) {
  Expression *exp = _sym_tmp_exps[sym_tmp_id];
  if (exp) {
    exp->dec_ref();
  }
  _sym_tmp_exps[sym_tmp_id] = NULL;
}

std::string ThreadContext::get_current_code_pos() {
  static const int SIZE = 1024;
  static char buf[SIZE];

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
  static const int SIZE = 2048;
  static char buf[SIZE];

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
//  for (SymStore::iterator sym_iter = _sym_refs.begin();
//       sym_iter != _sym_refs.end(); ++sym_iter) {
//    tty->print_cr("- sym_inst[%lu]:", sym_iter->first);
//    sym_iter->second->print();
//  }

//  int size = _sym_tmp_exps.size();
//  for (int i = 1; i < size; ++i) {
//    Expression *sym_exp = _sym_tmp_exps[i];
//    if (sym_exp) {
//      tty->print_cr("<< sym_tmp_exp[%d]:", i);
//      sym_exp->print_cr();
//    }
//  }
  _jdbc_mngr.print();

  _path_condition.print();
}

void ThreadContext::print_stack_trace() {
  static char buf[O_BUFLEN];
  VMError::print_stack_trace(tty, _thread, buf, sizeof(buf));
//  this->get_shadow_stack().print();
}

void ThreadContext::memory_leak_check() {
  tty->print_cr("Checking memory leaks for Expression, %lu remains...",
                Expression::total_count);
}

PathCondition &ThreadContext::get_path_condition() {
  return _path_condition;
}

void ThreadContext::set_pc_enabled(bool pathConditionEnabled) {
  if (!_aborted) {
    _path_condition_enabled = pathConditionEnabled;
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
