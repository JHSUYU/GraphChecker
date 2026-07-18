#ifdef ENABLE_CONCOLIC

#include "concolic/threadContext.hpp"
#include "concolic/exp/arrayInitExpression.hpp"
#include "concolic/exp/expression.hpp"
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
      _context_id(context_id),
      _owner_java_thread_id(jt == NULL || jt->threadObj() == NULL
          ? 0 : java_lang_Thread::thread_id(jt->threadObj())),
      _owner_os_thread_id(jt == NULL || jt->osthread() == NULL
          ? 0 : (jlong) jt->osthread()->thread_id()),
      _branch_sequence(0), _pending_branch_active(false),
      _pending_branch_event_id(0), _pending_branch_occurrence(0),
      _pending_compare_condition_index(-1) {
  init_sym_rid_counter();
  init_sym_tmp_id_counter();

  Expression::init_gc_helper();
  SymbolExpression::init_single_instances();
}

jlong ThreadContext::mark_branch(const char *site_id, int occurrence) {
  // A malformed/missed after-hook must not let an old marker authorize a
  // later branch.  Replacing the single pending slot is deterministic and
  // fail-closed: only the newly returned id can be claimed by Java.
  _pending_branch_event_id = ++_branch_sequence;
  _pending_branch_site_id = site_id == NULL ? "" : site_id;
  _pending_branch_occurrence = occurrence;
  _pending_branch_active = true;
  return _pending_branch_event_id;
}

void ThreadContext::record_compare_witness(Expression *expression) {
  if (!_path_condition_enabled || _path_condition_pause_depth > 0
      || expression == NULL) {
    return;
  }
  // lcmp/fcmp/dcmp materialize their symbolic trichotomy before the following
  // if bytecode.  Retain the exact index until that conditional executes.
  _pending_compare_condition_index = _path_condition.add(expression);
}

void ThreadContext::record_branch_condition(Expression *expression,
                                             bool outcome, int opcode) {
  if (!_path_condition_enabled || _path_condition_pause_depth > 0) {
    return;
  }

  int direct_index = -1;
  if (expression != NULL) {
    direct_index = _path_condition.add(expression);
  }

  if (_pending_branch_active) {
    BranchEvent event;
    event.event_id = _pending_branch_event_id;
    event.context_id = _context_id;
    event.owner_java_thread_id = _owner_java_thread_id;
    event.owner_os_thread_id = _owner_os_thread_id;
    event.region_id = _region_id;
    event.activation_id = _activation_id;
    event.site_id = _pending_branch_site_id;
    event.occurrence = _pending_branch_occurrence;
    event.outcome = outcome;
    event.opcode = opcode;
    event.code_position = get_current_code_pos();
    if (direct_index >= 0) {
      event.condition_indices.push_back(direct_index);
    } else if (_pending_compare_condition_index >= 0) {
      event.condition_indices.push_back(_pending_compare_condition_index);
    }
    _branch_events.push_back(event);
    _pending_branch_active = false;
    _pending_branch_event_id = 0;
    _pending_branch_site_id.clear();
    _pending_branch_occurrence = 0;
  }

  // A compare witness belongs only to the immediately following conditional,
  // whether or not that branch had a Soot marker.
  _pending_compare_condition_index = -1;
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
  writer.Key("contextId");
  writer.Int64(_context_id);
  writer.Key("ownerJavaThreadId");
  writer.Int64(_owner_java_thread_id);
  writer.Key("ownerOsThreadId");
  writer.Int64(_owner_os_thread_id);
  writer.Key("regionId");
  writer.String(_region_id.c_str());
  writer.Key("activationId");
  writer.String(_activation_id.c_str());
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
    writer.Key("activationId");
    writer.String(event.activation_id.c_str());
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
  // ArrayInternal entries may share expressions owned by SymRef, temporary,
  // or path-condition stores.  Drop the array store's references first, then
  // tear down the other owners.  This keeps the ownership direction explicit
  // and also releases all GC-tracked global handles before heap-id cleanup.
  ArrayStore::iterator arr_it;
  for (arr_it = _array_store.begin(); arr_it != _array_store.end(); arr_it++) {
    guarantee(arr_it->second != NULL, "Array store should not be null");
    delete arr_it->second;
    JNIHandles::destroy_global(arr_it->first);
  }
  _array_store.clear();

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
  SymString::INTERN_MAP.clear();
  SymStmt::resetGlobalCounter();
}

SymInstance *ThreadContext::get_or_alloc_sym_inst(oop obj) {
  if (obj == NULL) return NULL;
  if (obj->is_symbolic()) {
    return this->get_sym_inst(obj->get_sym_rid());
  } else {
    return this->alloc_sym_inst(obj);
  }
}

SymInstance *ThreadContext::alloc_sym_inst(oop obj) {
  sym_rid_t sym_rid = get_next_sym_rid();
  SymInstance *sym_inst;
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

  if (klass_symbol->equals(SymString::TYPE_NAME)) {
    if (OopUtils::is_java_string_interned(obj)) {
      ResourceMark rm;
      const char *str = OopUtils::java_string_to_c(obj);
      tty->print_cr("Unsupported symbolizing behavior of interned String!: [%s]", str);
      /**
       * we do not support symbolize interned Java string
       */
      return NULL;
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
  if (obj == NULL || obj->is_array() || !obj->is_symbolic()) return NULL;
  SymStore::const_iterator found = _sym_refs.find(obj->get_sym_rid());
  if (found == _sym_refs.end()) return NULL;
  return static_cast<SymInstance *>(found->second);
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

  ArrayInitExpression *array_init =
      new ArrayInitExpression(sym_arr->get_sym_rid(), array);
  this->record_path_condition(array_init);
  ArrayInternal *internal = get_or_create_array_internal(array);
  for (int index = 0; index < array_init->element_count(); ++index) {
    internal->store(index, array_init->element_expression_at(index),
                    "SYMBOLIC_ARRAY_INIT");
  }
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
  int line = -1;
  if (bcp != NULL) {
    int bci = method->bci_from(bcp);
    line = method->line_number_from_bci(bci);
  }

  method->print_name(&ss);
  ss.print(":%d", line);

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
  _path_condition_enabled = pathConditionEnabled;
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
