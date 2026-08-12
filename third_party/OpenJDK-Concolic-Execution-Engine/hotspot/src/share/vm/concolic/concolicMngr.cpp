#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "oops/arrayKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "runtime/fieldDescriptor.hpp"
#include "runtime/thread.hpp"
#include "webridge/webridgeMngr.hpp"
#include "utilities/ostream.hpp"
#include "utilities/vmError.hpp"

#include <string.h>

#ifdef ENABLE_CONCOLIC

volatile int ConcolicMngr::_num_threads_in_concolic = 0;
jlong ConcolicMngr::_next_context_id = 0;
pthread_mutex_t ConcolicMngr::mutex = PTHREAD_MUTEX_INITIALIZER;
__thread ThreadContext *ConcolicMngr::ctx = NULL;

namespace {

typedef rapidjson::Writer<rapidjson::StringBuffer> ExpressionWriter;

Expression *attached_reference_expression(oop value) {
  if (value == NULL) return NULL;
  if (value->is_array()) {
    SymArr *array = ConcolicMngr::ctx->find_sym_array((arrayOop)value);
    return array == NULL ? NULL : array->get_ref_exp();
  }
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(value);
  return instance == NULL ? NULL : instance->get_ref_exp();
}

void serialize_temporary_expression(ExpressionWriter &writer,
                                    Expression *expression) {
  guarantee(expression != NULL, "temporary expression required");
  expression->inc_ref();
  expression->serialize(writer);
  Expression::gc(expression);
}

std::string serialize_field_expression(const char *kind, bool symbolic,
                                       const char *authority,
                                       Expression *expression,
                                       bool temporary_expression) {
  using namespace rapidjson;
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("active");
  writer.Bool(ConcolicMngr::has_active_context());
  writer.Key("aborted");
  writer.Bool(ConcolicMngr::ctx != NULL
      && ConcolicMngr::ctx->is_aborted());
  writer.Key("abortReason");
  writer.String(ConcolicMngr::ctx == NULL ? ""
      : ConcolicMngr::ctx->get_abort_reason().c_str());
  writer.Key("kind");
  writer.String(kind == NULL ? "" : kind);
  writer.Key("symbolic");
  writer.Bool(symbolic);
  writer.Key("expressionAuthority");
  writer.String(authority == NULL ? "" : authority);
  writer.Key("expression");
  if (expression == NULL) {
    writer.Null();
  } else if (temporary_expression) {
    serialize_temporary_expression(writer, expression);
  } else {
    expression->serialize(writer);
  }
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

Expression *concrete_boxed_primitive_expression(oop value) {
  if (value == NULL || value->klass() == NULL
      || value->klass()->name() == NULL) {
    return NULL;
  }
  ResourceMark rm;
  BasicType type = primitive_target(
      std::string(value->klass()->name()->as_C_string()));
  switch (type) {
    case T_BOOLEAN:
      return SymPrimitive<jboolean>::get_exp_of_helper(value);
    case T_BYTE:
      return SymPrimitive<jbyte>::get_exp_of_helper(value);
    case T_CHAR:
      return SymPrimitive<jchar>::get_exp_of_helper(value);
    case T_SHORT:
      return SymPrimitive<jshort>::get_exp_of_helper(value);
    case T_INT:
      return SymPrimitive<jint>::get_exp_of_helper(value);
    case T_LONG:
      return SymPrimitive<jlong>::get_exp_of_helper(value);
    case T_FLOAT:
      return SymPrimitive<jfloat>::get_exp_of_helper(value);
    case T_DOUBLE:
      return SymPrimitive<jdouble>::get_exp_of_helper(value);
    default:
      return NULL;
  }
}

BasicType boxed_primitive_type(oop value) {
  if (value == NULL || value->klass() == NULL
      || value->klass()->name() == NULL) {
    return T_ILLEGAL;
  }
  ResourceMark rm;
  return primitive_target(
      std::string(value->klass()->name()->as_C_string()));
}

bool object_array_contains_symbolic_reference(arrayOop array,
                                              BasicType component_type) {
  if (component_type != T_OBJECT && component_type != T_ARRAY) return false;
  for (int index = 0; index < array->length(); ++index) {
    oop element = objArrayOop(array)->obj_at(index);
    if (attached_reference_expression(element) != NULL) {
      return true;
    }
  }
  return false;
}

} // anonymous namespace

jlong ConcolicMngr::startConcolic(JavaThread *thread) {
  // Ownership of this mutex spans the entire region.  A contender must never
  // block while the owner is asking the VM thread for a cleanup safepoint;
  // trylock makes overlap an immediate, fail-closed rejection instead.
  int lock_status = pthread_mutex_trylock(&mutex);
  if (lock_status != 0) {
    tty->print_cr("Concolic start rejected: region mutex busy (%d)",
                  lock_status);
    return 1;
  }
  /**
   * Although ThreadContext is thread-local, there are some static fields of
   * other classes, which are still global.
   *
   * Therefore, we still assume that only one thread can execute in concolic
   * model
   */
  // Product builds compile HotSpot assertions out.  The engine contains
  // process-global expression/symbolizer state, so an assertion alone does
  // not enforce its single-active-context contract.  Reject overlap before
  // allocating a TLS context; callers can then record a deterministic skip
  // instead of racing global symbolic state.
  if (_num_threads_in_concolic != 0 || ctx != NULL || thread == NULL) {
    int active = _num_threads_in_concolic;
    pthread_mutex_unlock(&mutex);
    tty->print_cr("Concolic start rejected: active contexts=%d, local context=%s",
                  active, ctx == NULL ? "false" : "true");
    return 1;
  }

  ++_num_threads_in_concolic;

  ctx = new ThreadContext(thread, ++_next_context_id);
  tty->print_cr("Starting concolic execution");
  return 0;
}

jlong ConcolicMngr::startConcolicRegion(JavaThread *thread,
                                        const char *region_id,
                                        const char *task_id) {
  jlong result = startConcolic(thread);
  if (result == 0 && ctx != NULL) {
    ctx->set_region_metadata(region_id, task_id);
    // A selected region can begin long before its first materialized input.
    // Keep shadow frames tracking across that concrete prefix, but do not
    // admit ambient library predicates into the path condition.  The first
    // explicit symbolize/track/observe operation below opens this gate before
    // installing its input expression.  Legacy startConcolic() retains its
    // eager recording behavior.
    ctx->set_pc_admitted(false);
  }
  return result;
}

void ConcolicMngr::abandonPendingBranchForException(Thread *thread) {
  if (ctx == NULL || ctx->is_aborted() || thread == NULL
      || !thread->is_Java_thread()
      || ctx->get_thread() != (JavaThread *) thread) {
    return;
  }
  // The marker belongs to one concrete conditional execution.  Exception
  // construction may call Java (notably Throwable.fillInStackTrace), so it
  // must be invalidated before any such call can consume the marker.
  ctx->cancel_pending_branch();
}

void ConcolicMngr::abortCurrentContext(const char *reason) {
  if (ctx != NULL) {
    ctx->abort_symbolic_execution(reason);
  }
}

void ConcolicMngr::cleanupAbandonedContext(JavaThread *thread) {
  if (ctx == NULL || thread == NULL || ctx->get_thread() != thread) {
    return;
  }
  ctx->abort_symbolic_execution("OWNER_JAVA_THREAD_EXIT");
  // This is a safe owner-thread boundary: no concolic Java frame remains and
  // uncaught-exception callbacks have already completed.  Release the
  // process-global single-context lock before the JavaThread is destroyed.
  endConcolic();
}

std::string ConcolicMngr::getSymbolicExpression(Handle handle) {
  using namespace rapidjson;
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("active");
  writer.Bool(has_active_context());
  writer.Key("aborted");
  writer.Bool(ctx != NULL && ctx->is_aborted());
  writer.Key("abortReason");
  writer.String(ctx == NULL ? "" : ctx->get_abort_reason().c_str());

  if (!has_active_context() || handle.is_null()) {
    writer.Key("kind");
    writer.String(handle.is_null() ? "NULL"
        : (ctx != NULL && ctx->is_aborted()
            ? "CONCOLIC_ABORTED" : "CONCOLIC_DISABLED"));
    writer.Key("symbolic");
    writer.Bool(false);
    writer.EndObject();
    return std::string(buffer.GetString(), buffer.GetLength());
  }

  oop obj = handle();
  BasicType primitive_type = boxed_primitive_type(obj);
  SymInstance *object_instance = obj->is_array()
      ? NULL : ctx->find_sym_inst(obj);
  Expression *container_state = obj->is_array()
      ? NULL : ctx->find_container_state(obj);
  bool symbolic = object_instance != NULL;
  if (obj->is_array()) {
    arrayOop array = arrayOop(obj);
    BasicType component_type =
        ArrayKlass::cast(array->klass())->element_type();
    symbolic = array->is_symbolic()
        || object_array_contains_symbolic_reference(array, component_type);
    if (symbolic && !array->is_symbolic()) {
      for (int index = 0; index < array->length(); ++index) {
        ctx->write_array_element(array, index,
            ContainerSupport::concrete_value(
                objArrayOop(array)->obj_at(index)));
      }
    }
    if (symbolic) {
      container_state = ctx->container_state(obj, "INDEXED");
    }
  } else if (symbolic && container_state == NULL) {
    const char *shape = ContainerSupport::shape(obj);
    if (shape != NULL) {
      container_state = ctx->container_state(obj, shape);
    }
  }
  if (container_state != NULL) symbolic = true;
  writer.Key("symbolic");
  writer.Bool(symbolic);
  Expression *expression = NULL;
  bool temporary_expression = false;
  if (container_state != NULL) {
    writer.Key("kind");
    writer.String("CONTAINER_RELATION");
    expression = container_state;
  } else if (symbolic) {
    writer.Key("kind");
    writer.String("SYMBOLIC_OBJECT");
    if (object_instance != NULL) {
      expression = object_instance->get_ref_exp();
    }
  } else {
    expression = concrete_boxed_primitive_expression(obj);
    temporary_expression = expression != NULL;
    writer.Key("kind");
    writer.String(temporary_expression
        ? "CONCRETE_PRIMITIVE" : "CONCRETE_OBJECT");
  }

  if (primitive_type != T_ILLEGAL) {
    char descriptor[2] = { type2char(primitive_type), '\0' };
    writer.Key("javaTypeDescriptor");
    writer.String(descriptor);
  }
  writer.Key("expressionAuthority");
  if (temporary_expression) {
    writer.String("VM_EXACT_CONCRETE_BOXED_PRIMITIVE_V1");
  } else if (primitive_type != T_ILLEGAL && expression != NULL) {
    writer.String("VM_EXACT_BOXED_PRIMITIVE_SHADOW_V1");
  } else {
    writer.String("VM_OBJECT_EXPRESSION_OBSERVATION_V1");
  }

  writer.Key("expression");
  if (expression == NULL) {
    writer.Null();
  } else if (temporary_expression) {
    serialize_temporary_expression(writer, expression);
  } else {
    expression->serialize(writer);
  }
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

std::string ConcolicMngr::getSymbolicFieldExpression(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor, Handle concrete_value) {
  if (!has_active_context()) {
    return serialize_field_expression("CONCOLIC_DISABLED", false,
        "", NULL, false);
  }
  if (owner.is_null()
      || declaring_class == NULL || declaring_class[0] == '\0'
      || field_name == NULL || field_name[0] == '\0'
      || descriptor == NULL || descriptor[0] == '\0') {
    return serialize_field_expression("FIELD_NOT_FOUND", false,
        "VM_EXACT_FIELD_LOOKUP_V1", NULL, false);
  }

  ResourceMark rm;
  fieldDescriptor field;
  Klass *declaring = OopUtils::get_local_fd_by_name(
      owner(), std::string(declaring_class), std::string(field_name),
      std::string(descriptor), field);
  if (declaring == NULL || field.is_static()) {
    return serialize_field_expression("FIELD_NOT_FOUND", false,
        "VM_EXACT_FIELD_LOOKUP_V1", NULL, false);
  }

  SymInstance *owner_instance = ctx->find_sym_inst(owner());
  Expression *shadow = owner_instance == NULL
      ? NULL : owner_instance->get(field.offset());
  if (shadow != NULL) {
    if (shadow == SymbolExpression::get(Sym_NULL)) {
      return serialize_field_expression("NULL_REFERENCE", false,
          "VM_EXACT_NULL_REFERENCE_V1", shadow, false);
    }
    return serialize_field_expression("SYMBOLIC_FIELD", true,
        "VM_EXACT_FIELD_SHADOW_V1", shadow, false);
  }

  if (concrete_value.is_null()) {
    return serialize_field_expression("NULL_REFERENCE", false,
        "VM_EXACT_NULL_REFERENCE_V1",
        SymbolExpression::get(Sym_NULL), false);
  }
  oop concrete = concrete_value();
  if (concrete->klass() != NULL
      && concrete->klass()->name() == vmSymbols::java_lang_String()) {
    return serialize_field_expression("CONCRETE_STRING", false,
        "VM_EXACT_CONCRETE_STRING_V1",
        new ConStringSymbolExp(concrete), true);
  }
  return getSymbolicExpression(concrete_value);
}

bool ConcolicMngr::trackContainerExpression(
    Handle container, const char *prefix) {
  if (!has_active_context() || container.is_null() || prefix == NULL
      || prefix[0] == '\0') {
    return false;
  }
  oop target = container();
  const char *shape = ContainerSupport::shape(target);
  if (shape == NULL) return false;
  Expression *tracked =
      ctx->track_container(target, shape, std::string(prefix));
  if (tracked == NULL) return false;
  ctx->set_pc_admitted(true);
  return true;
}

bool ConcolicMngr::snapshotContainerExpression(
    Handle container, Handle keys, Handle values, jint kind) {
  if (!has_active_context() || container.is_null() || values.is_null()
      || !values()->is_objArray()) {
    return false;
  }

  oop target = container();
  objArrayOop snapshot_values = objArrayOop(values());
  objArrayOop snapshot_keys = NULL;
  if (!keys.is_null()) {
    if (!keys()->is_objArray()) return false;
    snapshot_keys = objArrayOop(keys());
  }

  // Arrays already carrying a symbolic state have recorded their element
  // stores exactly.  Re-boxing their concrete elements here would lose those
  // primitive store expressions, so only snapshot a previously untracked
  // array.
  if (kind == 3) {
    if (!target->is_array()
        || snapshot_values->length() != ((arrayOop)target)->length()) {
      return false;
    }
    if (ctx->find_container_state(target) != NULL) return true;
    arrayOop array = arrayOop(target);
    ctx->container_state(target, "INDEXED");
    for (int index = 0; index < snapshot_values->length(); ++index) {
      ctx->write_array_element(array, index,
          ContainerSupport::concrete_value(
              snapshot_values->obj_at(index)));
    }
    return ctx->find_container_state(target) != NULL;
  }

  // The Java runtime has already inspected the actual final value as a
  // Collection, Map, or Set.  This one-shot snapshot therefore follows that
  // observed shape instead of duplicating a concrete-class allowlist here.
  // Method-level symbolic handlers remain deliberately narrower.
  bool indexed = kind == 0;
  bool associative = kind == 1 || kind == 2;
  if (!indexed && !associative) return false;
  const char *shape = indexed ? "INDEXED" : "ASSOCIATIVE";
  if (associative
      && (snapshot_keys == NULL
          || snapshot_keys->length() != snapshot_values->length())) {
    return false;
  }

  // A container the recorder has already watched change carries its contents
  // in those operations, so it does not need to be told what it holds -- and
  // telling it would replace a history that relates the container to this
  // activation's inputs with a constant that holds only on the recorded path.
  // That is the same judgement the array branch above makes.  A container
  // whose state is still the bare STATE root has no such history, and is
  // exactly the unconstrained symbolic collection the empty base exists to
  // replace, so it is still snapshotted; so is any state that does not say.
  Expression *recorded = ctx->find_container_state(target);
  if (recorded != NULL && recorded->is_recorded_container_mutation()) {
    return true;
  }

  // SNAPSHOT_BASE(STATE) is an exact empty collection: its size is zero and
  // every associative key is absent.  Replaying the observed final members
  // from that base yields a path-final snapshot rather than an unconstrained
  // symbolic initial collection.  It denotes the same empty value as CLEAR
  // but states a different fact -- this recorder asserts what the container
  // held, where CLEAR reports a Collection.clear() the program executed.  The
  // two carry separate op names so that a consumer can tell a recorded
  // observation from an observed program action.
  exp_list_t no_arguments;
  Expression *initial = ctx->container_state(target, shape);
  Expression *state = new ContainerExpression(
      shape, "SNAPSHOT_BASE", initial, no_arguments);
  ctx->set_container_state(target, state);

  for (int index = 0; index < snapshot_values->length(); ++index) {
    exp_list_t arguments;
    if (indexed) {
      arguments.push_back(ContainerSupport::concrete_value(
          snapshot_values->obj_at(index)));
      state = new ContainerExpression(
          shape, "APPEND", state, arguments);
    } else {
      arguments.push_back(ContainerSupport::concrete_value(
          snapshot_keys->obj_at(index)));
      arguments.push_back(kind == 2
          ? static_cast<Expression *>(new ConExpression((jboolean)true))
          : ContainerSupport::concrete_value(
              snapshot_values->obj_at(index)));
      state = new ContainerExpression(
          shape, "PUT", state, arguments);
    }
    ctx->set_container_state(target, state);
  }
  return ctx->find_container_state(target) != NULL;
}

std::string ConcolicMngr::getRegionSummary() {
  using namespace rapidjson;
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("engine");
  writer.String("openjdk8-zero-concolic");
  writer.Key("active");
  writer.Bool(has_active_context());
  writer.Key("aborted");
  writer.Bool(ctx != NULL && ctx->is_aborted());
  writer.Key("abortReason");
  writer.String(ctx == NULL ? "" : ctx->get_abort_reason().c_str());
  writer.Key("complete");
  writer.Bool(has_active_context());
  writer.Key("status");
  writer.String(ctx == NULL ? "INACTIVE"
      : (ctx->is_aborted() ? "ABORTED" : "ACTIVE"));
  writer.Key("regionId");
  writer.String(ctx == NULL ? "" : ctx->get_region_id().c_str());
  writer.Key("taskId");
  writer.String(ctx == NULL ? "" : ctx->get_task_id().c_str());
  writer.Key("threadContextId");
  writer.Int64(ctx == NULL ? 0 : ctx->get_context_id());
  writer.Key("pathConditionRecordingPaused");
  writer.Bool(ctx != NULL && ctx->path_condition_pause_depth() > 0);
  writer.Key("pathConditionPauseDepth");
  writer.Int(ctx == NULL ? 0 : ctx->path_condition_pause_depth());
  writer.Key("pathCondition");
  if (has_active_context()) {
    const char *path_condition = ctx->get_path_condition().toString();
    writer.RawValue(path_condition, strlen(path_condition), kArrayType);
  } else {
    writer.StartArray();
    writer.EndArray();
  }
  writer.Key("branchEvents");
  if (ctx != NULL) {
    std::string branch_events = ctx->get_branch_events();
    writer.RawValue(branch_events.c_str(), branch_events.length(),
                    kObjectType);
  } else {
    writer.StartObject();
    writer.Key("schemaVersion");
    writer.Int(1);
    writer.Key("kind");
    writer.String("CONCOLIC_THREAD_BRANCH_EVENTS");
    writer.Key("active");
    writer.Bool(false);
    writer.Key("events");
    writer.StartArray();
    writer.EndArray();
    writer.EndObject();
  }
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

jlong ConcolicMngr::markBranch(const char *site_id, int occurrence) {
  // A marker is meaningful only when the current Java subtree can propagate
  // symbolic operands.  In particular, reject paused, non-tracking, and
  // method-symbolized frames rather than leaving a marker that a later frame
  // could accidentally claim.
  if (!can_do_concolic()) {
    if (ctx != NULL) ctx->cancel_pending_branch();
    return 0;
  }
  return ctx->mark_branch(site_id, occurrence);
}

std::string ConcolicMngr::getBranchEvents() {
  if (ctx != NULL) {
    return ctx->get_branch_events();
  }
  return std::string("{\"schemaVersion\":1,\"kind\":"
                     "\"CONCOLIC_THREAD_BRANCH_EVENTS\","
                     "\"active\":false,\"events\":[]}");
}

void ConcolicMngr::pausePathConditionRecording() {
  if (has_active_context()) {
    ctx->pause_path_condition_recording();
  }
}

void ConcolicMngr::resumePathConditionRecording() {
  if (has_active_context()) {
    ctx->resume_path_condition_recording();
  }
}

jlong ConcolicMngr::endConcolic() {
  if (!ctx) {
    tty->print_cr("Warning: corrupted concolic execution thread state, is startConcolic() invoked properly?");
    return 1;
  }

  // A successful start deliberately leaves mutex owned by this JavaThread
  // for the lifetime of the region.  JavaThread/OS-thread affinity and the
  // TLS context therefore make this the matching owner-side unlock; rejected
  // contenders never reach this path with a context.
  assert(_num_threads_in_concolic == 1, "should be");
  --_num_threads_in_concolic;

//  ctx->print();
  delete ctx;
  ctx = NULL;
  ThreadContext::memory_leak_check();
  pthread_mutex_unlock(&mutex);
  return 0;
}

void ConcolicMngr::printSymExp(Handle handle) {
  if (can_do_concolic()) {
    oop obj = handle();
    ctx->printSymExp(obj);
  }
}

void ConcolicMngr::symbolize(Handle handle) {
  if (can_explicitly_symbolize()) {
    tty->print("Symbolize!\n");
    ctx->set_pc_admitted(true);
    int pause_depth = ctx->path_condition_pause_depth();
    while (ctx->path_condition_pause_depth() > 0) {
      ctx->resume_path_condition_recording();
    }
    ctx->symbolize(handle);
    for (int index = 0; index < pause_depth; ++index) {
      ctx->pause_path_condition_recording();
    }
  } else {
    tty->print_cr("Warning: symbolize canned without proper ctx, try System.startConcolic() before symbolize");
  }
//  tty->print_cr("----- %s", ctx->get_code_pos_for_first("main").c_str());
}

void ConcolicMngr::symbolize(Handle handle, const char* prefix) {
  if (can_explicitly_symbolize()) {
    tty->print("Symbolize!\n");
    ctx->set_pc_admitted(true);
    int pause_depth = ctx->path_condition_pause_depth();
    while (ctx->path_condition_pause_depth() > 0) {
      ctx->resume_path_condition_recording();
    }
    ctx->symbolize(handle, prefix);
    for (int index = 0; index < pause_depth; ++index) {
      ctx->pause_path_condition_recording();
    }
  } else {
    tty->print_cr("Warning: symbolize canned without proper ctx, try System.startConcolic() before symbolize");
  }
//  tty->print_cr("----- %s", ctx->get_code_pos_for_first("main").c_str());
}

void ConcolicMngr::symbolizeField(Handle handle, const char* field_name,
                                  const char* prefix) {
  if (can_explicitly_symbolize()) {
    tty->print("Symbolize field!\n");
    ctx->set_pc_admitted(true);
    int pause_depth = ctx->path_condition_pause_depth();
    while (ctx->path_condition_pause_depth() > 0) {
      ctx->resume_path_condition_recording();
    }
    ctx->symbolize_field(handle,
        field_name == NULL ? "" : std::string(field_name),
        prefix == NULL ? "" : std::string(prefix));
    for (int index = 0; index < pause_depth; ++index) {
      ctx->pause_path_condition_recording();
    }
  } else {
    tty->print_cr("Warning: symbolizeField called without an active context");
  }
}

void ConcolicMngr::symbolizeExactField(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor, const char *prefix) {
  if (can_explicitly_symbolize()
      && !owner.is_null()
      && declaring_class != NULL && declaring_class[0] != '\0'
      && field_name != NULL && field_name[0] != '\0'
      && descriptor != NULL && descriptor[0] != '\0'
      && prefix != NULL && prefix[0] != '\0') {
    tty->print("Symbolize exact field!\n");
    ctx->set_pc_admitted(true);
    int pause_depth = ctx->path_condition_pause_depth();
    while (ctx->path_condition_pause_depth() > 0) {
      ctx->resume_path_condition_recording();
    }
    ctx->symbolize_exact_field(
        owner, std::string(declaring_class), std::string(field_name),
        std::string(descriptor), std::string(prefix));
    for (int index = 0; index < pause_depth; ++index) {
      ctx->pause_path_condition_recording();
    }
  } else {
    tty->print_cr(
        "Warning: symbolizeExactField called without an eligible field");
  }
}

void ConcolicMngr::observeExactPrimitiveField(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor) {
  if (!can_explicitly_symbolize() || owner.is_null()
      || declaring_class == NULL || declaring_class[0] == '\0'
      || field_name == NULL || field_name[0] == '\0'
      || descriptor == NULL || descriptor[0] == '\0') {
    tty->print_cr(
        "Warning: observeExactPrimitiveField called without an eligible field");
    return;
  }

  ResourceMark rm;
  fieldDescriptor field;
  Klass *declaring = OopUtils::get_local_fd_by_name(
      owner(), std::string(declaring_class), std::string(field_name),
      std::string(descriptor), field);
  if (declaring == NULL || field.is_static()
      || (strcmp(descriptor, "I") != 0
          && strcmp(descriptor, "J") != 0)) {
    tty->print_cr(
        "Warning: observeExactPrimitiveField supports only exact int/long fields");
    return;
  }

  SymInstance *instance = ctx->get_or_alloc_sym_inst(owner());
  if (instance == NULL) return;
  Expression *observed = strcmp(descriptor, "I") == 0
      ? static_cast<Expression *>(
          new ConExpression(owner()->int_field(field.offset())))
      : static_cast<Expression *>(
          new ConExpression(owner()->long_field(field.offset())));
  instance->set_sym_exp(field.offset(), observed);
  ctx->set_pc_admitted(true);
}

void ConcolicMngr::symbolizeMethod(Handle holder_name_handle,
                                   Handle callee_name_handle) {
  ResourceMark rm;
  const char *holder_name = OopUtils::java_string_to_c(holder_name_handle());
  const char *callee_name = OopUtils::java_string_to_c(callee_name_handle());

  ctx->symbolize_method(holder_name, callee_name);

  tty->print_cr("added symbolic method: %s.%s", holder_name, callee_name);
}

void ConcolicMngr::recordStmtObj(Handle stmt, Handle obj) {
  if (ctx == NULL) {
    // tty->print_cr(CL_RED"[warning] You should only call `recordStmtObj` after start concolic" CNONE);
    return;
  }
  ctx->record_stmt_obj(stmt(), obj());
}

void ConcolicMngr::recordPersistentObj(Handle obj) {
  if (ctx == NULL) {
    // tty->print_cr(CL_RED"[warning] You should only call `recordPersistentObj` after start concolic" CNONE);
    return;
  }
  ctx->record_persistent_obj(obj());
}

#else

jlong ConcolicMngr::startConcolic() {
  tty->print("Start concolic!\n");
  return 0;
}

jlong ConcolicMngr::endConcolic() {
  tty->print("End concolic!\n");
  return 0;
}

void ConcolicMngr::symbolize(Handle handle) {}

void ConcolicMngr::symbolizeMethod(Handle holder_name_handle,
                                   Handle callee_name_handle) {}
#endif
