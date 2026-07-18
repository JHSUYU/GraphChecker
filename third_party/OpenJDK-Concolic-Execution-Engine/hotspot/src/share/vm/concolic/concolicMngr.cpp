#include "concolic/concolicMngr.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "oops/arrayKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "oops/typeArrayOop.hpp"
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

typedef rapidjson::Writer<rapidjson::StringBuffer> ArrayValueWriter;

Expression *existing_object_reference_expression(oop element) {
  if (element == NULL) return SymbolExpression::get(Sym_NULL);
  if (element->is_array()) return NULL;
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(element);
  return instance == NULL ? NULL : instance->get_ref_exp();
}

void serialize_temporary_expression(ArrayValueWriter &writer,
                                    Expression *expression) {
  guarantee(expression != NULL, "temporary expression required");
  expression->inc_ref();
  expression->serialize(writer);
  Expression::gc(expression);
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

void serialize_concrete_primitive(ArrayValueWriter &writer,
                                  typeArrayOop array, BasicType type,
                                  int index) {
  switch (type) {
    case T_BOOLEAN:
      serialize_temporary_expression(
          writer, new ConExpression(array->bool_at(index)));
      return;
    case T_BYTE:
      serialize_temporary_expression(
          writer, new ConExpression(array->byte_at(index)));
      return;
    case T_CHAR:
      serialize_temporary_expression(
          writer, new ConExpression(array->char_at(index)));
      return;
    case T_SHORT:
      serialize_temporary_expression(
          writer, new ConExpression(array->short_at(index)));
      return;
    case T_INT:
      serialize_temporary_expression(
          writer, new ConExpression(array->int_at(index)));
      return;
    case T_LONG:
      serialize_temporary_expression(
          writer, new ConExpression(array->long_at(index)));
      return;
    case T_FLOAT:
      serialize_temporary_expression(
          writer, new ConExpression(array->float_at(index)));
      return;
    case T_DOUBLE:
      serialize_temporary_expression(
          writer, new ConExpression(array->double_at(index)));
      return;
    default:
      writer.Null();
      return;
  }
}

bool array_element_complete(arrayOop array, BasicType component_type,
                            const ArrayInternal *internal, int index) {
  if (internal != NULL && !internal->is_valid(index)) return false;
  if (internal != NULL && internal->load(index) != NULL) return true;
  if (component_type != T_OBJECT && component_type != T_ARRAY) return true;

  oop element = objArrayOop(array)->obj_at(index);
  return element == NULL
      || existing_object_reference_expression(element) != NULL;
}

bool array_value_is_symbolic(arrayOop array, BasicType component_type,
                             const ArrayInternal *internal) {
  if (array->is_symbolic()) return true;
  for (int index = 0; index < array->length(); ++index) {
    if (internal != NULL && internal->has_expression(index)) return true;
    if (component_type == T_OBJECT || component_type == T_ARRAY) {
      oop element = objArrayOop(array)->obj_at(index);
      if (existing_object_reference_expression(element) != NULL
          && element != NULL) {
        return true;
      }
    }
  }
  return false;
}

void serialize_array_value(ArrayValueWriter &writer, arrayOop array) {
  ResourceMark rm;
  Symbol *array_name_symbol = array->klass()->name();
  const char *array_descriptor = array_name_symbol == NULL
      ? "" : array_name_symbol->as_C_string();
  const char *component_descriptor = array_descriptor[0] == '['
      ? array_descriptor + 1 : "";
  BasicType component_type =
      ArrayKlass::cast(array->klass())->element_type();
  ArrayInternal *internal =
      ConcolicMngr::ctx->find_array_internal(array);
  SymArr *symbolic_array = ConcolicMngr::ctx->find_sym_array(array);
  bool elements_complete = true;
  for (int index = 0; index < array->length(); ++index) {
    if (!array_element_complete(array, component_type, internal, index)) {
      elements_complete = false;
      break;
    }
  }

  writer.StartObject();
  writer.Key("_type");
  writer.String("ArrayValueExpression");
  writer.Key("_schema_version");
  writer.Int(1);
  writer.Key("_java_type");
  writer.String(array_descriptor);
  writer.Key("_component_java_type");
  writer.String(component_descriptor);
  writer.Key("_concrete_length");
  writer.Int(array->length());
  writer.Key("_length_exp");
  // V1 is a finite snapshot of the concrete JVM value at this observation
  // point.  Its exact extent is therefore the concrete length even when the
  // source array has a symbolic length expression elsewhere in the PC.
  serialize_temporary_expression(
      writer, new ConExpression((jint) array->length()));
  writer.Key("_elements_complete");
  writer.Bool(elements_complete);
  writer.Key("_elements");
  writer.StartArray();
  for (int index = 0; index < array->length(); ++index) {
    writer.StartObject();
    writer.Key("index");
    writer.Int(index);
    writer.Key("expression");

    Expression *shadow = internal == NULL ? NULL : internal->load(index);
    const char *provenance = NULL;
    const char *source_provenance = NULL;
    if (internal != NULL && !internal->is_valid(index)) {
      writer.Null();
      provenance = "ARRAY_SHADOW";
      source_provenance = internal->provenance(index);
    } else if (shadow != NULL) {
      shadow->serialize(writer);
      provenance = "ARRAY_SHADOW";
    } else if (component_type != T_OBJECT && component_type != T_ARRAY) {
      serialize_concrete_primitive(writer, typeArrayOop(array),
                                   component_type, index);
      provenance = "CONCRETE_PRIMITIVE";
    } else {
      oop element = objArrayOop(array)->obj_at(index);
      Expression *reference =
          existing_object_reference_expression(element);
      if (reference != NULL) {
        reference->serialize(writer);
        provenance = element == NULL
            ? "CONCRETE_NULL" : "SYMBOLIC_ELEMENT";
      } else {
        writer.Null();
        provenance = "SYMBOLIC_ELEMENT";
        source_provenance = "OPAQUE_CONCRETE_NON_NULL_REFERENCE";
      }
    }

    writer.Key("provenance");
    writer.String(provenance == NULL ? "UNAVAILABLE" : provenance);
    if (source_provenance != NULL) {
      // Parsers ignore unknown fields; retain a precise reason only on
      // already-incomplete elements for diagnostics without changing the
      // four-value canonical provenance contract.
      writer.Key("source_provenance");
      writer.String(source_provenance);
    }
    writer.EndObject();
  }
  writer.EndArray();
  if (symbolic_array != NULL) {
    char engine_array_id[64];
    int written = snprintf(engine_array_id, sizeof(engine_array_id),
                           "A%c_%lu", type2char(component_type),
                           symbolic_array->get_sym_rid());
    guarantee(written > 0 && written < (int) sizeof(engine_array_id),
              "engine array id overflow");
    writer.Key("_engine_array_id");
    writer.String(engine_array_id);
    writer.Key("_engine_array_id_authority");
    writer.String("VM_ACTIVE_SYM_ARRAY_ID_V1");
  }
  writer.Key("_authority");
  writer.String("VM_EXACT_FINITE_ARRAY_VALUE_V1");
  writer.EndObject();
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
                                        const char *activation_id) {
  jlong result = startConcolic(thread);
  if (result == 0 && ctx != NULL) {
    ctx->set_region_metadata(region_id, activation_id);
  }
  return result;
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

  if (!has_active_context() || handle.is_null()) {
    writer.Key("kind");
    writer.String(handle.is_null() ? "NULL" : "CONCOLIC_DISABLED");
    writer.Key("symbolic");
    writer.Bool(false);
    writer.EndObject();
    return std::string(buffer.GetString(), buffer.GetLength());
  }

  oop obj = handle();
  bool symbolic = obj->is_symbolic();
  if (obj->is_array()) {
    arrayOop array = arrayOop(obj);
    BasicType component_type =
        ArrayKlass::cast(array->klass())->element_type();
    symbolic = array_value_is_symbolic(
        array, component_type, ctx->find_array_internal(array));
  }
  writer.Key("symbolic");
  writer.Bool(symbolic);
  Expression *expression = NULL;
  bool temporary_expression = false;
  if (obj->is_array()) {
    writer.Key("kind");
    writer.String("ARRAY_VALUE");
  } else if (symbolic) {
    writer.Key("kind");
    writer.String("SYMBOLIC_OBJECT");
    SymInstance *instance = ctx->get_sym_inst(obj);
    if (instance != NULL) {
      expression = instance->get_ref_exp();
    }
  } else {
    expression = concrete_boxed_primitive_expression(obj);
    temporary_expression = expression != NULL;
    writer.Key("kind");
    writer.String(temporary_expression
        ? "CONCRETE_PRIMITIVE" : "CONCRETE_OBJECT");
  }

  writer.Key("expression");
  if (obj->is_array()) {
    serialize_array_value(writer, arrayOop(obj));
  } else if (expression == NULL) {
    writer.Null();
  } else if (temporary_expression) {
    serialize_temporary_expression(writer, expression);
  } else {
    expression->serialize(writer);
  }
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
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
  writer.Key("regionId");
  writer.String(ctx == NULL ? "" : ctx->get_region_id().c_str());
  writer.Key("activationId");
  writer.String(ctx == NULL ? "" : ctx->get_activation_id().c_str());
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
  if (has_active_context()) {
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
  if (ctx == NULL || ctx->path_condition_pause_depth() > 0) {
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
  if (ctx != NULL) {
    ctx->pause_path_condition_recording();
  }
}

void ConcolicMngr::resumePathConditionRecording() {
  if (ctx != NULL) {
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
