#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "classfile/vmSymbols.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/consumerBoundaryExpression.hpp"
#include "concolic/exp/readFromExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicString.hpp"

#include <stdio.h>

const char *ContainerSupport::shape(oop value) {
  if (value == NULL) return NULL;
  if (value->is_array()) return "INDEXED";
  if (value->klass() == NULL || value->klass()->name() == NULL) return NULL;
  Symbol *name = value->klass()->name();
  bool abstract_list = false;
  for (Klass *current = value->klass(); current != NULL;
       current = current->super()) {
    Symbol *current_name = current->name();
    if (current_name != NULL
        && current_name->equals("java/util/AbstractList")) {
      abstract_list = true;
      break;
    }
  }
  if (abstract_list || name->equals("java/util/ArrayDeque")) {
    return "INDEXED";
  }
  if (name->equals("java/util/HashMap")
      || name->equals("java/util/LinkedHashMap")
      || name->equals("java/util/HashSet")
      || name->equals("java/util/LinkedHashSet")) {
    return "ASSOCIATIVE";
  }
  return NULL;
}

bool ContainerSupport::indexed(oop value) {
  const char *value_shape = shape(value);
  return value_shape != NULL && value_shape[0] == 'I';
}

bool ContainerSupport::associative(oop value) {
  const char *value_shape = shape(value);
  return value_shape != NULL && value_shape[0] == 'A';
}

BasicType ContainerSupport::result_type(oop result, BasicType declared) {
  if (result == NULL || declared != T_OBJECT) return declared;
  Symbol *type = result->klass()->name();
  if (type->equals(SymPrimitive<jboolean>::TYPE_NAME)) return T_BOOLEAN;
  if (type->equals(SymPrimitive<jbyte>::TYPE_NAME)) return T_BYTE;
  if (type->equals(SymPrimitive<jchar>::TYPE_NAME)) return T_CHAR;
  if (type->equals(SymPrimitive<jshort>::TYPE_NAME)) return T_SHORT;
  if (type->equals(SymPrimitive<jint>::TYPE_NAME)) return T_INT;
  if (type->equals(SymPrimitive<jlong>::TYPE_NAME)) return T_LONG;
  if (type->equals(SymPrimitive<jfloat>::TYPE_NAME)) return T_FLOAT;
  if (type->equals(SymPrimitive<jdouble>::TYPE_NAME)) return T_DOUBLE;
  return T_OBJECT;
}

std::string ContainerSupport::java_type(oop result, BasicType declared) {
  if (result != NULL
      && result->klass()->name() == vmSymbols::java_lang_String()) {
    return "Ljava/lang/String;";
  }
  return std::string(1, type2char(result_type(result, declared)));
}

bool ContainerSupport::follows_callee_body(const std::string &callee_name) {
  return callee_name == "<init>";
}

bool ContainerSupport::claims_state(MethodSymbolizerHandle &handle) {
  Method *callee = handle.get_callee_method();
  if (callee == NULL || callee->is_static()) return false;
  oop receiver = handle.get_param<oop>(0);
  if (receiver == NULL) return false;
  if (ConcolicMngr::ctx->find_container_state(receiver) != NULL
      || ConcolicMngr::ctx->find_stack_slot(
          handle.get_caller_stack_begin_offset()) != NULL) {
    return true;
  }
  if (receiver->is_array()) {
    SymArr *array = ConcolicMngr::ctx->find_sym_array((arrayOop)receiver);
    return array != NULL && array->has_semantic_expression();
  }
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  return instance != NULL && instance->has_semantic_expression();
}

bool ContainerSupport::measures(Expression *length, Expression *state) {
  if (length == NULL || state == NULL) return false;
  ContainerExpression *size = length->as_container_expression();
  return size != NULL && size->get_operation() == "SIZE"
      && size->get_receiver() == state;
}

std::string ContainerSupport::measurement(Expression *length,
                                          Expression *state) {
  if (measures(length, state)) return "MEASURED";
  if (length == NULL) return "LENGTH_NOT_TRACKED";
  ContainerExpression *container = length->as_container_expression();
  if (container == NULL) return "LENGTH_IS_NOT_A_CONTAINER_RELATION";
  if (container->get_operation() != "SIZE") {
    return "LENGTH_IS_" + container->get_operation();
  }
  return "LENGTH_SIZES_ANOTHER_STATE";
}

std::string ContainerSupport::unsupported(const char *category,
                                          MethodSymbolizerHandle &handle) {
  std::string reason(category == NULL ? "UNSPECIFIED" : category);
  reason += ":";
  reason += handle.get_callee_holder_name();
  reason += ".";
  reason += handle.get_callee_name();
  Method *callee = handle.get_callee_method();
  if (callee != NULL && callee->signature() != NULL) {
    reason += callee->signature()->as_C_string();
  }
  return reason;
}

// ---------------------------------------------------------------------------
// Selected whole-container state.
// ---------------------------------------------------------------------------

SharedFieldVersions::Location ContainerSupport::state_location(oop container) {
  SharedFieldVersions::Location location;
  if (container == NULL || ConcolicMngr::ctx == NULL) return location;
  sym_rid_t owner = ConcolicMngr::ctx->canonical_container_id(container);
  if (owner == NULL_SYM_RID) return location;
  return SharedFieldVersions::Location(
      owner, SharedFieldVersions::SLOT_WHOLE_STATE,
      SharedFieldVersions::LOC_MAP_STATE);
}

jlong ContainerSupport::publish_state(oop container, Expression *new_state,
                                      const char *operation) {
  // The store's own relaxed counter first: with nothing selected anywhere
  // there is no provenance question, and this is on the path of every tracked
  // container mutation the workload performs.
  if (new_state == NULL || !SharedFieldVersions::has_carriers()) return 0;
  SharedFieldVersions::Location location = state_location(container);
  if (!location.is_valid() || !SharedFieldVersions::is_carrier(location)) {
    return 0;
  }
  // The publishing task already names the merged local path case.  Copying
  // the complete PC into every PUT/REMOVE version is both redundant and
  // prohibitively large in service loops; the Composer binds read-from arms
  // to that task's case selector instead.
  return SharedFieldVersions::publish(
      location, new_state, NULL, SharedFieldVersions::VERSION_STATE, operation);
}

bool ContainerSupport::mark_state_gap(oop container, const char *reason) {
  if (!SharedFieldVersions::has_carriers()) return false;
  SharedFieldVersions::Location location = state_location(container);
  return SharedFieldVersions::mark_writer_set_incomplete(location);
}

ContainerSupport::StateQuery ContainerSupport::query_state(
    oop container, const char *shape, const char *operation,
    const exp_list_t &arguments, BasicType result_type,
    const std::string &java_type) {
  StateQuery answer;
  if (operation == NULL) return answer;
  const std::string type_name = java_type.empty()
      ? std::string(1, type2char(result_type)) : java_type;

  if (!SharedFieldVersions::has_carriers()) return answer;
  SharedFieldVersions::Location location = state_location(container);
  if (!location.is_valid() || !SharedFieldVersions::is_carrier(location)) {
    return answer;
  }
  answer.selected = true;

  SharedFieldVersions::ReadPlan plan;
  if (!SharedFieldVersions::plan_read(location, &plan)) {
    return answer;
  }

  // An untracked writer produces an open coverage result, not a symbolic map
  // state.  plan_read has already recorded that gap; keep the concrete query
  // path and do not manufacture a state the solver can choose.
  if (plan.candidates.empty()) return answer;

  // The query applied to that writer's state, not the state.  This is the
  // whole difference between a scalar arm and a container arm: two writers
  // that installed different states give two different answers here even when
  // the member they wrote happens to be equal.  Everything else about the
  // node is the shared shape SharedFieldVersions::build_read_from writes.
  std::vector<Expression *> arm_values;
  arm_values.reserve(plan.candidates.size());
  for (size_t index = 0; index < plan.candidates.size(); ++index) {
    arm_values.push_back(new ContainerExpression(
        shape, operation, plan.candidates[index].value, arguments,
        result_type, type_name));
  }
  answer.expression = SharedFieldVersions::build_read_from(
      plan, location, type_name, arm_values);
  return answer;
}

Expression *ContainerSupport::concrete_value(oop value) {
  if (value == NULL) return SymbolExpression::get(Sym_NULL);
  if (value->is_array()) {
    SymArr *array =
        ConcolicMngr::ctx->get_or_alloc_sym_array((arrayOop)value);
    if (array != NULL && array->get_ref_exp() != NULL) {
      return array->get_ref_exp();
    }
    return array == NULL
        ? static_cast<Expression *>(new PlaceHolderSymbolExp(value))
        : static_cast<Expression *>(new ArraySymbolExp(
              array->get_sym_rid(), array->get_version(), T_OBJECT));
  }
  Symbol *type = value->klass()->name();
  if (type->equals(SymPrimitive<jboolean>::TYPE_NAME))
    return SymPrimitive<jboolean>::get_exp_of(value);
  if (type->equals(SymPrimitive<jbyte>::TYPE_NAME))
    return SymPrimitive<jbyte>::get_exp_of(value);
  if (type->equals(SymPrimitive<jchar>::TYPE_NAME))
    return SymPrimitive<jchar>::get_exp_of(value);
  if (type->equals(SymPrimitive<jshort>::TYPE_NAME))
    return SymPrimitive<jshort>::get_exp_of(value);
  if (type->equals(SymPrimitive<jint>::TYPE_NAME))
    return SymPrimitive<jint>::get_exp_of(value);
  if (type->equals(SymPrimitive<jlong>::TYPE_NAME))
    return SymPrimitive<jlong>::get_exp_of(value);
  if (type->equals(SymPrimitive<jfloat>::TYPE_NAME))
    return SymPrimitive<jfloat>::get_exp_of(value);
  if (type->equals(SymPrimitive<jdouble>::TYPE_NAME))
    return SymPrimitive<jdouble>::get_exp_of(value);
  if (type == vmSymbols::java_lang_String())
    return SymString::get_exp_of(value);
  SymInstance *identity =
      ConcolicMngr::ctx->get_or_alloc_sym_inst(value);
  return identity == NULL ? new PlaceHolderSymbolExp(value)
                          : identity->get_or_create_ref_exp(value);
}

Expression *ContainerSupport::semantic_value(oop value) {
  if (value == NULL || ConcolicMngr::ctx == NULL) return NULL;
  if (value->is_array()) {
    SymArr *array = ConcolicMngr::ctx->find_sym_array((arrayOop)value);
    return array != NULL && array->has_semantic_expression()
        ? array->get_ref_exp() : NULL;
  }
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(value);
  return instance != NULL && instance->has_semantic_expression()
      ? instance->get_ref_exp() : NULL;
}

Expression *ContainerSupport::concrete_result(
    MethodSymbolizerHandle &handle) {
  BasicType type = handle.get_result_type();
  switch (type) {
    case T_BOOLEAN:
      return new ConExpression(
          (jboolean)handle.get_result<jint>(T_BOOLEAN));
    case T_BYTE:
      return new ConExpression((jbyte)handle.get_result<jint>(T_BYTE));
    case T_CHAR:
      return new ConExpression((jchar)handle.get_result<jint>(T_CHAR));
    case T_SHORT:
      return new ConExpression((jshort)handle.get_result<jint>(T_SHORT));
    case T_INT:
      return new ConExpression(handle.get_result<jint>(T_INT));
    case T_LONG:
      return new ConExpression(handle.get_result<jlong>(T_LONG));
    case T_FLOAT:
      return new ConExpression(handle.get_result<jfloat>(T_FLOAT));
    case T_DOUBLE:
      return new ConExpression(handle.get_result<jdouble>(T_DOUBLE));
    case T_OBJECT:
    case T_ARRAY:
      return concrete_value(handle.get_result<oop>(type));
    default:
      return NULL;
  }
}

void ContainerSupport::constrain_result(
    MethodSymbolizerHandle &handle, Expression *expression) {
  if (expression == NULL) return;
  Expression *concrete = concrete_result(handle);
  if (concrete == NULL) return;
  ConcolicMngr::record_path_condition(
      new OpSymExpression(expression, concrete, op_eq, true));
}

void ContainerSupport::constrain_position(
    const char *shape, Expression *state, Expression *position,
    bool allow_end) {
  if (state == NULL || position == NULL) return;
  exp_list_t no_arguments;
  Expression *size =
      new ContainerExpression(shape, "SIZE", state, no_arguments, T_INT);
  ConcolicMngr::record_path_condition(new OpSymExpression(
      position, new ConExpression((jint)0), op_ge, true));
  ConcolicMngr::record_path_condition(new OpSymExpression(
      position, size, allow_end ? op_le : op_lt, true));
}

void ContainerSupport::attach_result(oop result, Expression *expression,
                                     oop owner) {
  if (result == NULL || expression == NULL) return;
  if (result->is_array()) {
    SymArr *array =
        ConcolicMngr::ctx->get_or_alloc_sym_array((arrayOop)result);
    if (array != NULL) array->set_ref_exp(expression);
    return;
  }
  SymInstance *instance =
      ConcolicMngr::ctx->get_or_alloc_sym_inst(result);
  if (instance == NULL) return;
  instance->set_ref_exp(expression);
  instance->enable_demand_symbolic_fields();
  if (owner != NULL) {
    ConcolicMngr::ctx->alias_container(result, owner);
  }
}

#endif  // ENABLE_CONCOLIC
