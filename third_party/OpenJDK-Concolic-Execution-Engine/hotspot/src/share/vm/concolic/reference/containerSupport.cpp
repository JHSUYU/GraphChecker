#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "classfile/vmSymbols.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicString.hpp"

const char *ContainerSupport::shape(oop value) {
  if (value == NULL) return NULL;
  if (value->is_array()) return "INDEXED";
  if (value->klass() == NULL || value->klass()->name() == NULL) return NULL;
  Symbol *name = value->klass()->name();
  if (name->equals("java/util/ArrayList")
      || name->equals("java/util/AbstractList")
      || name->equals("java/util/ArrayDeque")) {
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
