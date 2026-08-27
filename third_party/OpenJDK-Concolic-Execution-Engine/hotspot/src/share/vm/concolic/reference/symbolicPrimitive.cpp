#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicPrimitive.hpp"
#include "symbolicString.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "concolic/exp/methodExpression.hpp"

template <>
const char *SymPrimitive<jchar>::ARRAY_TYPE_NAME = "[Ljava/lang/Character;";
template <>
const char *SymPrimitive<jboolean>::ARRAY_TYPE_NAME = "[Ljava/lang/Boolean;";
template <>
const char *SymPrimitive<jbyte>::ARRAY_TYPE_NAME = "[Ljava/lang/Byte;";
template <>
const char *SymPrimitive<jint>::ARRAY_TYPE_NAME = "[Ljava/lang/Integer;";
template <>
const char *SymPrimitive<jshort>::ARRAY_TYPE_NAME = "[Ljava/lang/Short;";
template <>
const char *SymPrimitive<jlong>::ARRAY_TYPE_NAME = "[Ljava/lang/Long;";
template <>
const char *SymPrimitive<jfloat>::ARRAY_TYPE_NAME = "[Ljava/lang/Float;";
template <>
const char *SymPrimitive<jdouble>::ARRAY_TYPE_NAME = "[Ljava/lang/Double;";

template <> const char *SymPrimitive<jchar>::TYPE_NAME = "java/lang/Character";
template <> const char *SymPrimitive<jboolean>::TYPE_NAME = "java/lang/Boolean";
template <> const char *SymPrimitive<jbyte>::TYPE_NAME = "java/lang/Byte";
template <> const char *SymPrimitive<jint>::TYPE_NAME = "java/lang/Integer";
template <> const char *SymPrimitive<jshort>::TYPE_NAME = "java/lang/Short";
template <> const char *SymPrimitive<jlong>::TYPE_NAME = "java/lang/Long";
template <> const char *SymPrimitive<jfloat>::TYPE_NAME = "java/lang/Float";
template <> const char *SymPrimitive<jdouble>::TYPE_NAME = "java/lang/Double";

template <class T>
SymPrimitive<T>::SymPrimitive(sym_rid_t sym_rid) : SymInstance(sym_rid), _exp(NULL) {}

template <class T> SymPrimitive<T>::~SymPrimitive() {}

template <class T> Expression *SymPrimitive<T>::get(int field_offset) {
  assert(field_offset % 8 == 0,
         "we are turning to field_offset, this should be true");
  return _exp;
}

template <class T>
void SymPrimitive<T>::init_sym_exp(int field_offset, Expression *exp) {
  assert(field_offset % 8 == 0,
         "we are turning to field_offset, this should be true");
  _exp = exp;
}

template <class T>
void SymPrimitive<T>::set_sym_exp(int field_offset, Expression *exp) {
  _exp = exp;
}

// One slot serves every offset, exactly as get() and set_sym_exp() treat it.
template <class T> bool SymPrimitive<T>::has_sym_exp(int field_offset) {
  return _exp != NULL;
}

template <class T> void SymPrimitive<T>::print() {
  tty->print_cr("SymPrimitive: ");
  _exp->print();
  tty->print("\n");
}

template <class T> Expression *SymPrimitive<T>::get_exp_of(oop obj) {
  assert(obj->klass()->name()->equals(TYPE_NAME), "should be");
  Expression *exp;
  if (obj->is_symbolic()) {
    SymInstance *sym_inst = ConcolicMngr::ctx->get_sym_inst(obj);
    exp = sym_inst->get_ref_exp();
    assert(exp != NULL, "NOT NULL");
    return exp;
  } else {
    return get_exp_of_helper(obj);
  }
}

template <> Expression *SymPrimitive<jchar>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_char_to_c(obj));
}
template <> Expression *SymPrimitive<jboolean>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_boolean_to_c(obj));
}
template <> Expression *SymPrimitive<jbyte>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_byte_to_c(obj));
}
template <> Expression *SymPrimitive<jint>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_int_to_c(obj));
}
template <> Expression *SymPrimitive<jshort>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_short_to_c(obj));
}
template <> Expression *SymPrimitive<jlong>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_long_to_c(obj));
}
template <> Expression *SymPrimitive<jfloat>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_float_to_c(obj));
}
template <> Expression *SymPrimitive<jdouble>::get_exp_of_helper(oop obj) {
  return new ConExpression(OopUtils::java_double_to_c(obj));
}

template class SymPrimitive<jchar>;
template class SymPrimitive<jboolean>;
template class SymPrimitive<jbyte>;
template class SymPrimitive<jint>;
template class SymPrimitive<jshort>;
template class SymPrimitive<jlong>;
template class SymPrimitive<jfloat>;
template class SymPrimitive<jdouble>;

template <> bool SymPrimitive<jchar>::invoke_method_helper(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_name() == "valueOf") {
    return match_callee_and_do_sym(handle, "(C)Ljava/lang/Character;");
  }
  return false;
}
template <> bool SymPrimitive<jboolean>::invoke_method_helper(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_name() == "valueOf") {
    return match_callee_and_do_sym(handle, "(Z)Ljava/lang/Boolean;");
  }
  return false;
}
template <> bool SymPrimitive<jbyte>::invoke_method_helper(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_name() == "valueOf") {
    return match_callee_and_do_sym(handle, "(B)Ljava/lang/Byte;");
  }
  return false;
}
template <> bool SymPrimitive<jint>::invoke_method_helper(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_name() == "parseInt") {
    ResourceMark rm;
    const char *signature =
        handle.get_callee_method()->signature()->as_C_string();
    if (strcmp(signature, "(Ljava/lang/String;)I") != 0 &&
        strcmp(signature, "(Ljava/lang/String;I)I") != 0) {
      return false;
    }
    bool need_symbolize = handle.general_check_param_symbolized();
    if (need_symbolize) {
      handle.general_prepare_param();
    }
    return need_symbolize;
  } else if (handle.get_callee_name() == "valueOf") {
    return match_callee_and_do_sym(handle, "(I)Ljava/lang/Integer;");
  }
  return false;
}
template <> bool SymPrimitive<jshort>::invoke_method_helper(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_name() == "valueOf") {
    return match_callee_and_do_sym(handle, "(S)Ljava/lang/Short;");
  }
  return false;
}
template <> bool SymPrimitive<jlong>::invoke_method_helper(MethodSymbolizerHandle &handle) {
    if (handle.get_callee_name() == "parseLong") {
      bool need_symbolize = handle.general_check_param_symbolized();
      if (need_symbolize) {
        handle.general_prepare_param();
      }
      return need_symbolize;
    } else if (handle.get_callee_name() == "valueOf") {
      return match_callee_and_do_sym(handle, "(J)Ljava/lang/Long;");
    }
    return false;
}
template <> bool SymPrimitive<jfloat>::invoke_method_helper(MethodSymbolizerHandle &handle) {
    return false;
}
template <> bool SymPrimitive<jdouble>::invoke_method_helper(MethodSymbolizerHandle &handle) {
    return false;
}

template <> Expression *SymPrimitive<jchar>::finish_method_helper(MethodSymbolizerHandle &handle) {
  ResourceMark rm;
  if (handle.get_callee_name() == "valueOf" &&
      !strcmp(handle.get_callee_method()->signature()->as_C_string(), "(C)Ljava/lang/Character;")) {
    // get result object from stack
    set_symbolic_field(
        handle.get_result<oop>(handle.get_result_type()),
        vmSymbols::value_name(),
        vmSymbols::char_signature(),
        handle
    );
    return handle.get_param_list()[0];
  }
  return NULL;
}

template <> Expression *SymPrimitive<jboolean>::finish_method_helper(MethodSymbolizerHandle &handle) {
  ResourceMark rm;
  if (handle.get_callee_name() == "valueOf" &&
      !strcmp(handle.get_callee_method()->signature()->as_C_string(), "(Z)Ljava/lang/Boolean;")) {
    // get result object from stack
    set_symbolic_field(
        handle.get_result<oop>(handle.get_result_type()),
        vmSymbols::value_name(),
        vmSymbols::bool_signature(),
        handle
    );
    return handle.get_param_list()[0];
  }
  return NULL;
}
template <> Expression *SymPrimitive<jbyte>::finish_method_helper(MethodSymbolizerHandle &handle) {
  ResourceMark rm;
  if (handle.get_callee_name() == "valueOf" &&
      !strcmp(handle.get_callee_method()->signature()->as_C_string(), "(B)Ljava/lang/Byte;")) {
    // get result object from stack
    set_symbolic_field(
        handle.get_result<oop>(handle.get_result_type()),
        vmSymbols::value_name(),
        vmSymbols::byte_signature(),
        handle
    );
    return handle.get_param_list()[0];
  }
  return NULL;
}

template <> Expression * SymPrimitive<jint>::finish_method_helper(MethodSymbolizerHandle &handle) {
  ResourceMark rm;
  const char *signature =
      handle.get_callee_method()->signature()->as_C_string();
  if (handle.get_callee_name() == "parseInt" &&
      (!strcmp(signature, "(Ljava/lang/String;)I") ||
       !strcmp(signature, "(Ljava/lang/String;I)I"))) {
    Expression *exp = new MethodReturnSymbolExp(T_INT);
    ConcolicMngr::record_path_condition(new MethodExpression(
        handle.get_callee_holder_name(), handle.get_callee_name(),
        handle.get_param_list(), exp, false));
    return exp;
  }
  if (handle.get_callee_name() == "valueOf" &&
      !strcmp(signature, "(I)Ljava/lang/Integer;")) {
    // get result object from stack
    set_symbolic_field(
        handle.get_result<oop>(handle.get_result_type()),
        vmSymbols::value_name(),
        vmSymbols::int_signature(),
        handle
    );
    return handle.get_param_list()[0];
  }

  return NULL;
}

template <> Expression * SymPrimitive<jshort>::finish_method_helper(MethodSymbolizerHandle &handle) {
  ResourceMark rm;
  if (handle.get_callee_name() == "valueOf" &&
      !strcmp(handle.get_callee_method()->signature()->as_C_string(), "(S)Ljava/lang/Short;")) {
    // get result object from stack
    set_symbolic_field(
        handle.get_result<oop>(handle.get_result_type()),
        vmSymbols::value_name(),
        vmSymbols::short_signature(),
        handle
    );
    return handle.get_param_list()[0];
  }
  return NULL;
}

template <> Expression * SymPrimitive<jlong>::finish_method_helper(MethodSymbolizerHandle &handle) {
    if (handle.get_callee_name() == "parseLong") {
      Expression *exp = new MethodReturnSymbolExp(T_LONG);
      ConcolicMngr::record_path_condition(new MethodExpression(
          handle.get_callee_holder_name(), handle.get_callee_name(),
          handle.get_param_list(), exp, false));
      return exp;
    }
  ResourceMark rm;
  if (handle.get_callee_name() == "valueOf" &&
      !strcmp(handle.get_callee_method()->signature()->as_C_string(), "(J)Ljava/lang/Long;")) {
    // get result object from stack
    set_symbolic_field(
        handle.get_result<oop>(handle.get_result_type()),
        vmSymbols::value_name(),
        vmSymbols::long_signature(),
        handle
    );
    return handle.get_param_list()[0];
  }

  return NULL;
}

template <> Expression * SymPrimitive<jfloat>::finish_method_helper(MethodSymbolizerHandle &handle) {
    return NULL;
}
template <> Expression * SymPrimitive<jdouble>::finish_method_helper(MethodSymbolizerHandle &handle) {
    return NULL;
}

template<class T>
void
SymPrimitive<T>::set_symbolic_field(oop obj, Symbol *fld_name, Symbol *fld_tp_sig, MethodSymbolizerHandle &handle) {
  Expression *exp = handle.get_param_list()[0];
  SymInstance *sym_inst = ConcolicMngr::ctx->get_or_alloc_sym_inst(obj);
  fieldDescriptor fd;
  Klass *fld_klass = obj->klass()->find_field(
      fld_name,
      fld_tp_sig,
      &fd
  );
  sym_inst->set_sym_exp(fd.offset(), exp);
  sym_inst->mark_semantic_expression();
}

template<class T>
bool SymPrimitive<T>::match_callee_and_do_sym(MethodSymbolizerHandle &handle, const char* callee_signature) {
  ResourceMark rm;
  if (!strcmp(handle.get_callee_method()->signature()->as_C_string(), callee_signature)) {
    bool need_symbolize = handle.general_check_param_symbolized();
    if (need_symbolize) {
      handle.general_prepare_param();
    }
    return need_symbolize;
  }

  return false;
}

static bool is_supported_decimal_integer_to_string(
    MethodSymbolizerHandle &handle) {
    if (handle.get_callee_holder_name() != SymPrimitive<jint>::TYPE_NAME ||
        handle.get_callee_name() != "toString") {
      return false;
    }

    ResourceMark rm;
    const char *signature =
        handle.get_callee_method()->signature()->as_C_string();
    if (handle.get_callee_method()->is_static()) {
      return strcmp(signature, "(I)Ljava/lang/String;") == 0;
    }
    return strcmp(signature, "()Ljava/lang/String;") == 0;
}

static std::string unsupported_primitive_string_operation(
    MethodSymbolizerHandle &handle) {
    ResourceMark rm;
    const char *signature =
        handle.get_callee_method()->signature()->as_C_string();
    return std::string("unsupportedPrimitiveStringConversion:") +
        handle.get_callee_holder_name() + "." +
        handle.get_callee_name() + signature;
}

bool primitive_invoke_method_helper(MethodSymbolizerHandle &handle,BasicType type){
    const std::string &callee_name = handle.get_callee_name();
    if (callee_name == "toHexString" || callee_name == "toString") {
        bool need_symbolize = handle.general_check_param_symbolized();
        if (need_symbolize) {
          handle.general_prepare_param();
        }
        return need_symbolize;
    }
    switch (type) {
        case T_CHAR:
            return SymPrimitive<jchar>::invoke_method_helper(handle);
        case T_BOOLEAN:
            return SymPrimitive<jboolean>::invoke_method_helper(handle);
        case T_BYTE:
            return SymPrimitive<jbyte>::invoke_method_helper(handle);
        case T_INT:
            return SymPrimitive<jint>::invoke_method_helper(handle);
        case T_SHORT:
            return SymPrimitive<jshort>::invoke_method_helper(handle);
        case T_LONG:
            return SymPrimitive<jlong>::invoke_method_helper(handle);
        case T_FLOAT:
            return SymPrimitive<jfloat>::invoke_method_helper(handle);
        case T_DOUBLE:
            return SymPrimitive<jdouble>::invoke_method_helper(handle);
        default:
            ShouldNotReachHere();
    }
}

Expression *primitive_finish_method_helper(MethodSymbolizerHandle &handle, BasicType type){

    const std::string &callee_name = handle.get_callee_name();
    if (callee_name == "toHexString" || callee_name == "toString") {
        exp_list_t &params = handle.get_param_list();
        guarantee(!params.empty(), "primitive string conversion needs provenance");
        oop res_obj = handle.get_result<oop>(T_OBJECT);
        guarantee(res_obj != NULL,
                  "primitive string conversion returned null");
        Expression *string_exp;
        if (is_supported_decimal_integer_to_string(handle)) {
          // These are the only two conversions whose current downstream model
          // proves Java decimal semantics: Integer.toString(int) and the
          // equivalent Integer instance method.  Both have exactly one
          // provenance expression (the primitive int value).
          guarantee(params.size() == 1,
                    "decimal Integer.toString has one symbolic parameter");
          string_exp = OpStrExpression::to_string(params[0]);
        } else {
          // Keep every receiver/argument and the exact holder+descriptor.  A
          // downstream encoder must reject this operation unless it adds and
          // validates the corresponding Java conversion semantics.  In
          // particular, radix and hexadecimal conversions must never be
          // mistaken for decimal Integer.toString.
          string_exp = new OpStrExpression(
              unsupported_primitive_string_operation(handle), params);
        }
        // The result expression always travels on the caller's operand edge.
        // A fresh String may additionally retain it as object state, but a
        // VM-global/interned String must remain alias-specific: attaching the
        // expression to that shared oop would also symbolize unrelated
        // literals in this context.  Merely computing a conversion is not a
        // path decision, so unsupported provenance is reported only if a
        // later symbolic operation actually consumes this returned edge.
        if (!ConcolicMngr::ctx->requires_detached_object_shadow(res_obj)) {
          SymString *sym_res_str = static_cast<SymString *>(
              ConcolicMngr::ctx->get_or_alloc_sym_inst(res_obj));
          if (sym_res_str != NULL) {
            sym_res_str->set_ref_exp(string_exp);
          }
        }

        return string_exp;
    }

    switch (type) {
        case T_CHAR:
            return SymPrimitive<jchar>::finish_method_helper(handle);
        case T_BOOLEAN:
            return SymPrimitive<jboolean>::finish_method_helper(handle);
        case T_BYTE:
            return SymPrimitive<jbyte>::finish_method_helper(handle);
        case T_INT:
            return SymPrimitive<jint>::finish_method_helper(handle);
        case T_SHORT:
            return SymPrimitive<jshort>::finish_method_helper(handle);
        case T_LONG:
            return SymPrimitive<jlong>::finish_method_helper(handle);
        case T_FLOAT:
            return SymPrimitive<jfloat>::finish_method_helper(handle);
        case T_DOUBLE:
            return SymPrimitive<jdouble>::finish_method_helper(handle);
        default:
            ShouldNotReachHere();
    }
}

BasicType primitive_target(const std::string &class_name){
    if (class_name == SymPrimitive<jchar>::TYPE_NAME){
        return T_CHAR;
    } else if(class_name == SymPrimitive<jboolean>::TYPE_NAME){
        return T_BOOLEAN;
    } else if (class_name == SymPrimitive<jbyte>::TYPE_NAME){
        return T_BYTE;
    } else if (class_name == SymPrimitive<jint>::TYPE_NAME){
        return T_INT;
    } else if(class_name == SymPrimitive<jshort>::TYPE_NAME){
        return T_SHORT;
    } else if (class_name == SymPrimitive<jlong>::TYPE_NAME){
        return T_LONG;
    } else if (class_name == SymPrimitive<jfloat>::TYPE_NAME){
        return T_FLOAT;
    } else if (class_name == SymPrimitive<jdouble>::TYPE_NAME){
        return T_DOUBLE;
    } else{
        return T_ILLEGAL;
    }
}

#endif
