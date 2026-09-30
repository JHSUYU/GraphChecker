#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicPrimitive.hpp"
#include "symbolicString.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "concolic/exp/methodExpression.hpp"
#include "classfile/javaClasses.hpp"
#include "classfile/symbolTable.hpp"
#include "classfile/systemDictionary.hpp"
#include "prims/jvm.h"
#include "runtime/fieldDescriptor.hpp"
#include "runtime/orderAccess.inline.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/sessionSymbolicHeap.hpp"

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

template <class T> Expression *SymPrimitive<T>::get_exp_of(oop obj) {
  assert(obj->klass()->name()->equals(TYPE_NAME), "should be");
  Expression *exp;
  if (obj->is_symbolic()) {
    SymInstance *sym_inst =
        GlobalSymbolicSession::heap()->get_sym_inst(obj->get_sym_rid());
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
    Expression *exp = new MethodReturnSymbolExp(handle);
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
      Expression *exp = new MethodReturnSymbolExp(handle);
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

namespace {

// One JDK box cache: the holder class, its static `cache` array, and the
// value its first entry boxes.  Resolved on first ask and kept: the classes
// are the bootstrap loader's and never unload.
struct BoxCache {
  const char *holder;
  const char *signature;
  jlong low;
  Klass *klass;
  int offset;
};

BoxCache BOX_CACHES[] = {
  { "java/lang/Integer$IntegerCache", "[Ljava/lang/Integer;", -128, NULL, -1 },
  { "java/lang/Long$LongCache", "[Ljava/lang/Long;", -128, NULL, -1 },
  { "java/lang/Short$ShortCache", "[Ljava/lang/Short;", -128, NULL, -1 },
  { "java/lang/Byte$ByteCache", "[Ljava/lang/Byte;", -128, NULL, -1 },
  { "java/lang/Character$CharacterCache", "[Ljava/lang/Character;", 0, NULL,
    -1 },
};

BoxCache *cache_of(BasicType type) {
  switch (type) {
    case T_INT:   return &BOX_CACHES[0];
    case T_LONG:  return &BOX_CACHES[1];
    case T_SHORT: return &BOX_CACHES[2];
    case T_BYTE:  return &BOX_CACHES[3];
    case T_CHAR:  return &BOX_CACHES[4];
    default:      return NULL;
  }
}

// The static field `name` of `klass` holding `signature`, or -1.
int static_offset(Klass *klass, const char *name, const char *signature) {
  if (klass == NULL || !klass->oop_is_instance()) return -1;
  // Probed, not created: a probe takes no reference, so none is released.
  Symbol *field_name = SymbolTable::probe(name, (int) strlen(name));
  Symbol *field_signature =
      SymbolTable::probe(signature, (int) strlen(signature));
  if (field_name == NULL || field_signature == NULL) return -1;
  fieldDescriptor fd;
  if (!InstanceKlass::cast(klass)->find_local_field(field_name,
                                                     field_signature, &fd)
      || !fd.is_static()) {
    return -1;
  }
  return fd.offset();
}

// A cache's array of entries, or NULL while its holder class is not loaded
// (then no entry of it exists yet either).
objArrayOop cache_entries(BoxCache *cache) {
  if (cache->klass == NULL) {
    Symbol *name = SymbolTable::probe(cache->holder,
                                      (int) strlen(cache->holder));
    if (name == NULL) return NULL;
    Thread *thread = Thread::current();
    Klass *klass = SystemDictionary::find(name, Handle(), Handle(), thread);
    if (klass == NULL || thread->has_pending_exception()) return NULL;
    const int offset = static_offset(klass, "cache", cache->signature);
    if (offset < 0) return NULL;
    cache->offset = offset;
    OrderAccess::release_store_ptr(&cache->klass, klass);
  }
  oop entries = cache->klass->java_mirror()->obj_field(cache->offset);
  return entries == NULL || !entries->is_objArray() ? (objArrayOop) NULL
                                                    : objArrayOop(entries);
}

bool cached_box(oop box, BasicType type, jlong value) {
  BoxCache *cache = cache_of(type);
  objArrayOop array = cache == NULL ? (objArrayOop) NULL
                                    : cache_entries(cache);
  if (array == NULL) return false;
  const jlong index = value - cache->low;
  return index >= 0 && index < array->length()
      && array->obj_at((int) index) == box;
}

// One of the caches' own arrays: an element minted there is every valueOf's.
bool cache_array(oop array) {
  for (size_t index = 0; index < sizeof(BOX_CACHES) / sizeof(BOX_CACHES[0]);
       ++index) {
    if (cache_entries(&BOX_CACHES[index]) == array) return true;
  }
  return false;
}

bool shared_boolean(oop box) {
  static int true_offset = -1;
  static int false_offset = -1;
  Klass *klass = SystemDictionary::Boolean_klass();
  if (true_offset < 0) {
    true_offset = static_offset(klass, "TRUE", "Ljava/lang/Boolean;");
    false_offset = static_offset(klass, "FALSE", "Ljava/lang/Boolean;");
    if (true_offset < 0 || false_offset < 0) return false;
  }
  oop mirror = klass->java_mirror();
  return mirror->obj_field(true_offset) == box
      || mirror->obj_field(false_offset) == box;
}

// An enum constant: its class is ACC_ENUM, or (a constant with a body) a
// subclass of one.  Every `switch` and `==` in the JVM reads the constant.
bool enum_constant(oop obj) {
  for (Klass *klass = obj->klass(); klass != NULL; klass = klass->super()) {
    if ((klass->access_flags().get_flags() & JVM_ACC_ENUM) != 0) return true;
  }
  return false;
}

} // anonymous namespace

bool jvm_shared_object(oop obj) {
  if (obj == NULL) return false;
  if (obj->is_array()) return cache_array(obj);
  if (obj->klass() == SystemDictionary::String_klass()) {
    return OopUtils::is_java_string_interned(obj);
  }
  jvalue value;
  const BasicType type = java_lang_boxing_object::get_value(obj, &value);
  switch (type) {
    case T_BOOLEAN: return shared_boolean(obj);
    case T_BYTE:    return cached_box(obj, type, value.b);
    case T_CHAR:    return cached_box(obj, type, value.c);
    case T_SHORT:   return cached_box(obj, type, value.s);
    case T_INT:     return cached_box(obj, type, value.i);
    case T_LONG:    return cached_box(obj, type, value.j);
    case T_ILLEGAL: return enum_constant(obj);
    default:        return false;
  }
}

template<class T>
void
SymPrimitive<T>::set_symbolic_field(oop obj, Symbol *fld_name, Symbol *fld_tp_sig, MethodSymbolizerHandle &handle) {
  // A shared box keeps no expression: valueOf's value travels on the result
  // slot (MethodSymbolizer::finish_method), which is where an unboxing reads
  // it back.  Boolean.valueOf of a symbolic flag used to mark Boolean.TRUE for
  // the whole JVM.
  if (jvm_shared_object(obj)) return;
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

// Java's decimal rendering of a Byte, Short, Integer or Long, and its
// "true"/"false" of a Boolean: the holder's static toString of its own
// primitive, or the instance toString().  All of them are one `toString` op
// of the value.  A radix, a hexadecimal, a char or a floating rendering is
// none of these.
static bool is_decimal_or_boolean_rendering(MethodSymbolizerHandle &handle) {
    if (handle.get_callee_name() != "toString") return false;
    const std::string &holder = handle.get_callee_holder_name();
    const char *own = NULL;
    if (holder == SymPrimitive<jint>::TYPE_NAME) {
      own = "(I)Ljava/lang/String;";
    } else if (holder == SymPrimitive<jlong>::TYPE_NAME) {
      own = "(J)Ljava/lang/String;";
    } else if (holder == SymPrimitive<jshort>::TYPE_NAME) {
      own = "(S)Ljava/lang/String;";
    } else if (holder == SymPrimitive<jbyte>::TYPE_NAME) {
      own = "(B)Ljava/lang/String;";
    } else if (holder == SymPrimitive<jboolean>::TYPE_NAME) {
      own = "(Z)Ljava/lang/String;";
    } else {
      return false;
    }

    ResourceMark rm;
    const char *signature =
        handle.get_callee_method()->signature()->as_C_string();
    if (handle.get_callee_method()->is_static()) {
      return strcmp(signature, own) == 0;
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
        if (is_decimal_or_boolean_rendering(handle)) {
          // One provenance expression, the value (the argument, or the
          // receiver's value for the instance form), rendered the one way
          // COMPOSE lowers by the value's sort.
          guarantee(params.size() == 1,
                    "a decimal or boolean rendering has one parameter");
          string_exp = OpStrExpression::to_string(params[0]);
        } else {
          // Keep every receiver/argument and the exact holder+descriptor.  A
          // downstream encoder must reject this operation unless it adds and
          // validates the corresponding Java conversion semantics.  In
          // particular, radix and hexadecimal conversions must never be
          // mistaken for a decimal rendering.
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
