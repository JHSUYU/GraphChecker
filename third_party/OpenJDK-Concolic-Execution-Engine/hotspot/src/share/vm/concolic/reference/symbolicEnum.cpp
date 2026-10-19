#ifdef ENABLE_CONCOLIC

#include "classfile/javaClasses.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/methodExpression.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/methodSymbolizer.hpp"
#include "concolic/reference/symbolicEnum.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "memory/universe.hpp"
#include "oops/fieldStreams.hpp"
#include "oops/objArrayOop.hpp"
#include "oops/typeArrayOop.hpp"
#include "prims/jvm.h"

#include <string.h>

namespace {

const char *const ENUM = "java/lang/Enum";

// A constant valueOf named, of its class, or its ordinal: the call it
// states.
class EnumExpression : public MethodExpression {
public:
  EnumExpression(const std::string &klass, const char *method,
                 exp_list_t &arguments, Expression *result)
      : MethodExpression(ENUM, method, arguments, result), _class(klass) {}
  virtual const char *enum_constant_class() {
    return _class.empty() ? NULL : _class.c_str();
  }
  virtual bool is_enum_ordinal() { return _class.empty(); }
  virtual bool is_enum_value_of() { return !_class.empty(); }

private:
  // The constant's class (valueOf's), or empty for an ordinal.
  std::string _class;
};

// A constant the program held, by its name: the name of a constant of its
// class.  Stored into a tracked location, it names what a read of the
// location observed, so a compare of that read with a constant is a compare
// of names (SymEnum::compare), as a constant valueOf named is.
class EnumConstantName : public ConStringSymbolExp {
public:
  EnumConstantName(const std::string &name, const std::string &klass)
      : ConStringSymbolExp(name), _class(klass) {}
  virtual const char *enum_constant_class() { return _class.c_str(); }

private:
  std::string _class;
};

// The enum class `klass` is, or that a constant's own body subclasses: the
// class directly under java.lang.Enum; NULL for any other.
InstanceKlass *enum_class(Klass *klass) {
  for (Klass *current = klass;
       current != NULL && current->oop_is_instance();
       current = current->super()) {
    Klass *super = current->super();
    if (super != NULL && super->name()->equals(ENUM, (int) strlen(ENUM))) {
      return InstanceKlass::cast(current);
    }
  }
  return NULL;
}

std::string class_name(InstanceKlass *klass) {
  ResourceMark rm;
  return std::string(klass->name()->as_C_string());
}

// A constant's name (Enum.name).
std::string name_of(oop constant) {
  oop name = OopUtils::obj_field_by_name(constant, "name",
                                         "Ljava/lang/String;");
  if (name == NULL) return std::string();
  ResourceMark rm;
  return std::string(java_lang_String::as_utf8_string(name));
}

// A constant's ordinal (Enum.ordinal), or -1.
jint ordinal_of(oop constant) {
  fieldDescriptor ordinal;
  return OopUtils::get_fd_by_name(constant, "ordinal", "I", ordinal) == NULL
      ? -1 : constant->int_field(ordinal.offset());
}

// The class's constant names in ordinal order, from its enum constant
// fields (ACC_ENUM; no other static field of its type is one); false where
// it states none, or a gap.
bool constants(InstanceKlass *klass, exp_list_t *names) {
  std::vector<std::string> named;
  for (JavaFieldStream fields(klass); !fields.done(); fields.next()) {
    if (!fields.access_flags().is_static()
        || (fields.access_flags().as_int() & JVM_ACC_ENUM) == 0) {
      continue;
    }
    oop constant = klass->java_mirror()->obj_field(fields.offset());
    const jint ordinal = constant == NULL ? -1 : ordinal_of(constant);
    if (ordinal < 0) return false;
    if ((size_t) ordinal >= named.size()) named.resize(ordinal + 1);
    named[ordinal] = name_of(constant);
  }
  for (size_t index = 0; index < named.size(); ++index) {
    if (named[index].empty()) return false;
    names->push_back(new ConStringSymbolExp(named[index]));
  }
  return !named.empty();
}

// String equals of two names, `receiver` never null.
Expression *equal_names(Expression *receiver, Expression *argument) {
  exp_list_t names;
  names.push_back(receiver);
  names.push_back(argument);
  return new OpStrExpression("equals", names, false);
}

}  // namespace

void SymEnum::init_register_class(MethodSymbolizer *m_symbolizer) {
  static const char *const CLASSES[] = {ENUM, NULL};
  m_symbolizer->register_model(CLASSES, invoke_method_helper,
                               finish_method_helper);
}

bool SymEnum::invoke_method_helper(MethodSymbolizerHandle &handle) {
  Method *callee = handle.get_callee_method();
  if (callee == NULL) return false;
  const std::string &method = handle.get_callee_name();
  const int first = handle.get_caller_stack_begin_offset();
  bool taken;
  if (callee->is_static()) {
    // valueOf(Class, String), its name symbolic.
    taken = method == "valueOf" && callee->size_of_parameters() == 2
        && ConcolicMngr::ctx->find_stack_slot(first + 1) != NULL;
  } else {
    Expression *self = ConcolicMngr::ctx->find_stack_slot(first);
    taken = (method == "name" || method == "toString" || method == "ordinal")
        && self != NULL && self->enum_constant_class() != NULL;
  }
  if (taken) handle.general_prepare_param();
  return taken;
}

Expression *SymEnum::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  exp_list_t &params = handle.get_param_list();
  exp_list_t arguments;
  if (method == "valueOf") {
    oop constant = handle.get_result<oop>(T_OBJECT);
    InstanceKlass *klass =
        constant == NULL ? NULL : enum_class(constant->klass());
    if (klass == NULL || params.size() != 2 || params[1] == NULL) {
      return NULL;
    }
    const std::string named = class_name(klass);
    arguments.push_back(new ConStringSymbolExp(named));
    arguments.push_back(params[1]);
    if (!constants(klass, &arguments)) return NULL;
    return new EnumExpression(named, "valueOf", arguments,
                              new ConStringSymbolExp(name_of(constant)));
  }
  Expression *self = params.empty() ? NULL : params[0];
  if (self == NULL) return NULL;
  // name(), Enum.toString(): the name itself.
  if (method != "ordinal") return self;
  oop constant = handle.get_param<oop>(0);
  InstanceKlass *klass = enum_class(constant->klass());
  arguments.push_back(self);
  if (klass == NULL || !constants(klass, &arguments)) return NULL;
  return new EnumExpression(std::string(), "ordinal", arguments,
                            new ConExpression(ordinal_of(constant)));
}

Expression *SymEnum::constant_name(oop value) {
  InstanceKlass *klass = value == NULL ? NULL : enum_class(value->klass());
  return klass == NULL ? NULL
      : new EnumConstantName(name_of(value), class_name(klass));
}

Expression *SymEnum::compare(Expression *left, oop left_obj,
                             Expression *right, oop right_obj, SymbolicOp op,
                             bool outcome) {
  const char *left_class = left == NULL ? NULL : left->enum_constant_class();
  const char *right_class =
      right == NULL ? NULL : right->enum_constant_class();
  if (left_class == NULL && right_class == NULL) {
    return compare_with_constant(left, left_obj, right, right_obj, op,
                                 outcome);
  }
  const bool named_left = left_class != NULL;
  Expression *named = named_left ? left : right;
  const char *named_class = named_left ? left_class : right_class;
  Expression *other = named_left ? right : left;
  const char *other_class = named_left ? right_class : left_class;
  oop other_obj = named_left ? right_obj : left_obj;
  if (other != NULL && other_class == NULL && !named->is_enum_value_of()) {
    // A read of a name compared with a value of its own expression: the
    // reference compare over both (CONCOLIC_OPC_REF_CMP).
    return NULL;
  }
  if (other_class == NULL && other_obj == NULL) {
    // A read of a name may be null in another world: a reference test.
    if (other != NULL) {
      ConcolicMngr::ctx->note_model_gap("ENUM_OPERAND_PINNED");
    }
    return new OpSymExpression(named, SymbolExpression::get(Sym_NULL), op,
                               outcome);
  }
  Expression *equal;
  if (other_class != NULL) {
    // Both named: within one class a compare of names, across two never
    // equal (the class decides).
    equal = strcmp(named_class, other_class) != 0
        ? static_cast<Expression *>(new ConExpression((jboolean) false))
        : equal_names(left, right);
  } else {
    InstanceKlass *klass = enum_class(other_obj->klass());
    if (klass == NULL || class_name(klass) != named_class) {
      if (other != NULL) {
        ConcolicMngr::ctx->note_model_gap("ENUM_OPERAND_PINNED");
      }
      equal = new ConExpression((jboolean) false);
    } else {
      // A constant of its class: the constant's name the receiver, the
      // name that may be null the argument.  An expression the constant's
      // operand carried of its own is replaced by that name: named.
      if (other != NULL) {
        ConcolicMngr::ctx->note_model_gap("ENUM_OPERAND_PINNED");
      }
      equal = equal_names(new ConStringSymbolExp(name_of(other_obj)),
                          named);
    }
  }
  return new OpSymExpression(equal, new ConExpression((jboolean) true), op,
                             outcome);
}

Expression *SymEnum::compare_with_constant(Expression *left, oop left_obj,
                                           Expression *right, oop right_obj,
                                           SymbolicOp op, bool outcome) {
  if ((left == NULL) == (right == NULL)) return NULL;
  Expression *valued = left != NULL ? left : right;
  oop valued_obj = left != NULL ? left_obj : right_obj;
  oop constant = left != NULL ? right_obj : left_obj;
  InstanceKlass *klass =
      constant == NULL ? NULL : enum_class(constant->klass());
  if (klass == NULL) return NULL;
  if (valued_obj != NULL && enum_class(valued_obj->klass()) != klass) {
    return NULL;
  }
  // A value of its own expression -- a read that observed null, a
  // container's answer, a call's return -- compared with a constant of its
  // class that carries none: the constant's name equals it, null in another
  // world never.
  return new OpSymExpression(equal_names(constant_name(constant), valued),
                             new ConExpression((jboolean) true), op,
                             outcome);
}

void SymEnum::loaded_static(Klass *holder, int offset, oop value) {
  if (value == NULL || value->klass() != Universe::intArrayKlassObj()
      || holder == NULL || !holder->oop_is_instance()) {
    return;
  }
  fieldDescriptor field;
  if (!InstanceKlass::cast(holder)->find_local_field_from_offset(offset,
          true, &field)) {
    return;
  }
  static const char SWITCH_MAP[] = "$SwitchMap$";
  static const char SWITCH_TABLE[] = "$SWITCH_TABLE$";
  if (field.name()->starts_with(SWITCH_MAP, (int) strlen(SWITCH_MAP))
      || field.name()->starts_with(SWITCH_TABLE,
                                   (int) strlen(SWITCH_TABLE))) {
    ConcolicMngr::ctx->note_switch_map(
        ConcolicMngr::ctx->name_reference(value));
  }
}

Expression *SymEnum::table_read(arrayOop array, Expression *index) {
  if (index == NULL || !index->is_enum_ordinal() || array->is_symbolic()
      || !ConcolicMngr::ctx->switch_map(array)
      || ConcolicMngr::ctx->find_container_state(array) != NULL) {
    return NULL;
  }
  if (array->length() > ConcolicMngr::initialSnapshotMaxEntries()) {
    // Past the snapshot bound the map is no stated snapshot: its READ is
    // the opaque one.
    ConcolicMngr::ctx->note_model_gap("ENUM_SWITCH_MAP_OVER_BOUND");
    return NULL;
  }
  typeArrayOop ints = (typeArrayOop) array;
  exp_list_t none;
  Expression *chain =
      new ContainerExpression("INDEXED", "SNAPSHOT_BASE", NULL, none);
  for (int at = 0; at < ints->length(); ++at) {
    exp_list_t element;
    element.push_back(new ConExpression(ints->int_at(at)));
    chain = new ContainerExpression("INDEXED", "APPEND", chain, element);
  }
  exp_list_t at;
  at.push_back(index);
  return new ContainerExpression("INDEXED", "READ", chain, at, T_INT,
                                 std::string(1, type2char(T_INT)));
}

#endif // ENABLE_CONCOLIC
