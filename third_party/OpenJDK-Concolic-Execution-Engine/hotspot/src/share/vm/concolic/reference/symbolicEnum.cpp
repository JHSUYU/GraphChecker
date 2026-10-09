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

#include <string.h>

namespace {

const char *const ENUM = "java/lang/Enum";

// A constant valueOf named, or its ordinal: the call it states.
class EnumExpression : public MethodExpression {
public:
  EnumExpression(bool ordinal, const char *method, exp_list_t &arguments,
                 Expression *result)
      : MethodExpression(ENUM, method, arguments, result),
        _ordinal(ordinal) {}
  virtual bool names_enum_constant() { return !_ordinal; }
  virtual bool is_enum_ordinal() { return _ordinal; }

private:
  bool _ordinal;
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

// A constant's name (Enum.name).
std::string name_of(oop constant) {
  oop name = OopUtils::obj_field_by_name(constant, "name",
                                         "Ljava/lang/String;");
  if (name == NULL) return std::string();
  ResourceMark rm;
  return std::string(java_lang_String::as_utf8_string(name));
}

// The class's constant names in ordinal order, from the static array of its
// own type javac keeps them in ($VALUES); false where it holds none.
bool constants(InstanceKlass *klass, exp_list_t *names) {
  ResourceMark rm;
  const std::string values =
      std::string("[L") + klass->name()->as_C_string() + ";";
  for (JavaFieldStream fields(klass); !fields.done(); fields.next()) {
    if (!fields.access_flags().is_static()
        || !fields.signature()->equals(values.c_str(), (int) values.size())) {
      continue;
    }
    objArrayOop all =
        (objArrayOop) klass->java_mirror()->obj_field(fields.offset());
    if (all == NULL) return false;
    for (int index = 0; index < all->length(); ++index) {
      names->push_back(new ConStringSymbolExp(name_of(all->obj_at(index))));
    }
    return true;
  }
  return false;
}

// What an operand compared with a named constant names: null for null, a
// constant its own name, NULL for anything else.
Expression *named(oop object) {
  if (object == NULL) return SymbolExpression::get(Sym_NULL);
  return enum_class(object->klass()) == NULL ? NULL
      : new ConStringSymbolExp(name_of(object));
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
        && self != NULL && self->names_enum_constant();
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
    {
      ResourceMark rm;
      arguments.push_back(
          new ConStringSymbolExp(std::string(klass->name()->as_C_string())));
    }
    arguments.push_back(params[1]);
    if (!constants(klass, &arguments)) return NULL;
    return new EnumExpression(false, "valueOf", arguments,
                              new ConStringSymbolExp(name_of(constant)));
  }
  Expression *self = params.empty() ? NULL : params[0];
  if (self == NULL) return NULL;
  // name(), Enum.toString(): the name itself.
  if (method != "ordinal") return self;
  oop constant = handle.get_param<oop>(0);
  InstanceKlass *klass = enum_class(constant->klass());
  fieldDescriptor ordinal;
  arguments.push_back(self);
  if (klass == NULL || !constants(klass, &arguments)
      || OopUtils::get_fd_by_name(constant, "ordinal", "I", ordinal)
             == NULL) {
    return NULL;
  }
  return new EnumExpression(true, "ordinal", arguments,
      new ConExpression((jint) constant->int_field(ordinal.offset())));
}

Expression *SymEnum::compare(Expression *left, oop left_obj,
                             Expression *right, oop right_obj) {
  const bool named_left = left != NULL && left->names_enum_constant();
  const bool named_right = right != NULL && right->names_enum_constant();
  if (!named_left && !named_right) return NULL;
  // A named operand is equals' receiver: never null.
  Expression *other = named_left && named_right ? right
      : named_left ? named(right_obj) : named(left_obj);
  if (other == NULL) return NULL;
  exp_list_t names;
  names.push_back(named_left ? left : right);
  names.push_back(other);
  return new OpStrExpression("equals", names, false);
}

Expression *SymEnum::table_read(arrayOop array, Expression *index) {
  if (index == NULL || !index->is_enum_ordinal() || array->is_symbolic()
      || array->klass() != Universe::intArrayKlassObj()
      || array->length() > ConcolicMngr::initialSnapshotMaxEntries()
      || ConcolicMngr::ctx->find_container_state(array) != NULL) {
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
