#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicAtomic.hpp"

#include "classfile/vmSymbols.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/fieldAccessExpression.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "runtime/fieldDescriptor.hpp"

namespace {

const char *ATOMIC_INTEGER = "java/util/concurrent/atomic/AtomicInteger";
const char *ATOMIC_LONG = "java/util/concurrent/atomic/AtomicLong";

struct AtomicOperation {
  BasicType type;
  bool returns_old_value;
  bool takes_delta;
  SymbolicOp operation;

  AtomicOperation()
      : type(T_ILLEGAL), returns_old_value(false), takes_delta(false),
        operation(op_null) {}
};

bool decode_operation(MethodSymbolizerHandle &handle,
                      AtomicOperation *operation) {
  const std::string &holder = handle.get_callee_holder_name();
  if (holder == ATOMIC_INTEGER) {
    operation->type = T_INT;
  } else if (holder == ATOMIC_LONG) {
    operation->type = T_LONG;
  } else {
    return false;
  }

  Method *method = handle.get_callee_method();
  ResourceMark rm;
  const std::string signature(method->signature()->as_C_string());
  const std::string expected_no_arg = operation->type == T_INT ? "()I" : "()J";
  const std::string expected_delta = operation->type == T_INT ? "(I)I" : "(J)J";
  const std::string &name = handle.get_callee_name();

  if ((name == "getAndIncrement" || name == "getAndDecrement"
       || name == "incrementAndGet" || name == "decrementAndGet")
      && signature == expected_no_arg) {
    operation->returns_old_value = name.find("getAnd") == 0;
    operation->takes_delta = false;
    operation->operation = name.find("Decrement") != std::string::npos
        || name.find("decrement") != std::string::npos ? op_sub : op_add;
    return true;
  }
  if ((name == "getAndAdd" || name == "addAndGet")
      && signature == expected_delta) {
    operation->returns_old_value = name == "getAndAdd";
    operation->takes_delta = true;
    operation->operation = op_add;
    return true;
  }
  return false;
}

bool value_field(oop receiver, BasicType type, fieldDescriptor *field) {
  if (receiver == NULL || field == NULL) return false;
  Symbol *signature = type == T_INT
      ? vmSymbols::int_signature() : vmSymbols::long_signature();
  return receiver->klass()->find_field(
      vmSymbols::value_name(), signature, field) != NULL;
}

Expression *current_value(oop receiver, BasicType type,
                          fieldDescriptor *field,
                          SymInstance **receiver_instance) {
  if (!value_field(receiver, type, field)) return NULL;
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  if (instance == NULL) return NULL;
  *receiver_instance = instance;

  Expression *value = instance->get(field->offset());
  if (value != NULL) return value;

  Expression *owner = instance->get_ref_exp();
  if (owner == NULL && receiver->is_symbolic()) {
    owner = instance->get_or_create_ref_exp(receiver);
  }
  if (owner == NULL) return NULL;

  ResourceMark rm;
  return new FieldAccessExpression(
      owner, receiver->klass()->name()->as_C_string(), field->offset(), type);
}

Expression *unit_delta(BasicType type) {
  return type == T_INT
      ? static_cast<Expression *>(new ConExpression((jint)1))
      : static_cast<Expression *>(new ConExpression((jlong)1));
}

}  // namespace

bool SymbolicAtomic::invoke_method_helper(MethodSymbolizerHandle &handle) {
  AtomicOperation operation;
  if (!decode_operation(handle, &operation)) return false;

  oop receiver = handle.get_param<oop>(0);
  fieldDescriptor value;
  SymInstance *receiver_instance = NULL;
  Expression *old_value = current_value(
      receiver, operation.type, &value, &receiver_instance);
  if (old_value == NULL || receiver_instance == NULL) return false;

  Expression *delta = operation.takes_delta
      ? handle.get_primitive_exp(1, operation.type)
      : unit_delta(operation.type);
  if (delta == NULL) return false;

  // The concrete Atomic method still executes.  These two expressions are
  // the pre-state and operand used to rebuild its symbolic linearization at
  // normal return, while ordinary propagation is paused inside Unsafe.
  handle.get_param_list().push_back(old_value);
  handle.get_param_list().push_back(delta);
  return true;
}

Expression *SymbolicAtomic::finish_method_helper(
    MethodSymbolizerHandle &handle) {
  AtomicOperation operation;
  if (!decode_operation(handle, &operation)
      || handle.get_param_list().size() != 2) {
    return NULL;
  }

  oop receiver = handle.get_param<oop>(0);
  fieldDescriptor value;
  if (!value_field(receiver, operation.type, &value)) return NULL;
  SymInstance *receiver_instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  if (receiver_instance == NULL) return NULL;

  Expression *old_value = handle.get_param_list()[0];
  Expression *delta = handle.get_param_list()[1];
  Expression *new_value = new OpSymExpression(
      old_value, delta, operation.operation);
  // MethodSymbolizerHandle owns only freshly-created zero-ref parameters;
  // expressions already owned by an object shadow or caller stack are
  // borrowed.  Keep the new tree alive across set_sym_exp releasing the old
  // field shadow, since that old expression is one of the new tree's leaves.
  new_value->inc_ref();
  receiver_instance->mark_field_written(value.offset());
  receiver_instance->set_sym_exp(value.offset(), new_value);
  Expression::gc(new_value);
  return operation.returns_old_value ? old_value : new_value;
}

void SymbolicAtomic::init_register_class(
    MethodSymbolizer *method_symbolizer) {
  method_symbolizer->add_invoke_helper_methods(
      ATOMIC_INTEGER, invoke_method_helper);
  method_symbolizer->add_finish_helper_methods(
      ATOMIC_INTEGER, finish_method_helper);
  method_symbolizer->add_invoke_helper_methods(
      ATOMIC_LONG, invoke_method_helper);
  method_symbolizer->add_finish_helper_methods(
      ATOMIC_LONG, finish_method_helper);
}

#endif  // ENABLE_CONCOLIC
