#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicAtomic.hpp"

#include "classfile/vmSymbols.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/fieldAccessExpression.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/unsafeAccess.hpp"
#include "runtime/fieldDescriptor.hpp"

namespace {

const char *ATOMIC_INTEGER = "java/util/concurrent/atomic/AtomicInteger";
const char *ATOMIC_LONG = "java/util/concurrent/atomic/AtomicLong";

struct AtomicOperation {
  BasicType type;
  bool returns_old_value;
  bool takes_delta;
  // compareAndSet / weakCompareAndSet.  Modeled by its observed arm only; see
  // finish_method_helper.
  bool is_cas;
  // Where a CAS's `update` argument starts.  A long argument occupies two
  // local slots, so it starts one slot later on AtomicLong than on
  // AtomicInteger.
  int update_offset;
  SymbolicOp operation;

  AtomicOperation()
      : type(T_ILLEGAL), returns_old_value(false), takes_delta(false),
        is_cas(false), update_offset(0), operation(op_null) {}
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
  const std::string expected_cas = operation->type == T_INT ? "(II)Z" : "(JJ)Z";
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
  // weakCompareAndSet is the same instruction here as compareAndSet: both
  // delegate to one compare-and-swap, and a spurious failure would still be a
  // failure this run concretely observed.
  if ((name == "compareAndSet" || name == "weakCompareAndSet")
      && signature == expected_cas) {
    operation->is_cas = true;
    operation->update_offset = operation->type == T_INT ? 2 : 3;
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

/**
 * The atomic's pre-state for a field with no log: its shadow, or a stated
 * projection of it.  A tracked field's pre-state is instead the read the
 * compare-and-swap performs (UnsafeAccess), so it is never taken here.
 */
Expression *untracked_pre_state(oop receiver, BasicType type,
                                const fieldDescriptor &field,
                                SymInstance *instance) {
  Expression *value = instance->get(field.offset());
  if (value != NULL) return value;
  Expression *owner = instance->get_ref_exp();
  if (owner == NULL && receiver->is_symbolic()) {
    owner = instance->get_or_create_ref_exp(receiver);
  }
  if (owner == NULL) return NULL;
  ResourceMark rm;
  // Same evidence every other primitive field read states: the object this
  // pre-state was read from and the value it held.
  return new FieldAccessExpression(
      owner, receiver->klass()->name()->as_C_string(), field.offset(), type,
      std::string(), SharedFieldVersions::reference_expression(receiver),
      SharedFieldVersions::field_value(receiver, field.offset(), type));
}

Expression *unit_delta(BasicType type) {
  return type == T_INT
      ? static_cast<Expression *>(new ConExpression((jint)1))
      : static_cast<Expression *>(new ConExpression((jlong)1));
}

}  // namespace

/**
 * The linearization is the compare-and-swap the muted body performs
 * (Unsafe.getAndAddInt's loop, or compareAndSwapInt itself), and it is
 * versioned there, in one critical section with the concrete operation
 * (UnsafeAccess::end_cas).  This hook states what that operation means --
 * `new = old op delta`, or a CAS's expect and update -- as the thread's
 * intent; finish reads back what the operation resolved.  It used to resolve
 * the old value and publish the new one after the body, from the words the
 * call returned: two racing increments published out of order and each read
 * the other's word as an UNOBSERVED write, and a failed CAS re-read the heap
 * to decide what it had lost to.
 */
bool SymbolicAtomic::invoke_method_helper(MethodSymbolizerHandle &handle) {
  AtomicOperation operation;
  if (!decode_operation(handle, &operation)) return false;

  oop receiver = handle.get_param<oop>(0);
  fieldDescriptor value;
  if (!value_field(receiver, operation.type, &value)) return false;
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  if (instance == NULL) return false;
  SharedFieldVersions::Location location(
      instance->get_sym_rid(), value.offset(),
      SharedFieldVersions::LOC_INSTANCE_FIELD);
  Expression *prior = SharedFieldVersions::is_tracked(location)
      ? NULL : untracked_pre_state(receiver, operation.type, value, instance);
  if (prior == NULL && !SharedFieldVersions::is_tracked(location)) {
    return false;
  }

  UnsafeAccess::clear_intent();
  UnsafeAccess::Intent *intent = UnsafeAccess::intent();
  intent->model = true;
  intent->owner = instance->get_sym_rid();
  intent->offset = value.offset();
  intent->prior = prior;
  if (prior != NULL) {
    const SharedFieldVersions::ConcreteBits held =
        SharedFieldVersions::field_bits(receiver, value.offset(),
                                        operation.type);
    intent->prior_stated = held.stated();
    intent->prior_bits = held.bits;
  }
  if (operation.is_cas) {
    intent->kind = UnsafeAccess::CAS;
    intent->expect = handle.get_primitive_exp(1, operation.type);
    intent->operand =
        handle.get_primitive_exp(operation.update_offset, operation.type);
  } else {
    intent->kind = UnsafeAccess::ADD;
    intent->op = operation.operation;
    intent->operand = operation.takes_delta
        ? handle.get_primitive_exp(1, operation.type)
        : unit_delta(operation.type);
  }
  return true;
}

Expression *SymbolicAtomic::finish_method_helper(
    MethodSymbolizerHandle &handle) {
  AtomicOperation operation;
  UnsafeAccess::Intent result = *UnsafeAccess::intent();
  UnsafeAccess::clear_intent();
  if (!decode_operation(handle, &operation) || !result.model || !result.done) {
    return NULL;
  }
  if (operation.is_cas) {
    // `old == expect`: the branch on the result selects its arm.
    return result.new_value;
  }
  // The field's shadow is the new value (UnsafeAccess::update_shadow).
  oop receiver = handle.get_param<oop>(0);
  fieldDescriptor value;
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  if (instance != NULL && value_field(receiver, operation.type, &value)) {
    instance->mark_field_written(value.offset());
  }
  return operation.returns_old_value ? result.old_value : result.new_value;
}

void SymbolicAtomic::init_register_class(
    MethodSymbolizer *method_symbolizer) {
  const char *const classes[] = { ATOMIC_INTEGER, ATOMIC_LONG, NULL };
  method_symbolizer->register_model(classes, invoke_method_helper,
                                    finish_method_helper);
}

#endif  // ENABLE_CONCOLIC
