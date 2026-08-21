#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicAtomic.hpp"

#include "classfile/vmSymbols.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/eventLedger.hpp"
#include "concolic/exp/fieldAccessExpression.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/threadContext.hpp"
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
  SymbolicOp operation;

  AtomicOperation()
      : type(T_ILLEGAL), returns_old_value(false), takes_delta(false),
        is_cas(false), operation(op_null) {}
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

jlong concrete_value_bits(oop receiver, BasicType type, int offset) {
  return type == T_INT
      ? SharedFieldVersions::raw_bits((jint) receiver->int_field(offset))
      : SharedFieldVersions::raw_bits((jlong) receiver->long_field(offset));
}

/**
 * The atomic's pre-state, as an expression.
 *
 * When the value field is a selected carrier this goes through the ordinary
 * read-from resolver, so an RMW's read half obeys exactly the same provenance
 * rules as a plain read of the same field -- and, being a volatile access,
 * acquires the resolved writer's clock when the writer is proven.  When it is
 * not selected, the pre-existing behaviour is kept: the field shadow, or a
 * fresh field-access term when there is none.
 */
Expression *current_value(oop receiver, BasicType type,
                          fieldDescriptor *field,
                          SymInstance **receiver_instance) {
  if (!value_field(receiver, type, field)) return NULL;
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  if (instance == NULL) return NULL;
  *receiver_instance = instance;

  SharedFieldVersions::Location location(
      instance->get_sym_rid(), field->offset(),
      SharedFieldVersions::LOC_INSTANCE_FIELD);
  if (SharedFieldVersions::is_carrier(location)) {
    jlong bits = concrete_value_bits(receiver, type, field->offset());
    SharedFieldVersions::ReadResult resolved;
    if (SharedFieldVersions::resolve_read(
            location,
            SharedFieldVersions::primitive_fingerprint(type, bits), type,
            &resolved)
        && resolved.expression != NULL) {
      ConcolicMngr::recordVolatileRead(
          location.owner, field->offset(), resolved.writer_clock,
          resolved.resolution == SharedFieldVersions::RESOLVE_EXACT);
      return resolved.expression;
    }
  }

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

/**
 * Publishes the write half of one linearized atomic operation.
 *
 * The relation is already built by the caller (`new = old + delta`, or the
 * CAS's `update`); this is what makes it a version other threads' reads can
 * select, with the same evidence an ordinary store would carry.
 */
void publish_linearization(SymInstance *receiver_instance,
                           const fieldDescriptor &field, BasicType type,
                           oop receiver, Expression *new_value,
                           Expression *extra_guard, int event_kind,
                           const char *detail) {
  SharedFieldVersions::Location location(
      receiver_instance->get_sym_rid(), field.offset(),
      SharedFieldVersions::LOC_INSTANCE_FIELD);
  Expression *guard = ConcolicMngr::ctx->path_guard();
  if (extra_guard != NULL) {
    guard = guard == NULL
        ? extra_guard
        : (Expression *) new OpSymExpression(guard, extra_guard, op_land);
  }
  jlong bits = concrete_value_bits(receiver, type, field.offset());
  SharedFieldVersions::publish(
      location, new_value, guard,
      SharedFieldVersions::primitive_fingerprint(type, bits), true,
      SharedFieldVersions::VERSION_RMW);
  if (EventLedger::is_recording()) {
    ConcolicMngr::ctx->tick_clock();
    EventLedger::record(event_kind, location.owner, field.offset(), detail);
  }
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

  if (operation.is_cas) {
    // A long argument occupies two local slots, so the second argument starts
    // one slot later on AtomicLong than on AtomicInteger.
    const int update_offset = operation.type == T_INT ? 2 : 3;
    Expression *expect = handle.get_primitive_exp(1, operation.type);
    Expression *update =
        handle.get_primitive_exp(update_offset, operation.type);
    if (expect == NULL || update == NULL) return false;
    handle.get_param_list().push_back(old_value);
    handle.get_param_list().push_back(expect);
    handle.get_param_list().push_back(update);
    return true;
  }

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
  if (!decode_operation(handle, &operation)) return NULL;

  oop receiver = handle.get_param<oop>(0);
  fieldDescriptor value;
  if (!value_field(receiver, operation.type, &value)) return NULL;
  SymInstance *receiver_instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  if (receiver_instance == NULL) return NULL;

  if (operation.is_cas) {
    if (handle.get_param_list().size() != 3) return NULL;
    Expression *old_value = handle.get_param_list()[0];
    Expression *expect = handle.get_param_list()[1];
    Expression *update = handle.get_param_list()[2];
    // The relation the boolean result denotes.  It is the same relation on
    // both arms, which is why it can be returned unconditionally.
    Expression *matched = new OpSymExpression(old_value, expect, op_eq, true);

    const bool succeeded = handle.get_result<jint>(T_BOOLEAN) != 0;
    if (succeeded) {
      // Only the arm this run actually took is published.  The failing arm is
      // not modeled at all: writing a version for a store that did not happen
      // would put a value into the read-from choice of every later reader of
      // this location on the strength of a branch nothing executed.  The arm
      // that did happen carries `old == expect` as part of its guard, so a
      // solver cannot select this writer while denying the comparison that
      // let it win.
      receiver_instance->mark_field_written(value.offset());
      receiver_instance->set_sym_exp(value.offset(), update);
      publish_linearization(
          receiver_instance, value, operation.type, receiver, update, matched,
          EventLedger::EVENT_ATOMIC_CAS, "OBSERVED_SUCCESS new = update");
    } else if (EventLedger::is_recording()) {
      // Nothing was stored, so there is nothing to version.  The failure is
      // still recorded: it is the observed arm, and a consumer that sees only
      // successes cannot tell a CAS that never ran from one that lost.
      ConcolicMngr::ctx->tick_clock();
      EventLedger::record(
          EventLedger::EVENT_ATOMIC_CAS, receiver_instance->get_sym_rid(),
          value.offset(), "OBSERVED_FAILURE old != expect");
    }
    return matched;
  }

  if (handle.get_param_list().size() != 2) return NULL;
  Expression *old_value = handle.get_param_list()[0];
  Expression *delta = handle.get_param_list()[1];
  Expression *new_value = new OpSymExpression(
      old_value, delta, operation.operation);
  receiver_instance->mark_field_written(value.offset());
  receiver_instance->set_sym_exp(value.offset(), new_value);
  publish_linearization(
      receiver_instance, value, operation.type, receiver, new_value, NULL,
      EventLedger::EVENT_ATOMIC_RMW,
      operation.operation == op_sub ? "new = old - delta"
                                    : "new = old + delta");
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
