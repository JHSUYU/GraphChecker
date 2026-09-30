#ifdef ENABLE_CONCOLIC

#include "concolic/unsafeAccess.hpp"

#include "classfile/systemDictionary.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/threadContext.hpp"
#include "oops/arrayOop.hpp"
#include "oops/instanceMirrorKlass.hpp"
#include "oops/typeArrayKlass.hpp"
#include "memory/resourceArea.hpp"

#include <string.h>

namespace {

// POD, so it can live in thread-local storage.
__thread UnsafeAccess::Intent _intent;

// The location an Unsafe (holder, offset) names, as the bytecode hooks name
// it: an instance field by its owner's identity, a static field by its
// mirror's, an array element by its index.  An object with no session
// identity names no location: nothing tracked can live in it.
bool locate(oop holder, jlong offset, BasicType type,
            SharedFieldVersions::Location *location) {
  if (holder == NULL || !holder->is_symbolic() || offset < 0) return false;
  if (holder->is_array()) {
    const BasicType element = holder->is_objArray() ? T_OBJECT
        : TypeArrayKlass::cast(holder->klass())->element_type();
    const jlong base = arrayOopDesc::base_offset_in_bytes(element);
    const jlong size = holder->is_objArray()
        ? (jlong) heapOopSize : (jlong) type2aelembytes(element);
    if (offset < base || (offset - base) % size != 0) return false;
    const jlong index = (offset - base) / size;
    if (index >= ((arrayOop) holder)->length()) return false;
    *location = SharedFieldVersions::Location(
        holder->get_sym_rid(), (int) index,
        SharedFieldVersions::LOC_ARRAY_ELEMENT);
    return true;
  }
  const bool mirror = holder->klass() == SystemDictionary::Class_klass()
      && offset >= InstanceMirrorKlass::offset_of_static_fields();
  *location = SharedFieldVersions::Location(
      holder->get_sym_rid(), (int) offset,
      mirror ? SharedFieldVersions::LOC_STATIC_FIELD
             : SharedFieldVersions::LOC_INSTANCE_FIELD);
  return true;
}

// The constant a concrete word stands for, else a reference's identity.
Expression *concrete(const SharedFieldVersions::ConcreteBits &word,
                     oop reference) {
  return word.stated()
      ? SharedFieldVersions::primitive_expression(word.type, word.bits)
      : SharedFieldVersions::reference_expression(reference);
}

}  // namespace

UnsafeAccess::Intent *UnsafeAccess::intent() { return &_intent; }

void UnsafeAccess::clear_intent() { memset(&_intent, 0, sizeof(_intent)); }

void UnsafeAccess::capture(MethodSymbolizerHandle &handle) {
  // An ordinary caller's Unsafe write: its operands' shadows are on the
  // caller's operand stack now, and the muted call is about to clear them.
  // Locals: this, o, offset (two words), then the operands.
  Method *callee = handle.get_callee_method();
  if (callee == NULL || callee->is_static() || _intent.kind != NONE) return;
  const std::string &name = handle.get_callee_name();
  int kind = NONE;
  if (name.compare(0, 3, "put") == 0) {
    kind = PUT;
  } else if (name.compare(0, 13, "compareAndSwap") == 0) {
    kind = CAS;
  } else if (name.compare(0, 9, "getAndAdd") == 0) {
    kind = ADD;
  } else if (name.compare(0, 9, "getAndSet") == 0) {
    kind = SET;
  } else {
    return;
  }
  ResourceMark rm;
  SignatureStream stream(callee->signature());
  // (Ljava/lang/Object;J...): anything else (an address form) is off-heap.
  if (stream.at_return_type() || stream.type() != T_OBJECT) return;
  stream.next();
  if (stream.at_return_type() || stream.type() != T_LONG) return;
  stream.next();
  if (stream.at_return_type()) return;
  const BasicType operand_type = stream.type();
  oop holder = handle.get_param<oop>(1);
  if (holder == NULL || !holder->is_symbolic()) return;
  const int begin = handle.get_caller_stack_begin_offset();
  // The shadow of the operand at local `at`, anchored at its last word.
  const int first = 4;
  const int width = type2size[operand_type];
  Expression *first_operand = ConcolicMngr::ctx->find_stack_slot(
      begin + first + width - 1);
  Expression *second_operand = kind == CAS
      ? ConcolicMngr::ctx->find_stack_slot(begin + first + 2 * width - 1)
      : NULL;
  clear_intent();
  _intent.kind = kind;
  _intent.owner = holder->get_sym_rid();
  _intent.offset = handle.get_param<jlong>(3);
  _intent.op = op_add;
  if (kind == CAS) {
    _intent.expect = first_operand;
    _intent.operand = second_operand;
  } else {
    _intent.operand = first_operand;
  }
}

void UnsafeAccess::release_capture() {
  if (_intent.kind != NONE && !_intent.model) clear_intent();
}

void UnsafeAccess::begin(Access *access, oop holder, jlong offset,
                         BasicType type) {
  access->active = false;
  access->intent = NULL;
  if (!GlobalSymbolicSession::is_open()) return;
  const bool intended = _intent.kind != NONE && !_intent.done;
  if (!intended && !SharedFieldVersions::has_carriers()) return;
  if (!locate(holder, offset, type, &access->location)) return;
  if (intended && _intent.owner == access->location.owner
      && _intent.offset == offset) {
    access->intent = &_intent;
  }
  // A reference cell states its box's word (a wrapper field's value);
  // anything else it holds states none.
  access->cell = SharedFieldVersions::Cell(holder, type, type == T_OBJECT);
  access->path_guard = ConcolicMngr::ctx == NULL
      ? NULL : ConcolicMngr::ctx->path_guard();
  SharedFieldVersions::prepare_read(&access->plan);
  SharedFieldVersions::lock(access->location);
  access->active = true;
}

void UnsafeAccess::end_put(Access *access,
                           const SharedFieldVersions::ConcreteBits &stored,
                           oop stored_reference) {
  if (!access->active) return;
  Intent *intent = access->intent;
  Expression *value = intent != NULL
      && (intent->kind == PUT || intent->kind == SET)
      ? intent->operand : NULL;
  SharedFieldVersions::Store store;
  SharedFieldVersions::prepare_store(&store, access->location, value,
                                     access->path_guard, value != NULL,
                                     value != NULL);
  SharedFieldVersions::begin_store_locked(&store, access->cell);
  const jlong version = SharedFieldVersions::end_store_locked(
      &store, stored, stored_reference);
  // A context whose operand no call boundary could capture wrote this: the
  // word is right, what it was a function of is unknown.
  if (version > 0 && intent == NULL && ConcolicMngr::ctx != NULL) {
    SharedFieldVersions::mark_writer_set_incomplete_locked(
        access->location, "UNSAFE_WRITE_UNCAPTURED");
  }
  SharedFieldVersions::unlock(access->location);
  if (intent != NULL) {
    intent->done = true;
    intent->succeeded = true;
    intent->new_value = value;
  }
  update_shadow(*access, value, stored, stored_reference);
}

void UnsafeAccess::end_cas(Access *access, bool succeeded,
                           const SharedFieldVersions::ConcreteBits &witnessed,
                           oop witnessed_reference,
                           const SharedFieldVersions::ConcreteBits &stored,
                           oop stored_reference) {
  if (!access->active) return;
  Intent *intent = access->intent;
  // A retry of a loop (getAndAdd, getAndSet) that lost the race decides
  // nothing: the loop reads again and tries again.
  if (!succeeded && (intent == NULL || intent->kind != CAS)) {
    SharedFieldVersions::unlock(access->location);
    return;
  }
  // The read the compare made, of the word it compared -- never a re-read of
  // the heap after the fact.
  Expression *old_value = NULL;
  if (intent != NULL) {
    const std::string type_name(1, type2char(
        witnessed.stated() && !witnessed.is_null() ? witnessed.type
                                                   : T_OBJECT));
    if (SharedFieldVersions::plan_read_locked(access->location, witnessed,
                                              &access->plan)) {
      old_value = SharedFieldVersions::scalar_read(
          access->plan, access->location, type_name, witnessed,
          witnessed_reference);
    } else {
      old_value = intent->prior;
    }
  }

  Expression *value = NULL;
  Expression *guard = access->path_guard;
  int kind = SharedFieldVersions::VERSION_WRITE;
  if (intent != NULL) {
    if (intent->kind == ADD) {
      if (old_value != NULL || intent->operand != NULL) {
        value = new OpSymExpression(
            old_value != NULL ? old_value : concrete(witnessed, NULL),
            intent->operand != NULL ? intent->operand : concrete(
                SharedFieldVersions::ConcreteBits(
                    witnessed.type,
                    stored.bits - witnessed.bits), NULL),
            (SymbolicOp) intent->op);
      }
      kind = SharedFieldVersions::VERSION_RMW;
    } else if (intent->kind == CAS) {
      value = intent->operand;
      kind = SharedFieldVersions::VERSION_RMW;
      if (old_value != NULL || intent->expect != NULL) {
        // The comparison that let the store happen is part of its guard: a
        // solver cannot select this writer while denying it.
        Expression *matched = new OpSymExpression(
            old_value != NULL ? old_value
                              : concrete(witnessed, witnessed_reference),
            intent->expect != NULL
                ? intent->expect : concrete(witnessed, witnessed_reference),
            op_eq, true);
        if (intent->model) intent->new_value = matched;
        if (succeeded) {
          guard = guard == NULL ? matched
              : (Expression *) new OpSymExpression(guard, matched, op_land);
        }
      }
    } else {
      value = intent->operand;
    }
  }

  jlong version = 0;
  if (succeeded) {
    SharedFieldVersions::Store store;
    SharedFieldVersions::prepare_store(&store, access->location, value,
                                       guard, value != NULL, value != NULL,
                                       kind);
    SharedFieldVersions::begin_store_locked(&store, access->cell);
    version = SharedFieldVersions::end_store_locked(&store, stored,
                                                    stored_reference);
    if (version > 0 && intent == NULL && ConcolicMngr::ctx != NULL) {
      SharedFieldVersions::mark_writer_set_incomplete_locked(
          access->location, "UNSAFE_WRITE_UNCAPTURED");
    }
  }
  SharedFieldVersions::unlock(access->location);
  if (intent != NULL) {
    intent->done = true;
    intent->succeeded = succeeded;
    intent->old_value = old_value;
    if (intent->kind != CAS || !intent->model) intent->new_value = value;
  }
  if (succeeded) update_shadow(*access, value, stored, stored_reference);
}

void UnsafeAccess::update_shadow(const Access &access, Expression *value,
                                 const SharedFieldVersions::ConcreteBits &stored,
                                 oop stored_reference) {
  // The shadow a bytecode store would have left, so an untracked read of it
  // is not the value this write replaced.  Session state, so a thread with
  // no context keeps it true too.
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  oop holder = access.cell.holder;
  if (heap == NULL || holder == NULL) return;
  if (access.location.kind == SharedFieldVersions::LOC_ARRAY_ELEMENT) {
    if (heap->find_container_state(holder) == NULL) return;
    heap->write_array_element((arrayOop) holder, access.location.slot,
                              value != NULL ? value
                                  : concrete(stored, stored_reference));
    return;
  }
  SymInstance *shadow = heap->find_sym_inst(holder);
  if (shadow == NULL) return;
  shadow->mark_field_written(access.location.slot);
  shadow->set_sym_exp(access.location.slot, value);
}

#endif // ENABLE_CONCOLIC
