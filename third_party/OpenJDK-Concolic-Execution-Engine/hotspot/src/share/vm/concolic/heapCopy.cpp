#ifdef ENABLE_CONCOLIC

#include "concolic/heapCopy.hpp"

#include "concolic/concolicMngr.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/threadContext.hpp"
#include "oops/objArrayKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "oops/typeArrayKlass.hpp"
#include "oops/typeArrayOop.hpp"
#include "oops/fieldStreams.hpp"
#include "runtime/fieldType.hpp"

#include <algorithm>

namespace {

BasicType element_type(arrayOop array) {
  return array->is_objArray() ? T_OBJECT
      : TypeArrayKlass::cast(array->klass())->element_type();
}

// What a load of `source[index]` returns, as the aload hook answers it: the
// value the recording decides, NULL for the concrete word, or a READ.
Expression *source_value(arrayOop source, SymArr *shadow, Expression *state,
                         int index, const SharedFieldVersions::ConcreteBits &word,
                         oop element) {
  Expression *value = NULL;
  if (ContainerSupport::recorded_element(source, shadow, state, NULL, index,
                                         &value)) {
    return value;
  }
  return ContainerSupport::element_read(
      shadow, state, new ConExpression((jint) index), element_type(source),
      word, element);
}

SharedFieldVersions::Location element_location(arrayOop array, int index) {
  return SharedFieldVersions::Location(
      array->get_sym_rid(), index, SharedFieldVersions::LOC_ARRAY_ELEMENT);
}

}  // namespace

void HeapCopy::before_array_copy(ArrayCopy *copy, arrayOop source,
                                 int source_position, arrayOop destination,
                                 int destination_position, int length) {
  copy->active = false;
  if (!GlobalSymbolicSession::is_open() || source == NULL
      || destination == NULL || length <= 0 || source_position < 0
      || destination_position < 0
      || source_position > source->length() - length
      || destination_position > destination->length() - length
      || source->is_objArray() != destination->is_objArray()
      || element_type(source) != element_type(destination)) {
    // copy_array refuses it before copying anything.
    return;
  }
  ThreadContext *ctx = ConcolicMngr::ctx;
  // A paused or muted thread stays silent, as its stores do; a thread
  // outside every region versions tracked elements, unattributed.
  if (ctx != NULL && !ConcolicMngr::can_do_concolic()) return;
  const bool propagates = ctx != NULL;
  const bool source_shadowed = propagates && source->is_symbolic();
  copy->shadowed = propagates && destination->is_symbolic();
  copy->tracked.clear();
  if (destination->is_symbolic()) {
    SharedFieldVersions::tracked_elements(
        destination->get_sym_rid(), destination_position,
        destination_position + length, &copy->tracked);
  }
  if (!source_shadowed && !copy->shadowed && copy->tracked.empty()) return;
  if (store_checked(source, destination)) {
    // Each element's store check runs inside the copy, and one that fails
    // throws part way -- allocating and running Java, which no held stripe
    // may span.  A copy that will fail names the destination instead of
    // describing it.  One that should pass still may not (another thread's
    // aastore can change the source under it), so it holds no stripe: its
    // tracked elements are named, not versioned.
    if (!assignable(source, source_position, destination, length)) {
      unmodeled(destination, destination_position, length,
                "ARRAYCOPY_FAILED");
      return;
    }
    for (size_t index = 0; index < copy->tracked.size(); ++index) {
      SharedFieldVersions::mark_writer_set_incomplete(
          element_location(destination, copy->tracked[index]),
          "ARRAYCOPY_STORE_CHECK");
    }
    copy->tracked.clear();
    if (!source_shadowed && !copy->shadowed) return;
  }

  const BasicType type = element_type(source);
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  SymArr *source_shadow =
      source_shadowed ? ctx->find_sym_array(source) : NULL;
  Expression *source_state = source_shadow == NULL
      ? NULL : ctx->container_state(source, "INDEXED");
  // The source range as it is before the copy: the ranges may overlap.
  // Every element when the destination's shadow is modeled, else only the
  // tracked ones (a copy past the bound keeps no per-element shadow).
  const bool whole = length <= ARRAYCOPY_MODEL_LIMIT;
  copy->values.assign(length, (Expression *) NULL);
  copy->words.assign(length, SharedFieldVersions::ConcreteBits());
  copy->identities.assign(length, 0);
  bool symbolic = false;
  for (int i = 0; i < length; ++i) {
    const int at = destination_position + i;
    if (!whole && !std::binary_search(copy->tracked.begin(),
                                      copy->tracked.end(), at)) {
      continue;
    }
    oop element = type == T_OBJECT
        ? objArrayOop(source)->obj_at(source_position + i) : (oop) NULL;
    copy->words[i] = type == T_OBJECT ? SharedFieldVersions::ConcreteBits()
        : SharedFieldVersions::element_bits(source, source_position + i);
    if (element != NULL) copy->identities[i] = heap->name_reference(element);
    if (source_state != NULL) {
      copy->values[i] = source_value(source, source_shadow, source_state,
                                     source_position + i, copy->words[i],
                                     element);
      symbolic = symbolic || copy->values[i] != NULL;
    }
  }
  if (!copy->shadowed && symbolic && whole) {
    // Symbolic values arrive in a concrete array: it takes a shadow, whose
    // elements are the heap's own under the writes it records.
    ctx->get_or_alloc_sym_array(destination, NULL, true);
    copy->shadowed = true;
  }
  copy->modeled = copy->shadowed && whole;
  copy->destination = Handle(Thread::current(), destination);
  copy->destination_position = destination_position;
  copy->length = length;
  copy->path_guard = ctx == NULL ? NULL : ctx->path_guard();
  copy->stripes.clear();
  for (size_t index = 0; index < copy->tracked.size(); ++index) {
    copy->stripes.push_back(SharedFieldVersions::stripe_of(
        element_location(destination, copy->tracked[index])));
  }
  std::sort(copy->stripes.begin(), copy->stripes.end());
  copy->stripes.erase(std::unique(copy->stripes.begin(), copy->stripes.end()),
                      copy->stripes.end());
  // The concrete copy and the tracked elements' versions are one critical
  // section, as a store and its version are.  A copy holding stripes cannot
  // throw: bounds and element types were checked, and it runs no store
  // check.
  SharedFieldVersions::lock_stripes(copy->stripes);
  // A log that began between the scan and the locks: versioned with the
  // rest when its stripe is held, else named once they are released.
  std::vector<int> now;
  SharedFieldVersions::tracked_elements(
      destination->get_sym_rid(), destination_position,
      destination_position + length, &now);
  if (now.size() != copy->tracked.size()) {
    std::vector<int> held;
    for (size_t index = 0; index < now.size(); ++index) {
      const int stripe = SharedFieldVersions::stripe_of(
          element_location(destination, now[index]));
      if (std::binary_search(copy->stripes.begin(), copy->stripes.end(),
                             stripe)) {
        held.push_back(now[index]);
      } else {
        copy->unheld.push_back(now[index]);
      }
    }
    copy->tracked.swap(held);
  }
  copy->active = true;
}

bool HeapCopy::store_checked(arrayOop source, arrayOop destination) {
  // ObjArrayKlass::do_copy's test for its unchecked path.
  return destination->is_objArray()
      && !ObjArrayKlass::cast(source->klass())->element_klass()->is_subtype_of(
             ObjArrayKlass::cast(destination->klass())->element_klass());
}

bool HeapCopy::assignable(arrayOop source, int source_position,
                          arrayOop destination, int length) {
  if (!store_checked(source, destination)) return true;
  Klass *element = ObjArrayKlass::cast(destination->klass())->element_klass();
  objArrayOop elements = objArrayOop(source);
  for (int i = 0; i < length; ++i) {
    oop value = elements->obj_at(source_position + i);
    if (value != NULL && !value->klass()->is_subtype_of(element)) {
      return false;
    }
  }
  return true;
}

void HeapCopy::unmodeled(arrayOop destination, int position, int length,
                         const char *reason) {
  if (!destination->is_symbolic()) return;
  std::vector<int> tracked;
  SharedFieldVersions::tracked_elements(destination->get_sym_rid(), position,
                                        position + length, &tracked);
  for (size_t index = 0; index < tracked.size(); ++index) {
    SharedFieldVersions::mark_writer_set_incomplete(
        element_location(destination, tracked[index]), reason);
  }
  if (ConcolicMngr::ctx != NULL) {
    ContainerSupport::mark_state_gap(destination, reason);
    ConcolicMngr::ctx->forget_container_state(destination);
  }
}

void HeapCopy::after_array_copy(ArrayCopy *copy, bool failed) {
  if (!copy->active) return;
  copy->active = false;
  arrayOop destination = (arrayOop) copy->destination();
  const BasicType type = element_type(destination);
  for (size_t index = 0; index < copy->tracked.size(); ++index) {
    const int at = copy->tracked[index];
    const SharedFieldVersions::Location location =
        element_location(destination, at);
    // A copy holding stripes ran no store check, so it did not fail.
    Expression *value = copy->values[at - copy->destination_position];
    SharedFieldVersions::Store store;
    SharedFieldVersions::prepare_store(&store, location, value,
                                       copy->path_guard, value != NULL,
                                       value != NULL);
    SharedFieldVersions::begin_store_locked(
        &store, SharedFieldVersions::Cell(destination, type));
    SharedFieldVersions::end_store_locked(
        &store, SharedFieldVersions::element_bits(destination, at),
        type == T_OBJECT ? objArrayOop(destination)->obj_at(at) : (oop) NULL);
  }
  SharedFieldVersions::unlock_stripes(copy->stripes);
  for (size_t index = 0; index < copy->unheld.size(); ++index) {
    SharedFieldVersions::mark_writer_set_incomplete(
        element_location(destination, copy->unheld[index]),
        "ARRAYCOPY_RACE");
  }

  ThreadContext *ctx = ConcolicMngr::ctx;
  if (ctx == NULL || !copy->shadowed) return;
  if (failed || !copy->modeled) {
    // The destination's state no longer describes the heap: named, and
    // dropped, so its next load reads the heap instead of a stale write.
    ContainerSupport::mark_state_gap(destination, failed
        ? "ARRAYCOPY_FAILED" : "ARRAYCOPY_BEYOND_MODEL_LIMIT");
    ctx->forget_container_state(destination);
    return;
  }
  for (int i = 0; i < copy->length; ++i) {
    const int at = copy->destination_position + i;
    Expression *value = copy->values[i];
    const bool symbolic = value != NULL;
    if (value == NULL) {
      value = type == T_OBJECT
          ? ContainerSupport::concrete_value(
                objArrayOop(destination)->obj_at(at))
          : SharedFieldVersions::primitive_expression(copy->words[i].type,
                                                      copy->words[i].bits);
    }
    ctx->write_array_element(
        destination, at, value,
        ElementWord(symbolic, type == T_OBJECT ? copy->identities[i]
                                               : copy->words[i].bits));
  }
}

void HeapCopy::cloned(oop original, oop clone) {
  if (!ConcolicMngr::can_do_concolic() || original == NULL || clone == NULL
      || !original->is_symbolic()) {
    return;
  }
  ThreadContext *ctx = ConcolicMngr::ctx;
  if (original->is_array()) {
    SymArr *shadow = ctx->find_sym_array(arrayOop(original));
    if (shadow == NULL) return;
    SymArr *copy = ctx->get_or_alloc_sym_array(
        arrayOop(clone), shadow->get_length_exp(), shadow->named());
    if (copy == NULL) return;
    if (shadow->has_semantic_expression()) {
      copy->set_ref_exp(shadow->get_ref_exp());
    }
    // The original's state is immutable, so the clone shares it: every
    // element a read of the clone asks is the element the original held
    // when it was copied.  Written, so a read of it is not pinned as an
    // untouched array's is.
    Expression *state = ctx->find_container_state(original);
    if (state != NULL) {
      ctx->set_container_state(clone, state);
      copy->store();
    }
    return;
  }
  SymInstance *shadow = ctx->find_sym_inst(original);
  if (shadow == NULL) return;
  SymInstance *copy = ctx->get_or_alloc_sym_inst(clone);
  if (copy == NULL) return;
  shadow->copy_fields_to(copy);
  if (!SharedFieldVersions::has_carriers()) return;
  // A tracked field's shadow may be stale -- its newest store came from a
  // thread outside every region, which versions without touching shadows --
  // so the copy takes the newest version's value when the clone holds what
  // it wrote (the word; a reference's shadow expression), and is concrete
  // otherwise.
  for (Klass *klass = original->klass(); klass != NULL;
       klass = klass->super()) {
    if (!klass->oop_is_instance()) continue;
    for (JavaFieldStream fields(InstanceKlass::cast(klass)); !fields.done();
         fields.next()) {
      if (fields.access_flags().is_static()) continue;
      const SharedFieldVersions::Location location(
          original->get_sym_rid(), fields.offset(),
          SharedFieldVersions::LOC_INSTANCE_FIELD);
      if (!SharedFieldVersions::is_tracked(location)) continue;
      const BasicType type = FieldType::basic_type(fields.signature());
      copy->set_sym_exp(fields.offset(),
          SharedFieldVersions::newest_value_if_held(
              location, SharedFieldVersions::Cell(
                  clone, type,
                  type == T_OBJECT
                      && SharedFieldVersions::wrapper_value_type(
                             fields.signature()) != T_ILLEGAL),
              copy->get(fields.offset())));
    }
  }
}

#endif // ENABLE_CONCOLIC
