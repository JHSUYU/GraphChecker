#ifdef ENABLE_CONCOLIC

#include "concolic/threadContext.hpp"

/**
 * this will generate a new tmp_id; use it when `exp` is newly
 * calculated, which doesn't have `sym_rid` and `index`
 */
void ThreadContext::set_stack_slot(int offset, Expression *exp) {
  ShadowTable &opr_stack = this->get_last_stack();
  if (exp) {
    sym_tmp_id_t sym_tmp_id = this->get_next_sym_tmp_id(exp);
    opr_stack.set_slot(offset, exp, NULL_SYM_RID, sym_tmp_id);
  } else {
    opr_stack.clear_slot(offset);
  }
}

void ThreadContext::set_stack_slot_if_possible(int offset, Expression *exp) {
  if (this->get_last_stack().size() > 0) {
    this->set_stack_slot(offset, exp);
  }
}

void ThreadContext::set_stack_value_if_possible(int anchor_offset,
                                                int slot_count,
                                                Expression *exp) {
  if (this->get_last_stack().size() > 0) {
    this->set_stack_value(anchor_offset, slot_count, exp);
  }
}


void ThreadContext::set_stack_slot(int offset, Expression *exp,
                                   sym_rid_t sym_rid, int index) {
  ShadowTable &opr_stack = this->get_last_stack();
  if (exp) {
    opr_stack.set_slot(offset, exp, sym_rid, index);
  } else {
    opr_stack.clear_slot(offset);
  }
}

/**
 * TODO: document when to clear the stack
 */
void ThreadContext::clear_stack_slot(int offset) {
  return this->get_last_stack().clear_slot(offset);
}

void ThreadContext::clear_stack_words(int first_offset, int slot_count) {
  ShadowTable &opr_stack = this->get_last_stack();
  if (opr_stack.size() == 0 || slot_count == 0) return;
  opr_stack.clear_slots(first_offset, slot_count);
}

void ThreadContext::clear_stack_value(int anchor_offset, int slot_count) {
  assert(slot_count == 1 || slot_count == 2,
         "a JVM value occupies one or two shadow slots");
  this->get_last_stack().clear_slots(anchor_offset - slot_count + 1,
                                     slot_count);
}

void ThreadContext::set_stack_value(int anchor_offset, int slot_count,
                                    Expression *exp) {
  clear_stack_value(anchor_offset, slot_count);
  if (exp != NULL) set_stack_slot(anchor_offset, exp);
}

void ThreadContext::set_stack_value(int anchor_offset, int slot_count,
                                    Expression *exp, sym_rid_t sym_rid,
                                    int index) {
  clear_stack_value(anchor_offset, slot_count);
  if (exp != NULL) set_stack_slot(anchor_offset, exp, sym_rid, index);
}

void ThreadContext::clear_operand_stack() {
  this->get_last_stack().clear_all();
}

void ThreadContext::copy_local_value_to_stack(int local_anchor_offset,
                                              int stack_anchor_offset,
                                              int slot_count) {
  assert(slot_count == 1 || slot_count == 2,
         "a JVM value occupies one or two shadow slots");
  ShadowTable::Entry source;
  source = this->get_local_entry(local_anchor_offset);
  clear_stack_value(stack_anchor_offset, slot_count);
  this->get_last_stack().set_slot(stack_anchor_offset, source);
}

void ThreadContext::move_stack_value_to_local(int stack_anchor_offset,
                                              int local_anchor_offset,
                                              int slot_count) {
  assert(slot_count == 1 || slot_count == 2,
         "a JVM value occupies one or two shadow slots");
  ShadowTable::Entry source;
  source = this->get_stack_entry(stack_anchor_offset);
  this->get_last_local().clear_slots(local_anchor_offset - slot_count + 1,
                                    slot_count);
  this->get_last_local().set_slot(local_anchor_offset, source);
  clear_stack_value(stack_anchor_offset, slot_count);
}

void ThreadContext::copy_stack_slot(int src_off, int dst_off, int size) {
  ShadowTable &opr_stack = this->get_last_stack();
  opr_stack.copy_entries(opr_stack, src_off, dst_off, size);
}

void ThreadContext::swap_two_stack_slot(int off1, int off2) {
  ShadowTable &opr_stack = this->get_last_stack();
  opr_stack.swap_two_entries(off1, off2);
}

void ThreadContext::copy_entry_from_local_to_stack(int local_offset,
                                                   int stack_offset) {
  assert(local_offset >= 0, "local_offset >= 0");
  assert(stack_offset >= 0, "stack_offset >= 0");
  ShadowTable::Entry &entry = this->get_local_entry(local_offset);
  this->get_last_stack().set_slot(stack_offset, entry);
}

void ThreadContext::copy_entry_from_stack_to_local(int stack_offset,
                                                   int local_offset) {
  assert(local_offset >= 0, "local_offset >= 0");
  assert(stack_offset >= 0, "stack_offset >= 0");
  ShadowTable::Entry &entry = this->get_stack_entry(stack_offset);
  this->get_last_local().set_slot(local_offset, entry);
}

ArrayInternal *ThreadContext::get_or_create_array_internal(arrayOop oop) {
  if (!oop) {
    return NULL;
  }

  ArrayInternal *existing = find_array_internal(oop);
  if (existing != NULL) return existing;

  Handle array_handle(_thread, oop);
  jobject stable_handle = JNIHandles::make_global(array_handle);
  ArrayInternal *created = new ArrayInternal(oop->length());
  _array_store.insert(std::make_pair(stable_handle, created));
  return created;
}

ArrayInternal *ThreadContext::find_array_internal(arrayOop oop) const {
  if (oop == NULL) return NULL;
  for (ArrayStore::const_iterator found = _array_store.begin();
       found != _array_store.end(); ++found) {
    if (JNIHandles::resolve(found->first) == oop) return found->second;
  }
  return NULL;
}

void ThreadContext::store_array_element_shadow(arrayOop array, int index,
                                               Expression *expression,
                                               const char *provenance) {
  if (array == NULL || index < 0 || index >= array->length()) return;
  ArrayInternal *internal = find_array_internal(array);
  // A concrete overwrite with no shadow only has work to do when an older
  // shadow exists.  This keeps ordinary array traffic out of the shadow map.
  if (internal == NULL && expression == NULL) return;
  if (internal == NULL) internal = get_or_create_array_internal(array);
  internal->store(index, expression, provenance);
}

void ThreadContext::prepare_arraycopy_shadow(arrayOop destination) {
  if (destination == NULL) return;
  // Run before the real JVM copy, while no exception is pending.  This makes
  // the exceptional completion path allocation-free.
  get_or_create_array_internal(destination);
}

void ThreadContext::arraycopy_shadow(arrayOop source, int source_pos,
                                     arrayOop destination,
                                     int destination_pos, int length) {
  if (source == NULL || destination == NULL || length <= 0) return;

  ArrayInternal *source_internal = find_array_internal(source);
  ArrayInternal *destination_internal = find_array_internal(destination);
  if (source_internal != NULL) {
    if (destination_internal == NULL) {
      destination_internal = get_or_create_array_internal(destination);
    }
    destination_internal->copy_range_from(source_internal, source_pos,
                                          destination_pos, length);
  } else if (destination_internal != NULL) {
    // The source has no per-element shadows.  The successful JVM copy makes
    // the destination values exact concrete heap values again.
    for (int offset = 0; offset < length; ++offset) {
      destination_internal->reset_to_concrete(
          destination_pos + offset, "JVM_ARRAYCOPY_CONCRETE_VALUE");
    }
  }

  SymArr *destination_array = find_sym_array(destination);
  if (destination_array != NULL) destination_array->store();
}

void ThreadContext::invalidate_arraycopy_shadow(arrayOop destination,
                                                int destination_pos,
                                                int length) {
  if (destination == NULL || length <= 0) return;
  jlong requested_start = destination_pos;
  jlong requested_end = requested_start + (jlong) length;
  int start = requested_start < 0 ? 0 : (int) requested_start;
  int end = requested_end > destination->length()
      ? destination->length() : (int) requested_end;
  if (start >= end || start >= destination->length() || end <= 0) return;

  ArrayInternal *destination_internal = find_array_internal(destination);
  if (destination_internal == NULL) return;
  for (int index = start; index < end; ++index) {
    destination_internal->invalidate(
        index, "INVALIDATED_ARRAYCOPY_EXCEPTION");
  }
}


#endif
