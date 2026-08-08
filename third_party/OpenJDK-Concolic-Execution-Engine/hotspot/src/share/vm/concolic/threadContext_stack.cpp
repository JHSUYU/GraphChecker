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


/**
 * A shadow slot names a value; it never owns the expression it names, and it
 * has no say in when that expression dies.  This is where the reference that
 * makes the naming safe is taken.
 *
 * The activation's temporary store is the only structure that outlives every
 * shadow slot without outliving the region, so it is the slot's owner of
 * record.  No tmp id is handed back: this reference is a claim for the rest
 * of the activation, released once when the context is torn down, never by a
 * detach.
 */
void ThreadContext::retain_for_activation(Expression *exp) {
  if (exp == NULL) return;
  this->get_next_sym_tmp_id(exp);
}

/**
 * `sym_rid` and `index` are provenance -- which field, element or length the
 * value was read from.  They are not the slot's identity, and the location
 * they name keeps mutating after the read: PUTFIELD hands the old field
 * expression to Expression::gc, a restated array element replaces its
 * reference expression, and either one frees a tree the operand stack and
 * the locals are still allowed to read.  Retain first, exactly as the
 * value-producing overload above already does, so a write to the location
 * can never delete a value some slot already took from it.
 */
void ThreadContext::set_stack_slot(int offset, Expression *exp,
                                   sym_rid_t sym_rid, int index) {
  if (exp) {
    this->retain_for_activation(exp);
    this->get_last_stack().set_slot(offset, exp, sym_rid, index);
  } else {
    this->get_last_stack().clear_slot(offset);
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

#endif
