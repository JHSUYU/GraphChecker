#ifdef ENABLE_CONCOLIC

#include "concolic/threadContext.hpp"

/**
 * Use this overload when `exp` is newly calculated, so it has no `sym_rid`
 * and `index` provenance to carry.  Writing the provenance explicitly matters:
 * the slot may still hold a previous occupant's field offset or array index.
 */
void ThreadContext::set_stack_slot(int offset, Expression *exp) {
  ShadowTable &opr_stack = this->get_last_stack();
  if (exp) {
    opr_stack.set_slot(offset, exp, NULL_SYM_RID, -1);
  } else {
    opr_stack.clear_slot(offset);
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
 * `sym_rid` and `index` are provenance -- which field, element or length the
 * value was read from.  They are not the slot's identity, and the location
 * they name keeps mutating after the read: PUTFIELD replaces the old field
 * expression and a restated array element replaces its reference expression.
 * Neither can invalidate a value some slot already took from that location,
 * because an expression outlives every structure that names it.
 */
void ThreadContext::set_stack_slot(int offset, Expression *exp,
                                   sym_rid_t sym_rid, int index) {
  if (exp) {
    this->get_last_stack().set_slot(offset, exp, sym_rid, index);
  } else {
    this->get_last_stack().clear_slot(offset);
  }
}

/**
 * TODO: document when to clear the stack
 */
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

#endif
