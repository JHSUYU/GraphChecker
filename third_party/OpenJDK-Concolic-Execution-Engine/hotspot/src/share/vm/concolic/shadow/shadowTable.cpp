#ifdef ENABLE_CONCOLIC

#include "concolic/shadow/shadowTable.hpp"
#include "utilities/ostream.hpp"
#include "concolic/concolicMngr.hpp"

ShadowTable::ShadowTable() {}

void ShadowTable::guarantee_index(const char *operation, int offset) const {
  int table_size = (int)_tbl.size();
  guarantee(offset >= 0 && offset < table_size,
            err_msg("ShadowTable %s index %d outside [0,%d)",
                    operation, offset, table_size));
}

void ShadowTable::guarantee_range(const char *operation, int first_offset,
                                  int slot_count) const {
  int table_size = (int)_tbl.size();
  guarantee(first_offset >= 0 && slot_count >= 0
                && first_offset <= table_size
                && slot_count <= table_size - first_offset,
            err_msg("ShadowTable %s range first=%d count=%d outside size=%d",
                    operation, first_offset, slot_count, table_size));
}

void ShadowTable::init(int max_slot_size) {
  guarantee(max_slot_size >= 0, "ShadowTable size must be non-negative");
  _tbl.resize(max_slot_size);
}

void ShadowTable::copy_entries(ShadowTable &src_tbl, int src_begin,
                               int dst_begin, int size) {
  src_tbl.guarantee_range("copy source", src_begin, size);
  guarantee_range("copy destination", dst_begin, size);
  /**
   * TODO: memcpy
   */
  for (int i = 0; i < size; i++) {
    const Entry &entry = src_tbl.get_entry(src_begin++);
    set_slot(dst_begin++, entry);
  }
}

void ShadowTable::clear_slots(int first_offset, int slot_count) {
  guarantee_range("clear", first_offset, slot_count);
  for (int offset = first_offset;
       offset < first_offset + slot_count; ++offset) {
    clear_slot(offset);
  }
}

void ShadowTable::clear_all() {
  clear_slots(0, size());
}

void ShadowTable::print() {
  int size = _tbl.size();
  tty->print_cr(" size: %d", size);
  for (int i = 0; i < size; ++i) {
    int offset = size - i - 1;
    Entry &entry = _tbl[offset];
    tty->print_cr("     [%d] SymExpression: %p, sym_rid: %lu, index %d", offset,
                  entry.exp, entry.sym_rid, entry.index);
  }
}

void ShadowTable::set_slot(int offset, Expression *exp, sym_rid_t sym_rid, int index) {
  guarantee_index("set expression and provenance", offset);
  Entry &entry = _tbl[offset];
  entry.exp = exp;
  entry.sym_rid = sym_rid;
  entry.index = index;
}

Expression *ShadowTable::get_slot(int offset) {
  guarantee_index("get expression", offset);
  Expression *ret = _tbl[offset].exp;
  // assert(ret, "not null");
  return ret;
}

void ShadowTable::set_slot(int offset, Expression *exp) {
  guarantee_index("set expression", offset);
  Entry &entry = _tbl[offset];
  entry.exp = exp;
}

void ShadowTable::set_slot(int offset, const Entry &other) {
  guarantee_index("set entry", offset);
  _tbl[offset] = other;
}

void ShadowTable::clear_slot(int offset) {
  guarantee_index("clear entry", offset);
  _tbl[offset].reset();
}

ShadowTable::Entry &ShadowTable::get_entry(int offset) {
  guarantee_index("get entry", offset);
  return _tbl[offset];
}

void ShadowTable::swap_two_entries(int off1, int off2) {
  guarantee_index("swap first", off1);
  guarantee_index("swap second", off2);
  Entry &entry1 = _tbl[off1];
  Entry &entry2 = _tbl[off2];
  Entry temp;

  temp = entry1;
  entry1 = entry2;
  entry2 = temp;
}


ShadowTable::Entry &ShadowTable::Entry::operator=(const ShadowTable::Entry &other) {
  this->sym_rid = other.sym_rid;
  this->index = other.index;
  this->exp = other.exp;
  return *this;
}
#endif
