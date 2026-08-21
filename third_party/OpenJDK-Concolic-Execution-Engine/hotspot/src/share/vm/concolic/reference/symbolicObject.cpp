#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicObject.hpp"
#include "oops/klass.hpp"
#include "utilities/ostream.hpp"

SymObj::SymObj(sym_rid_t sym_rid) : SymInstance(sym_rid), _ref_exp(NULL) {}

SymObj::~SymObj() {}

// Last-writer-wins, made literal by _field_mutex: a reader observes one
// completed write, never a half-rebalanced tree.  Which write it observes is
// the named CONCURRENT_FIELD_SHADOW_WRITE gap; see sessionSymbolicHeap.hpp.

Expression *SymObj::get(int field_offset) {
  FieldLock guard(this);
  exp_map_t::iterator iter = _exps.find(field_offset);
  return iter == _exps.end() ? NULL : iter->second;
}

void SymObj::init_sym_exp(int field_offset, Expression *exp) {
  FieldLock guard(this);
  _exps[field_offset] = exp;
}

void SymObj::set_sym_exp(int field_offset, Expression *exp) {
  FieldLock guard(this);
  if (exp == NULL) {
    _exps.erase(field_offset);
  } else {
    _exps[field_offset] = exp;
  }
}

void SymObj::print() {
  FieldLock guard(this);
  exp_map_t::iterator iter;
  for (iter = _exps.begin(); iter != _exps.end(); ++iter) {
    tty->print_cr("Field(%d): ", iter->first);
    iter->second->print_cr();
  }
}

#endif