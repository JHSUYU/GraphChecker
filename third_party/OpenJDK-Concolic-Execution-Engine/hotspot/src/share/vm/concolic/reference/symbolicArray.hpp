#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICARRAY_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICARRAY_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/reference/symbolicReference.hpp"
#include "oops/oop.inline.hpp"
#include "utilities/debug.hpp"

#include <map>
#include <stdio.h>

class SymArr : public SymRef {
private:
  int _version;
  Expression *_length_exp;
  Expression *_ref_exp;
  bool _semantic_expression;
  // The shadow exists only because a read at a symbolic index named the
  // array: its contents are the heap's own until something writes or
  // symbolizes it.
  bool _named_by_read;

public:
  SymArr(sym_rid_t sym_rid, Expression *length_exp);
  ~SymArr();

  Expression *get_ref_exp() { return _ref_exp; };
  void set_ref_exp(Expression *expression) {
    _ref_exp = expression;
    _semantic_expression = expression != NULL;
  }

  inline void mark_semantic_expression() {
    _semantic_expression = true;
  }

  inline bool has_semantic_expression() const {
    return _semantic_expression;
  }

  inline void set_named_by_read(bool named) { _named_by_read = named; }
  inline bool named_by_read() const { return _named_by_read; }

  inline void store() {
    ++_version;
  }

  inline void set_length_exp(Expression *length_exp) {
    _length_exp = length_exp;
  }

  inline Expression *get_length_exp() { return _length_exp; }
  inline int get_version() { return _version; }

public:
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICARRAY_HPP
