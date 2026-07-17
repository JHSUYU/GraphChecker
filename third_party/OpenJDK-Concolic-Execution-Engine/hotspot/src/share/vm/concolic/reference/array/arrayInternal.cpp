//
// Created by gansen on 5/18/22.
//
#ifdef ENABLE_CONCOLIC
#include "arrayInternal.hpp"

void ArrayInternal::store(int index, Expression *exp,
                          const char *provenance) {
  guarantee(index >= 0, "Must be >= 0");
  try_resize(index);
  guarantee(index < (int) _element_exprs.size(), "Must be < size");
  // Increment first: an overlapping arraycopy may store the same expression
  // back into a slot, and dropping the old reference first would free it.
  if (exp != NULL) {
    exp->inc_ref();
  }
  Expression::gc(_element_exprs[index]);
  _element_exprs[index] = exp;
  _element_valid[index] = true;
  _element_provenance[index] = provenance == NULL
      ? "BYTECODE_ARRAY_STORE" : provenance;
}

Expression *ArrayInternal::load(int index) const {
  if (index < 0 || index >= (int) _element_exprs.size()
      || !_element_valid[index]) {
    return NULL;
  }

  return _element_exprs[index];
}

bool ArrayInternal::is_valid(int index) const {
  return index >= 0 && index < (int) _element_valid.size()
      && _element_valid[index];
}

const char *ArrayInternal::provenance(int index) const {
  if (index < 0 || index >= (int) _element_provenance.size()) {
    return "OUT_OF_RANGE";
  }
  return _element_provenance[index].c_str();
}

bool ArrayInternal::has_expression(int index) const {
  return is_valid(index) && _element_exprs[index] != NULL;
}

bool ArrayInternal::has_expression_in_range(int start, int length) const {
  if (length <= 0) return false;
  for (int offset = 0; offset < length; ++offset) {
    int index = start + offset;
    if (has_expression(index)) return true;
  }
  return false;
}

void ArrayInternal::reset_to_concrete(int index, const char *provenance) {
  store(index, NULL, provenance);
}

void ArrayInternal::invalidate(int index, const char *provenance) {
  guarantee(index >= 0, "Must be >= 0");
  try_resize(index);
  // Keep the old expression owned but unreachable while invalid.  In
  // particular, JVM_ArrayCopy may call this with a pending Java exception;
  // that path must only flip independent validity metadata, not run symbolic
  // expression reclamation or any other stateful engine operation.
  _element_valid[index] = false;
  _element_provenance[index] = provenance == NULL
      ? "INVALIDATED_ARRAYCOPY_EXCEPTION" : provenance;
}

void ArrayInternal::copy_range_from(const ArrayInternal *source,
                                    int source_pos, int destination_pos,
                                    int length) {
  guarantee(source != NULL, "source shadow must exist");
  guarantee(source_pos >= 0 && destination_pos >= 0 && length >= 0,
            "validated JVM arraycopy range expected");

  // Stage the whole source interval so this is a true memmove when source and
  // destination are the same shadow array and the intervals overlap.
  std::vector<Expression *> expressions(length, NULL);
  std::vector<bool> valid(length, true);
  for (int offset = 0; offset < length; ++offset) {
    int source_index = source_pos + offset;
    valid[offset] = source->is_valid(source_index);
    if (valid[offset]) {
      expressions[offset] = source->load(source_index);
      if (expressions[offset] != NULL) expressions[offset]->inc_ref();
    }
  }

  for (int offset = 0; offset < length; ++offset) {
    int destination_index = destination_pos + offset;
    if (!valid[offset]) {
      invalidate(destination_index, "JVM_ARRAYCOPY_SOURCE_INVALID");
    } else {
      store(destination_index, expressions[offset],
            expressions[offset] == NULL
                ? "JVM_ARRAYCOPY_CONCRETE_VALUE"
                : "JVM_ARRAYCOPY_SHADOW_MEMMOVE");
    }
  }

  for (int offset = 0; offset < length; ++offset) {
    Expression::gc(expressions[offset]);
  }
}

void ArrayInternal::try_resize(int index) {
  if (index >= (int) _element_exprs.size()) {
    _element_exprs.resize(index + 1, NULL);
    _element_valid.resize(index + 1, true);
    _element_provenance.resize(index + 1, "VM_CONCRETE_VALUE");
  }
}

ArrayInternal::~ArrayInternal() {
  for (size_t elem_index = 0; elem_index < _element_exprs.size(); elem_index++) {
    Expression::gc(_element_exprs[elem_index]);
    _element_exprs[elem_index] = NULL;
  }
}
#endif
