//
// Created by gansen on 5/18/22.
//

#ifndef JDK8_CDB_ARRAYINTERNAL_HPP
#define JDK8_CDB_ARRAYINTERNAL_HPP
#ifdef ENABLE_CONCOLIC
#include "oops/oopsHierarchy.hpp"
#include "concolic/exp/expression.hpp"

#include <string>
#include <vector>

// representation of an array in cpp form
class ArrayInternal {
private:
  std::vector<Expression* > _element_exprs;
  std::vector<bool> _element_valid;
  std::vector<std::string> _element_provenance;

  void try_resize(int index);
public:
  ArrayInternal(int length) {
    guarantee(length >= 0, "Array length should be >= 0");
    _element_exprs.resize(length, NULL);
    _element_valid.resize(length, true);
    _element_provenance.resize(length, "VM_CONCRETE_VALUE");
  }
  ~ArrayInternal();

  void store(int index, Expression* exp,
             const char *provenance = "BYTECODE_ARRAY_STORE");
  Expression* load(int index) const;
  bool is_valid(int index) const;
  const char *provenance(int index) const;
  bool has_expression(int index) const;
  bool has_expression_in_range(int start, int length) const;
  void reset_to_concrete(int index,
                         const char *provenance = "VM_CONCRETE_VALUE");
  void invalidate(int index,
                  const char *provenance =
                      "INVALIDATED_ARRAYCOPY_EXCEPTION");
  void copy_range_from(const ArrayInternal *source, int source_pos,
                       int destination_pos, int length);
};

#endif
#endif //JDK8_CDB_ARRAYINTERNAL_HPP
