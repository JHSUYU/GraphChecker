#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICATOMIC_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICATOMIC_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "concolic/methodSymbolizer.hpp"

/** Symbolic summaries for the arithmetic read-modify-write Atomic methods. */
class SymbolicAtomic {
public:
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);
  static void init_register_class(MethodSymbolizer *method_symbolizer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICATOMIC_HPP
