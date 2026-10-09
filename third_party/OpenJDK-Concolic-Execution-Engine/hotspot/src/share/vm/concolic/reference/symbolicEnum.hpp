#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICENUM_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICENUM_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "oops/arrayOop.hpp"

class MethodSymbolizer;

/**
 * The enum model: a constant Enum.valueOf chose by a symbolic name is that
 * name.  Its result slot -- never the constant, which is JVM-wide -- carries
 * `MethodExpression("java/lang/Enum valueOf", [class, n, c0, ..., ck])`,
 * `n` the name and `c0..ck` the class's constant names in ordinal order,
 * a String-valued node COMPOSE lowers to `n` defined where it is one of
 * them.  `name()` and `Enum.toString()` of it are the node, `ordinal()`
 * `MethodExpression("java/lang/Enum ordinal", [node, c0, ..., ck])`; a
 * reference compare with it is the String `equals` of the two names
 * (compare); an int array no recorded write touched, read at its ordinal
 * -- a switch map javac filled once -- reads a stated snapshot of the array
 * (table_read).  Every other Enum method runs as bytecode.
 */
class SymEnum {
public:
  static void init_register_class(MethodSymbolizer *m_symbolizer);
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  // if_acmpeq/ne of two operands, either a constant valueOf named: the
  // String equals of their names (a null operand's is null), or NULL when
  // neither is one.
  static Expression *compare(Expression *left, oop left_obj,
                             Expression *right, oop right_obj);
  // A load of `array` at `index`, an ordinal: a READ of the array's
  // elements as a stated snapshot, or NULL where it is no untouched int
  // array within the snapshot bound.
  static Expression *table_read(arrayOop array, Expression *index);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICENUM_HPP
