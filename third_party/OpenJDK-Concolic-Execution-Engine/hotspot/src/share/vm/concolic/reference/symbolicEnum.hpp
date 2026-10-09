#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICENUM_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICENUM_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/SymbolicOp.hpp"
#include "concolic/defs.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "oops/arrayOop.hpp"

class MethodSymbolizer;

/**
 * The enum model: an enum constant is its name.  Enum.valueOf with a
 * symbolic name returns the run's constant, its result **slot** -- never the
 * constant, which is JVM-wide -- carrying
 * `MethodExpression("java/lang/Enum valueOf", [class, n, c0, ..., ck])`,
 * `n` the name and `c0..ck` the class's constant names in ordinal order (its
 * enum constant fields), a String-valued node COMPOSE lowers to `n` defined
 * where it is one of them.  A constant a container holds is its name too
 * (constant_name, ContainerSupport::concrete_value), so a key valueOf named
 * and one the program held agree.  `name()` and `Enum.toString()` of the
 * node are the node, `ordinal()` `MethodExpression("java/lang/Enum ordinal",
 * [node, c0, ..., ck])`; a reference compare with it is a compare of names
 * within its class (compare); a switch map javac or ecj made, loaded at its
 * ordinal, reads a stated snapshot of the map (loaded_static, table_read).
 * Every other Enum method runs as bytecode.
 */
class SymEnum {
public:
  static void init_register_class(MethodSymbolizer *m_symbolizer);
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  // An enum constant's name, a String constant, else NULL.
  static Expression *constant_name(oop value);
  // The condition of an if_acmp`op` that took `outcome` over two operands,
  // either a constant valueOf named, else NULL (a reference compare).
  static Expression *compare(Expression *left, oop left_obj,
                             Expression *right, oop right_obj, SymbolicOp op,
                             bool outcome);
  // A getstatic of `holder`'s field at `offset` loaded `value`: a switch
  // map is noted for table_read.
  static void loaded_static(Klass *holder, int offset, oop value);
  // A load of `array` at `index`, an ordinal: a READ of a switch map's
  // elements as a stated snapshot, or NULL for any other array.
  static Expression *table_read(arrayOop array, Expression *index);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICENUM_HPP
