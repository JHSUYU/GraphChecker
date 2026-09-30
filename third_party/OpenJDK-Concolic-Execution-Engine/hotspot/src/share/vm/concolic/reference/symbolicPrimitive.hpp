#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICPRIMITIVE_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICPRIMITIVE_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/utils.hpp"
#include <string>

template <class T> class SymPrimitive : public SymInstance {
public:
  static const char *ARRAY_TYPE_NAME;
  static const char *TYPE_NAME;

private:
  Expression *_exp;

public:
  SymPrimitive(sym_rid_t sym_rid);
  ~SymPrimitive();

  Expression *get(int field_offset);
  Expression *get_ref_exp() { return _exp; };
  void set_ref_exp(Expression *exp) {
    _exp = exp;
    mark_semantic_expression();
  };

  void init_sym_exp(int field_offset, Expression *exp);
  void set_sym_exp(int field_offset, Expression *exp);
  bool has_sym_exp(int field_offset);
  static void set_symbolic_field(oop obj, Symbol* fld_name, Symbol* fld_tp_sig, MethodSymbolizerHandle &handle);
  static bool match_callee_and_do_sym(MethodSymbolizerHandle &handle, const char* sig);
public:

public:
  static Expression *get_exp_of(oop obj);
  static Expression *get_exp_of_helper(oop obj);
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);
};

/**
 * Whether `obj` is one JVM-wide object: an entry of a JDK box cache
 * (Byte/Short/Integer/Long/Character.valueOf) or such a cache's own array,
 * Boolean.TRUE/FALSE, an interned String, or an enum constant.  Every later
 * `Integer.valueOf(5)` in the JVM is that same object, so an expression
 * attached to it would be read back by code that never saw the value.  The
 * one rule: a JVM-shared identity never carries a shadow.  A value such an
 * object carries rides the slot that holds it, and the object stays clean
 * (item 5); every mint (the symbolizers, System.mintLeaf) and every model
 * result asks here first.
 */
bool jvm_shared_object(oop obj);

bool primitive_invoke_method_helper(MethodSymbolizerHandle &handle,BasicType type);
Expression *primitive_finish_method_helper(MethodSymbolizerHandle &handle,BasicType type);
BasicType primitive_target(const std::string &class_name);

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICPRIMITIVE_HPP
