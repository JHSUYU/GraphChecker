#ifndef SHARE_VM_CONCOLIC_METHODSYMBOLIZER_HPP
#define SHARE_VM_CONCOLIC_METHODSYMBOLIZER_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/symbolExpression.hpp"
#include "concolic/methodSymbolizerHandle.hpp"

#include <map>
#include <set>
#include <string>
#include <vector>

class ZeroFrame;

class MethodSymbolizer {
  typedef std::map<std::string, bool(*)(MethodSymbolizerHandle&)> invoke_helper_method_map_t;
  typedef std::map<std::string, Expression*(*)(MethodSymbolizerHandle&)> finish_helper_method_map_t;

  bool _symbolizing_method;
  MethodSymbolizerHandle _handle;
  invoke_helper_method_map_t _invoke_helper_methods;
  finish_helper_method_map_t _finish_helper_methods;
  // Logging is an observation sink, not part of the program relation.  A
  // symbolic argument may flow into formatters, encoders and appenders, but
  // none of their results flows back into the workload.  Keep those callees
  // concrete instead of recording their internal array/string constraints.
  std::vector<std::string> _classes_prefix_to_disable;

public:
  MethodSymbolizer();


  /* let compiler not optimize this  code!! */
  inline bool __attribute__((optimize("O0"))) is_symbolizing_method() { return _symbolizing_method; }

  inline void set_symbolizing_method(bool symbolizing_method) { _symbolizing_method = symbolizing_method; }

  // True when invoke_method would route this callee to a handler rather than
  // let its body speak for itself.  Such a call must reach invoke_method, so
  // an entry point that skips the Java frame has to decline it.
  bool intercepts(Method *callee_method);
  void invoke_method(ZeroFrame *caller_frame, ZeroFrame *callee_frame);
  void finish_method(ZeroFrame *caller_frame);

private:
  void init_helper_methods();

public:
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  static int prepare_param(MethodSymbolizerHandle &handle, BasicType type,
                           intptr_t *locals, int locals_offset);
  void add_invoke_helper_methods(const std::string class_name, bool(*invoke_helper_func)(MethodSymbolizerHandle&));
  void add_finish_helper_methods(const std::string class_name, Expression*(*finish_helper_func)(MethodSymbolizerHandle&));

  /**
   * Registers one symbolic model for every class it claims.
   *
   * A model is exactly a pair of helpers -- one consulted on invoke, one on
   * return -- installed under each of its target class names.  Every model
   * wrote that loop out again for itself, in four slightly different shapes.
   *
   * The array form is NULL-terminated and is the one to use when the names
   * are literals: it needs no dynamic initialization, so a model that has no
   * other use for a name set does not build one, and there is no static
   * initialization for its registration to depend on.  The set form is for
   * the models that already keep a set because they also answer
   * is_target_class() from it.
   */
  void register_model(const char *const *class_names,
                      bool (*invoke_helper)(MethodSymbolizerHandle &),
                      Expression *(*finish_helper)(MethodSymbolizerHandle &));
  void register_model(const std::set<std::string> &class_names,
                      bool (*invoke_helper)(MethodSymbolizerHandle &),
                      Expression *(*finish_helper)(MethodSymbolizerHandle &));

  void add_prefix_disabled_class(const std::string class_name);

private:
  bool disabled_class(const std::string &class_name) const;
};

class MethodReturnSymbolExp : public SymbolExpression {
  // Minted atomically: any attached thread may symbolize a method return.
  static volatile intptr_t sym_method_count;

public:
  MethodReturnSymbolExp(BasicType type);
};

#endif

#endif // SHARE_VM_CONCOLIC_METHODSYMBOLIZER_HPP
