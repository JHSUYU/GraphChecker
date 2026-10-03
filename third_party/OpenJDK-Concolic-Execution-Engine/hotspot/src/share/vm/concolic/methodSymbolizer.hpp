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
  // The muted calls whose callbacks are running, innermost last, and the
  // callback frames, one per suspended call.
  struct CallbackWindow {
    const ZeroFrame *frame;
    Expression *key;
    // The thread's path-condition length when the callback began.
    int path_start;
  };
  std::vector<MethodSymbolizerHandle> _suspended;
  std::vector<CallbackWindow> _windows;
  static const size_t MAX_CALLBACK_DEPTH = 4;
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

  /**
   * The callback window.  While a model call's body runs muted, a frame
   * whose receiver is one of the call's functional arguments is a callback
   * (a lambda's apply/test/accept): it runs with propagation, its parameters
   * seeded by the model's contract (CallbackSeeder), and a model call inside
   * it nests -- the muted call's handle is suspended on a stack, at most
   * MAX_CALLBACK_DEPTH deep.  What it returned is logged on the call
   * (CallbackResult), from which the model's finish builds the mutation.
   * Its side effects are hooked like any interpreted code; before, they ran
   * muted and were lost.  True when `callee_frame` opened one.
   */
  bool enter_callback(ZeroFrame *caller_frame, ZeroFrame *callee_frame);
  /** Closes the innermost window when `callee_frame` is its frame. */
  bool exit_callback(ZeroFrame *callee_frame);
  /**
   * Whether a call suspended in a callback window is on `container` (its
   * receiver's backing container); such a call is marked reentered.
   */
  bool reenters(oop container);
  /** Whether a callback window is open on this thread. */
  inline bool in_callback() const { return !_windows.empty(); }
  /** Whether a call made now could still open callback windows. */
  inline bool callbacks_available() const {
    return _windows.size() < MAX_CALLBACK_DEPTH;
  }

private:
  void init_helper_methods();
  // Names the call's functional arguments, so their frames are found.
  void register_functional_arguments();

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

/**
 * The primitive result of a call the VM does not model: a fresh symbol.
 *
 * It states the value the call returned, because nothing else declares the
 * symbol: SOLR-18406's SolrParams.getLong of a request parameter
 * (Long.parseLong) minted M_J_return28, and the composer cut it as an
 * undeclared free symbol.  And it states the call it is the result of --
 * callee and argument expressions, serialized as every node's children are
 * -- so that a consumer can lower a known function as a relation, and can
 * tell a pin of the returned value that would cut a moved root (an argument
 * that names one) from one that would not.  The same relation used to live
 * only in the path condition's MethodExpression, out of reach of the node.
 */
class MethodReturnSymbolExp : public SymbolExpression {
  // Minted atomically: any attached thread may symbolize a method return.
  static volatile intptr_t sym_method_count;

  ReturnedValue _returned;
  std::string _holder;
  std::string _name;
  std::string _descriptor;
  exp_list_t _arguments;

public:
  // Mints the result of the call `handle` is finishing.
  explicit MethodReturnSymbolExp(MethodSymbolizerHandle &handle);

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif

#endif // SHARE_VM_CONCOLIC_METHODSYMBOLIZER_HPP
