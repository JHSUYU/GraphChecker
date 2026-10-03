#ifndef SHARE_VM_CONCOLIC_METHODSYMBOLIZERHANDLE_HPP
#define SHARE_VM_CONCOLIC_METHODSYMBOLIZERHANDLE_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "interpreter/bytecodeInterpreter.hpp"
#include "interpreterFrame_zero.hpp"
#include "runtime/frame.hpp"
#include "runtime/frame.inline.hpp"

#include <string>
#include <vector>

class MethodSymbolizerHandle;

/**
 * What one callback of a modeled call returned, in the order the muted body
 * made them (MethodSymbolizer's callback window): its expression when it
 * returned one, else its concrete value or identity; whether a reference
 * result was null, or a primitive's int; whether it threw; the key its
 * seeder named the visited element by (removeIf, forEach, replaceAll); and
 * the conditions its path recorded -- a predicate compiled to branches
 * returns a constant, and what decided it is `path` (their conjunction) and
 * `path_negation` (the disjunction of their negations, NULL when one has
 * no relational complement).
 */
struct CallbackResult {
  Expression *result;
  bool symbolic;
  bool returned_null;
  jint returned_int;
  bool threw;
  Expression *key;
  Expression *path;
  Expression *path_negation;
  CallbackResult()
      : result(NULL), symbolic(false), returned_null(false), returned_int(0),
        threw(false), key(NULL), path(NULL), path_negation(NULL) {}

  /**
   * A predicate callback's answer as a condition that holds exactly where
   * it answered true: its own boolean expression, else what its path
   * decided in the direction it answered (`path` for true, `path_negation`
   * for false); NULL when nothing symbolic decided it -- or when a false
   * answer's path has no relational complement, which `undecided()` tells
   * apart.
   */
  Expression *truth() const;
  /** A symbolic decision `truth()` cannot state. */
  bool undecided() const { return !symbolic && path != NULL && truth() == NULL; }
};

/**
 * A model's contract for its callbacks: the expressions a callback's
 * parameters carry (one per parameter, NULL for none), given the session id
 * of the functional object called back and the arguments the muted body
 * passes it, and the key of the element it visits, if any.
 */
typedef void (*CallbackSeeder)(MethodSymbolizerHandle &call,
                               sym_rid_t receiver,
                               const std::vector<oop> &arguments,
                               exp_list_t *seeds, Expression **key);

/**
 * A model that reads each callback as it returns, instead of from the
 * call's log: its result, the object it returned, and its arguments as its
 * frame holds them then.  With one, a concrete result is not built into an
 * expression (the model names what it needs from the object), so a call
 * whose callbacks stay concrete allocates nothing per callback.
 */
typedef void (*CallbackListener)(MethodSymbolizerHandle &call,
                                 const CallbackResult &result, oop returned,
                                 const std::vector<oop> &arguments);

class MethodSymbolizerHandle {
private:
  ZeroFrame *_caller_frame;
  ZeroFrame *_callee_frame;
  interpreterState _callee_istate;
  exp_list_t _param_list;
  std::string _callee_holder_name;
  std::string _callee_name;
  // Whether the invoke hook decided to record this exact call.  The finish
  // hook of the same call reads it back.  It belongs to the handle -- that is,
  // to this thread's symbolizer -- because it describes one activation on one
  // thread; a per-class static would be shared by every thread attached to the
  // session and read back a decision another thread had just made.
  bool _recording;
  // The call's functional arguments (java/util/function/*, Comparator), by
  // session id: a frame whose receiver is one of them is a callback.
  std::vector<sym_rid_t> _functional;
  CallbackSeeder _seeder;
  CallbackListener _listener;
  std::vector<CallbackResult> _callbacks;
  // The state the call's container held when it began, when it had one.
  Expression *_pre_state;
  // A callback called back into this call's container.
  bool _reentered;
  // Why this call's callbacks cannot be stated (a declined window, too many
  // visits), or NULL.
  const char *_callback_refusal;
  // The call mutates as each callback answers (removeIf, replaceAll), so an
  // unwind after one did leaves a change its model cannot state.
  bool _mutates_per_callback;

public:
  MethodSymbolizerHandle()
      : _caller_frame(NULL), _callee_frame(NULL), _callee_istate(NULL),
        _recording(false), _seeder(NULL), _listener(NULL), _pre_state(NULL),
        _reentered(false), _callback_refusal(NULL),
        _mutates_per_callback(false) {}

  inline void set_recording(bool recording) { _recording = recording; }
  inline bool is_recording() const { return _recording; }

  // ---- callbacks (MethodSymbolizer::enter_callback) ----
  inline void add_functional(sym_rid_t id) { _functional.push_back(id); }
  inline bool has_functional() const { return !_functional.empty(); }
  bool is_functional(sym_rid_t id) const {
    for (size_t index = 0; index < _functional.size(); ++index) {
      if (_functional[index] == id) return true;
    }
    return false;
  }
  inline void set_seeder(CallbackSeeder seeder) { _seeder = seeder; }
  inline CallbackSeeder seeder() const { return _seeder; }
  inline void set_listener(CallbackListener listener) {
    _listener = listener;
  }
  inline CallbackListener listener() const { return _listener; }
  inline std::vector<CallbackResult> &callbacks() { return _callbacks; }
  inline void set_pre_state(Expression *pre_state) { _pre_state = pre_state; }
  inline Expression *pre_state() const { return _pre_state; }
  inline void mark_reentered() { _reentered = true; }
  inline bool reentered() const { return _reentered; }
  inline void refuse_callbacks(const char *reason) {
    if (_callback_refusal == NULL) _callback_refusal = reason;
  }
  inline const char *callback_refusal() const { return _callback_refusal; }
  inline void set_mutates_per_callback(bool mutates) {
    _mutates_per_callback = mutates;
  }
  inline bool mutates_per_callback() const { return _mutates_per_callback; }

  /**
   * returns the being offset of first parameter in callee's local variable
   * table
   */
  inline int get_callee_local_begin_offset() { return 0; }

  int get_caller_stack_begin_offset() {
    if (_caller_frame->is_interpreter_frame()) {
      interpreterState caller_istate = _caller_frame->as_interpreter_frame()->interpreter_state();
      return caller_istate->stack_base() - _callee_istate->locals() - 1;
    } else if (_caller_frame->is_entry_frame()) {
      return 0;
    }
    ShouldNotCallThis();
    return 0;
  }

  /**
   *!!the offset returned is error, discard now.
   */
  // inline int get_end_offset() {
  //   return _caller_istate->stack_base() - _caller_istate->stack() - 1;
  // }
  void sanityCheck() {
    Method *callee_method = _callee_istate->method();
    if (_caller_frame->is_interpreter_frame()) {
      ResourceMark rm;
      interpreterState caller_istate = _caller_frame->as_interpreter_frame()->interpreter_state();
      char *callee_method_name_c_str = callee_method->method_holder()->name()->as_C_string();
      // for lambda expressions(where the call site might locate in java/lang/invoke),
      // caller_istate->callee() == callee_method might not hold
      if (!strstr(callee_method_name_c_str, "java/lang/invoke") &&
          !strstr(callee_method_name_c_str, "$$Lambda")) {
        assert(caller_istate->callee() == callee_method, "should be");
      }
    } else if (_callee_frame->is_entry_frame()) {
      JavaCallWrapper *call_wrapper = *_caller_frame->as_entry_frame()->call_wrapper();
      assert(call_wrapper->callee_method() == callee_method, "should be");
    }
  }

  Method *get_callee_method() {
    sanityCheck();
    return _callee_istate->method();
  }

  inline intptr_t *get_locals_ptr() { return _callee_istate->locals(); }

  BasicType get_result_type() {
    Method *callee_method = NULL;
    if (_caller_frame->is_interpreter_frame()) {
      callee_method = _caller_frame->as_interpreter_frame()->interpreter_state()->callee();
    } else if (_caller_frame->is_entry_frame()) {
      JavaCallWrapper *call_wrapper = *_caller_frame->as_entry_frame()->call_wrapper();
      callee_method = call_wrapper->callee_method();
    }
    return callee_method->result_type();
  }

  // Whether the finishing call's result can be read at all.  The finish hook
  // runs inside pop_zero_frame; a native callee's primitive result is then
  // still in native_entry's C local (it is pushed after the pop), so the
  // popped frame's stack holds whatever was there before.  Only an oop
  // result is reachable, in the frame's oop_temp (review1 #3).
  bool result_readable() {
    if (!_callee_istate->method()->is_native()) return true;
    BasicType type = get_result_type();
    return type == T_VOID || type == T_OBJECT || type == T_ARRAY;
  }

  // A result starts in the slot just above the callee's top of stack
  // whatever its width: a long or double is one VMJavaVal64 at &stack[1],
  // exactly where the bytecodes' STACK_LONG(-1) finds it.  Reading at
  // stack() + size took the slot past it for every long and double result --
  // an AtomicLong's getAndDecrement of 5 came back as 0x7f5c00000001.
  template<class T>
  T get_result(BasicType type) {
    assert(type2size[type] == 1 || type2size[type] == 2, "what?");
    guarantee(result_readable(), "a native's primitive result is not "
              "reachable when its frame is popped");
    if (_callee_istate->method()->is_native()) {
      return *(T *) _callee_istate->oop_temp_addr();
    }
    return *(T *) (_callee_istate->stack() + 1);
  }

  inline void set_caller_frame(ZeroFrame *caller_frame) {
    _caller_frame = caller_frame;
  }

  inline void set_callee_frame(ZeroFrame *callee_frame) {
    _callee_frame = callee_frame;
    _callee_istate = callee_frame->as_interpreter_frame()->interpreter_state();
  }

  inline ZeroFrame *get_caller_frame() { return _caller_frame; }

  inline ZeroFrame *get_callee_frame() { return _callee_frame; }

  inline interpreterState get_callee_istate() { return _callee_istate; }

  inline void set_callee_holder_name(const char *c_str) {
    _callee_holder_name = std::string(c_str);
  }

  inline const std::string &get_callee_holder_name() {
    return _callee_holder_name;
  }

  inline void set_callee_name(const char *c_str) {
    _callee_name = std::string(c_str);
  }

  inline const std::string &get_callee_name() { return _callee_name; }

  inline exp_list_t &get_param_list() { return _param_list; }

  template<class T>
  inline T get_param(int offset) {
    return *(T *) (get_locals_ptr() - offset);
  }

  Expression *get_primitive_exp(int offset, BasicType type);

  // Returns an alias-specific operand shadow when one reached this call, or
  // the session's object shadow otherwise.  It never allocates a
  // symbolic object merely by observing an argument.
  Expression *get_reference_exp(int offset, oop obj);

  void general_prepare_param(int max_param_num = 100);

  int general_prepare_param_helper(BasicType type, int locals_offset, bool is_this);

  bool general_check_param_symbolized();

  bool general_check_param_symbolized_helper(BasicType type, int &locals_offset);

public:
  // The parameter list only names expressions; the session arena owns them.
  inline void clear_param_list() {
    _param_list.clear();
  }

  inline void reset() {
    _caller_frame = NULL;
    _callee_frame = NULL;
    _callee_istate = NULL;
    _recording = false;
    _functional.clear();
    _seeder = NULL;
    _listener = NULL;
    _callbacks.clear();
    _pre_state = NULL;
    _reentered = false;
    _callback_refusal = NULL;
    _mutates_per_callback = false;
    clear_param_list();
    _callee_holder_name.clear();
    _callee_name.clear();
  }

};

#endif

#endif // SHARE_VM_CONCOLIC_METHODSYMBOLIZERHANDLE_HPP
