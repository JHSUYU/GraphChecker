#ifndef SHARE_VM_CONCOLIC_METHODSYMBOLIZERHANDLE_HPP
#define SHARE_VM_CONCOLIC_METHODSYMBOLIZERHANDLE_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "interpreter/bytecodeInterpreter.hpp"
#include "interpreterFrame_zero.hpp"
#include "runtime/frame.hpp"
#include "runtime/frame.inline.hpp"

#include <string>

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

public:
  MethodSymbolizerHandle()
      : _caller_frame(NULL), _callee_frame(NULL), _callee_istate(NULL),
        _recording(false) {}

  inline void set_recording(bool recording) { _recording = recording; }
  inline bool is_recording() const { return _recording; }

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

  // A result starts in the slot just above the callee's top of stack
  // whatever its width: a long or double is one VMJavaVal64 at &stack[1],
  // exactly where the bytecodes' STACK_LONG(-1) finds it.  Reading at
  // stack() + size took the slot past it for every long and double result --
  // an AtomicLong's getAndDecrement of 5 came back as 0x7f5c00000001.
  template<class T>
  T get_result(BasicType type) {
    assert(type2size[type] == 1 || type2size[type] == 2, "what?");
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
    clear_param_list();
    _callee_holder_name.clear();
    _callee_name.clear();
  }

};

#endif

#endif // SHARE_VM_CONCOLIC_METHODSYMBOLIZERHANDLE_HPP
