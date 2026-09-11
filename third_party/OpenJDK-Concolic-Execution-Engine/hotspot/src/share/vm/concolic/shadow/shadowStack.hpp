#ifndef SHARE_VM_CONCOLIC_SHADOW_SHADOWSTACK_HPP
#define SHARE_VM_CONCOLIC_SHADOW_SHADOWSTACK_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/shadow/shadowFrame.hpp"

#include <vector>

class JavaThread;
class Method;

class ShadowStack {
  typedef std::vector<ShadowFrame *> ShadowFrames;
  static const int DEFAULT_MAX_STACK_DEPTH = 1024;

private:
  struct PendingReflection {
    jlong token;
    Method *target;
    int entry_words;
    ShadowTable carrier;

    PendingReflection(jlong call_token, Method *method, int parameter_words)
        : token(call_token), target(method), entry_words(parameter_words) {}
  };

  ShadowFrames _s_frames;
  /**
   * Reflection can nest while a target is being prepared.  Each argument
   * table is therefore paired with its exact target and consumed LIFO.
   */
  std::vector<PendingReflection *> _pending_reflections;
  jlong _next_reflection_token;
  Expression *_reflection_ret_exp;

public:
  ShadowStack(JavaThread *jt);

  ~ShadowStack();

  jlong register_reflection_call(Method *target, int entry_words,
                                 ShadowTable &carrier);
  bool take_reflection_stack(Method *target, int entry_words,
                             ShadowTable &destination);
  bool cancel_reflection_call(jlong token);

  void set_reflection_ret_exp(Expression *exp) {
    assert(_reflection_ret_exp == NULL, "should be");
    _reflection_ret_exp = exp;
  }

  Expression *get_reflection_ret_exp() {
    Expression *ret = _reflection_ret_exp;
    _reflection_ret_exp = NULL;
    return ret;
  }

  inline ShadowFrame &get_last_frame() { return *_s_frames.back(); }

  inline bool symbolic_tracking_enabled() const {
    return !_s_frames.empty()
        && _s_frames.back()->symbolic_tracking_enabled();
  }

  const ZeroFrame *marker_owner_frame() const;
  bool is_current_frame(const ZeroFrame *frame) const;

  /**
   * get index-th ShadowFrame from top
   * no inline here, for debugging
   */
  ShadowFrame &get_frame(int index) {
    int size = _s_frames.size();
    assert(index < size, "invalid index");
    return *_s_frames.at(size - 1 - index);
  }

  void push(ZeroFrame *callee_frame, ZeroFrame *caller_frame,
            bool symbolic_tracking_enabled);

  void pop(ZeroFrame *zero_frame);

};

#endif

#endif // SHARE_VM_CONCOLIC__SHADOW_SHADOWSTACK_HPP
