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

  /** Whether there is a last frame to ask about at all. */
  inline bool has_frames() const { return !_s_frames.empty(); }

  inline bool symbolic_tracking_enabled() const {
    return !_s_frames.empty()
        && _s_frames.back()->symbolic_tracking_enabled();
  }

  const ZeroFrame *marker_owner_frame() const;

  /**
   * The index of the program frame that called into the engine: the
   * topmost frame below every native frame and every frame of the engine's
   * own classes and of reflection on top of the stack -- a region's root,
   * asked at its start (ThreadContext::push_region).  -1 when none.
   */
  int program_entry_index() const;

  /** Clears the local and operand tables of every tracking frame from
   *  `index` up (ThreadContext::pause_base_recording); none for -1. */
  void clear_tracking_frames_from(int index);
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

  /**
   * `symbolic_tracking_enabled`: whether the callee may track (with its
   * caller's); `concrete_boundary`: recording is paused at the push, so the
   * callee takes no expression from its caller and hands none back.
   */
  void push(ZeroFrame *callee_frame, ZeroFrame *caller_frame,
            bool symbolic_tracking_enabled, bool concrete_boundary);

  void pop(ZeroFrame *zero_frame);

  /**
   * A callback's frame, called from a muted model body that has no shadow
   * frame of its own: nothing is copied from a caller; the local at each of
   * `anchors` is seeded with the matching `seeds` entry.
   */
  void push_callback(ZeroFrame *callee_frame, const std::vector<int> &anchors,
                     const exp_list_t &seeds);
  /**
   * Pops a callback's frame without handing its result to any caller, and
   * returns the result's shadow (NULL for `result_type` T_VOID or none).
   */
  Expression *pop_callback(ZeroFrame *callee_frame, BasicType result_type);

};

#endif

#endif // SHARE_VM_CONCOLIC__SHADOW_SHADOWSTACK_HPP
