#ifdef ENABLE_CONCOLIC

#include "concolic/shadow/shadowFrame.hpp"
#include "runtime/frame.inline.hpp"

ShadowFrame::ShadowFrame(frame &fr)
    : _zero_frame(fr.zeroframe()), _symbolic_tracking_enabled(true) {}

ShadowFrame::ShadowFrame(const ZeroFrame *zero_frame,
                         bool symbolic_tracking_enabled)
    : _zero_frame(zero_frame),
      _symbolic_tracking_enabled(symbolic_tracking_enabled) {}

void ShadowFrame::copy() {
  if (_zero_frame->is_interpreter_frame()) {
    const InterpreterFrame *interp_frame = _zero_frame->as_interpreter_frame();
    const interpreterState istate = interp_frame->interpreter_state();
    Method *method = istate->method();
    /**
     *  Be careful, the following methods return size in word,
     *    rather than size in parameters
     */
    int max_stack = method->max_stack();
    int max_locals = method->max_locals();

    _opr_stack.init(max_stack);
    _local_tbl.init(max_locals);

  }
  /**
   * For EntryFrame, we currently only care about reflection, which is handled by ShadowStack
   */
}

void ShadowFrame::check(ZeroFrame *zero_frame) {
  guarantee(zero_frame == this->_zero_frame, "frame should be the same");
}

#endif
