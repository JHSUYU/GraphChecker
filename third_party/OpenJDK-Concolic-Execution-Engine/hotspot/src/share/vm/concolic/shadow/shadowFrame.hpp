#ifndef SHARE_VM_CONCOLIC_SHADOW_SHADOWFRAME_HPP
#define SHARE_VM_CONCOLIC_SHADOW_SHADOWFRAME_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/shadow/shadowTable.hpp"
#include "runtime/frame.inline.hpp"

class ShadowFrame {

private:
  const ZeroFrame *_zero_frame;
  bool _symbolic_tracking_enabled;
  // Pushed while recording was paused: no expression enters it from its
  // caller or leaves it to its caller (ShadowStack::push/pop), whether or
  // not it tracks once the pause lifts in it (the base pause alone).
  bool _concrete_boundary;
  ShadowTable _opr_stack;
  ShadowTable _local_tbl;

public:
  explicit ShadowFrame(frame &fr);
  ShadowFrame(const ZeroFrame *zero_frame, bool symbolic_tracking_enabled,
              bool concrete_boundary);
  ~ShadowFrame() {}

  void copy();
  
  inline ShadowTable& get_opr_stack() { return _opr_stack; }
  inline ShadowTable& get_local_tbl() { return _local_tbl; }
  inline const ZeroFrame* get_zero_frame() { return _zero_frame; }
  inline bool symbolic_tracking_enabled() const {
    return _symbolic_tracking_enabled;
  }
  inline bool concrete_boundary() const { return _concrete_boundary; }
  void check(ZeroFrame *zero_frame);

};

#endif

#endif // SHARE_VM_CONCOLIC_SHADOW_SHADOWFRAME_HPP
