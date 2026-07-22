#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/shadow/shadowStack.hpp"
#include "runtime/frame.inline.hpp"
#include "runtime/thread.hpp"

#include <algorithm>

ShadowStack::ShadowStack(JavaThread *jt) : _reflection_ret_exp(NULL) {
  _s_frames.reserve(DEFAULT_MAX_STACK_DEPTH);

  if (jt->zero_stack()->sp() && jt->top_zero_frame()) {
    bool has_last_Java_frame = jt->has_last_Java_frame();
    if (!has_last_Java_frame)
      jt->set_last_Java_frame();

    // If the top frame is a Shark frame and the frame anchor isn't
    // set up then it's possible that the information in the frame
    // is garbage: it could be from a previous decache, or it could
    // simply have never been written.  So we print a warning...
    StackFrameStream sfs(jt);
    if (!has_last_Java_frame && !sfs.is_done()) {
      assert(!sfs.current()->zeroframe()->is_shark_frame(),
             "top frame might be junk");
    }

    for (int frame_index = 0; !sfs.is_done(); sfs.next(), frame_index++) {
      ShadowFrame *s_frame = new ShadowFrame(*sfs.current(), frame_index);
      s_frame->copy();
      _s_frames.push_back(s_frame);
    }
    // reverse the stack
    std::reverse(_s_frames.begin(), _s_frames.end());

    // Reset the frame anchor if necessary
    if (!has_last_Java_frame)
      jt->reset_last_Java_frame();
  }
}

const ZeroFrame *ShadowStack::marker_owner_frame() const {
  // markConcolicBranch is itself a native call.  Bind its one-shot marker to
  // the closest non-native Java caller so branches in nested accessors or VM
  // exception construction cannot steal it.
  for (ShadowFrames::const_reverse_iterator iter = _s_frames.rbegin();
       iter != _s_frames.rend(); ++iter) {
    const ZeroFrame *candidate = (*iter)->get_zero_frame();
    if (candidate != NULL && candidate->is_interpreter_frame()) {
      Method *method = candidate->as_interpreter_frame()
          ->interpreter_state()->method();
      if (method != NULL && !method->is_native()) {
        return candidate;
      }
    }
  }
  return NULL;
}

bool ShadowStack::is_current_frame(const ZeroFrame *frame) const {
  return frame != NULL && !_s_frames.empty()
      && _s_frames.back()->get_zero_frame() == frame;
}

ShadowStack::~ShadowStack() {
  for (ShadowFrames::iterator iter = _s_frames.begin(); iter != _s_frames.end();
       ++iter) {
    delete *iter;
  }
  _s_frames.clear();
}

void ShadowStack::push(ZeroFrame *callee_frame, ZeroFrame *caller_frame,
                       intptr_t *sp, bool symbolic_tracking_enabled) {
  // ConcolicMngr::ctx->print_stack_trace();
  // ConcolicMngr::ctx->get_shadow_stack().print();

  if (_s_frames.empty()) {
    // There is no sound caller state from which to seed this frame.  This can
    // only occur after the region owner has escaped without a matching
    // finish; permanently disable the context instead of rebasing arbitrary
    // JVM cleanup frames onto stale symbolic state.
    ConcolicMngr::abortCurrentContext("SHADOW_STACK_HAS_NO_CALLER");
    return;
  }

  _s_frames.back()->check(caller_frame);

  ShadowFrame &last_s_frame = get_frame(0);
  ShadowTable &last_opr_stack = last_s_frame.get_opr_stack();
  bool effective_tracking = symbolic_tracking_enabled
      && last_s_frame.symbolic_tracking_enabled();
  ShadowFrame *s_frame = new ShadowFrame(callee_frame, sp, 8,
                                         effective_tracking);
  s_frame->copy();
  if (!effective_tracking) {
    // Paused and method-symbolized callees still perform real JVM stack
    // transitions.  Consume their caller arguments even though no expression
    // is propagated into the deliberately non-tracking callee frame.
    if (callee_frame->is_interpreter_frame()) {
      interpreterState callee_istate =
          callee_frame->as_interpreter_frame()->interpreter_state();
      int parameter_slots = callee_istate->method()->size_of_parameters();
      if (parameter_slots > 0 && last_opr_stack.size() != 0) {
        int begin_offset = 0;
        if (caller_frame->is_interpreter_frame()) {
          interpreterState caller_istate =
              caller_frame->as_interpreter_frame()->interpreter_state();
          begin_offset = caller_istate->stack_base()
              - callee_istate->locals() - 1;
        }
        last_opr_stack.clear_slots(begin_offset, parameter_slots);
      }
    }
    _s_frames.push_back(s_frame);
    return;
  }
  if (callee_frame->is_interpreter_frame()) {
    interpreterState callee_istate =
        callee_frame->as_interpreter_frame()->interpreter_state();
    Method *callee_method = callee_istate->method();
    if (caller_frame->is_interpreter_frame()) {
      interpreterState caller_istate =
          caller_frame->as_interpreter_frame()->interpreter_state();
      /**
       * At this time, `istate->locals()` points to the start of locals,
       * while `caller_istate->stack()` points to end of locals
       */
      int begin_offset =
          caller_istate->stack_base() - callee_istate->locals() - 1;
      int end_offset =
          caller_istate->stack_base() - caller_istate->stack() - 1;
      if (!callee_method->is_native()) {
        s_frame->get_local_tbl().copy_entries(last_opr_stack, begin_offset, 0,
                                              end_offset - begin_offset);
      }
      // Every invocation consumes the complete caller argument footprint.
      // Native callees have no bytecode locals to populate, but their dead
      // argument slots must still be cleared before a result reuses them.
      last_opr_stack.clear_slots(begin_offset,
                                 end_offset - begin_offset);
    } else if (caller_frame->is_entry_frame()) {
      if (last_opr_stack.size() != 0) {
        int begin_offset = 0;
        int end_offset = (intptr_t *) caller_frame
            - (intptr_t *) callee_frame - 3;
        if (!callee_method->is_native()) {
          s_frame->get_local_tbl().copy_entries(
              last_opr_stack, begin_offset, 0,
              end_offset - begin_offset);
        }
        last_opr_stack.clear_slots(begin_offset,
                                   end_offset - begin_offset);
      }
    }
  } else if (callee_frame->is_entry_frame()) {
    ShadowTable &reflection_stack = ConcolicMngr::ctx->get_shadow_stack().get_reflection_stack();
    if (reflection_stack.size() != 0) {
      JavaThread *java_thread = ConcolicMngr::ctx->get_thread();
      ZeroStack *zero_stack = java_thread->zero_stack();
      int stack_words = (intptr_t *) callee_frame - zero_stack->sp() - 2;
      assert(stack_words == reflection_stack.size(), "should be");
      s_frame->get_opr_stack().swap(reflection_stack);
    }
  }
  _s_frames.push_back(s_frame);
}

void ShadowStack::pop(ZeroFrame *callee_frame) {
  /**
   * This is a workaround when we do not suppot shadow stack completely
   */
  assert(!_s_frames.empty(), "not empty");

  /**
   * do pop
   */
  ShadowFrame *s_frame = _s_frames.back();
  s_frame->check(callee_frame);
  // A marker is owned by one concrete Java activation.  Invalidate it before
  // releasing that frame address so a later activation cannot reuse the
  // address and accidentally claim the stale marker.
  ConcolicMngr::ctx->cancel_pending_branch_for_frame(callee_frame);
  _s_frames.pop_back();

  if (_s_frames.empty()) {
    delete s_frame;
    ConcolicMngr::abortCurrentContext("SHADOW_STACK_EXHAUSTED");
    return;
  }

  // Observation helpers entered while concolic propagation is paused still
  // need a structural frame so push/pop remains balanced.  Their values are
  // deliberately not copied back into the symbolic caller state.
  if (!s_frame->symbolic_tracking_enabled()) {
    if (callee_frame->is_interpreter_frame()) {
      interpreterState callee_istate =
          callee_frame->as_interpreter_frame()->interpreter_state();
      int result_slots = type2size[callee_istate->method()->result_type()];
      if (result_slots > 0) {
        ShadowTable &caller_stack = get_last_frame().get_opr_stack();
        ZeroFrame *caller_frame = callee_frame->next();
        if (caller_frame->is_interpreter_frame()) {
          interpreterState caller_istate =
              caller_frame->as_interpreter_frame()->interpreter_state();
          int result_begin = caller_istate->stack_base()
              - callee_istate->locals() - 1;
          caller_stack.clear_slots(result_begin, result_slots);
        } else if (caller_frame->is_entry_frame()
                   && caller_stack.size() != 0) {
          caller_stack.clear_slots(0, result_slots);
        }
      }
    }
    delete s_frame;
    return;
  }

  ShadowTable &opr_stack = s_frame->get_opr_stack();
  ShadowTable &next_opr_stack = get_last_frame().get_opr_stack();

  /**
   * return result from current opr_stack to locals
   */
  if (callee_frame->is_interpreter_frame()) {
    interpreterState callee_istate =
        callee_frame->as_interpreter_frame()->interpreter_state();
    Method *callee_method = callee_istate->method();
    if (callee_method->is_native()) {
      int result_slots = type2size[callee_method->result_type()];
      if (result_slots > 0) {
        assert(result_slots == 1 || result_slots == 2,
               "a JVM native result occupies one or two words");
        ZeroFrame *caller_frame = callee_frame->next();
        if (caller_frame->is_interpreter_frame()) {
          interpreterState caller_istate =
              caller_frame->as_interpreter_frame()->interpreter_state();
          int caller_result_offset = caller_istate->stack_base()
              - callee_istate->locals() - 1;
          next_opr_stack.clear_slots(caller_result_offset, result_slots);
        } else if (caller_frame->is_entry_frame()
                   && next_opr_stack.size() != 0) {
          next_opr_stack.clear_slots(0, result_slots);
        }
      }
      // A specialized native handler may install a symbolic result after the
      // concrete interpreter has popped arguments.  Until then the native
      // result is concrete and its complete footprint must stay empty.
      delete s_frame;
      return;
    }
    BasicType res_type = callee_method->result_type();
    if (res_type != T_VOID) {
      // An exceptional unwind has no Java return value on the callee operand
      // stack, regardless of its declared result type.  Normal object and
      // array returns carry a one-word expression edge just like category-1
      // primitives; long/double retain their exact two-word footprint.
      if (callee_istate->thread()->has_pending_exception()) {
        delete s_frame;
        return;
      }
      // here `result` describes whatever returned
      int result_slots = type2size[res_type];
      assert(result_slots == 1 || result_slots == 2,
             "a non-void JVM result occupies one or two words");

      intptr_t *callee_result = callee_istate->stack() + result_slots;
      /**
       * TODO: check callee_opr_stack_offset should be only 0 or 1?
       */
      int callee_opr_stack_offset =
          callee_istate->stack_base() - callee_result - 1;
      /**
       * Previously, we find a bug that causes callee_opr_stack_offset < 0,
       * it seems to be related with athrow, and thus we wrote an if statement
       * that checks thread()->has_pending_exception().
       *
       * But the foundamental reason why exception causes stack() + 1== stack() is not dedtermined.
       * Therefore, I use the following guarantee, and decide to check the reason when the guarantee is violated
       */
      guarantee(callee_opr_stack_offset >= 0, "should be");

      ZeroFrame *caller_frame = callee_frame->next();
      if (caller_frame->is_interpreter_frame()) {
        interpreterState caller_istate =
            caller_frame->as_interpreter_frame()->interpreter_state();
        intptr_t *caller_result = callee_istate->locals();
        /**
         * TODO: Reduandant calculation in MethodSymbolizerHandle
         */
        int caller_opr_stack_offset =
            caller_istate->stack_base() - caller_result - 1;
        next_opr_stack.copy_entries(opr_stack, callee_opr_stack_offset,
                                    caller_opr_stack_offset, result_slots);
      } else if (caller_frame->is_entry_frame()) {
        if (next_opr_stack.size() != 0) {
          next_opr_stack.copy_entries(opr_stack, callee_opr_stack_offset,
                                      0, result_slots);
        }
      }

      // tty->print_cr(CL_GREEN"copy from %d to %d with size=%d"CNONE,
      // callee_opr_stack_offset, caller_opr_stack_offset, result_slots);
    }
  } else if (callee_frame->is_entry_frame()) {
    if (opr_stack.size() != 0) {
      JavaCallWrapper* call_wrapper = *callee_frame->as_entry_frame()->call_wrapper();
      Method* callee_method = call_wrapper->callee_method();
      BasicType type = callee_method->result_type();
      if (is_java_primitive(type)) {
        this->set_reflection_ret_exp(opr_stack.get_slot(type2size[type] - 1));
      }
    }
  }

  delete s_frame;
}

ShadowTable *ShadowStack::init_reflection_stack(int max_slot_size) {
  assert(_reflection_stack.size() == 0, "should be");
  _reflection_stack.init(max_slot_size);
  return &_reflection_stack;
}

void ShadowStack::print_origin() {
  for (ShadowFrames::reverse_iterator iter = _s_frames.rbegin();
       iter != _s_frames.rend(); ++iter) {
    ShadowFrame *s_frame = *iter;
    s_frame->print_origin();
  }
}

void ShadowStack::print() {
  tty->print_cr("ShadowStack: ");
  for (ShadowFrames::reverse_iterator iter = _s_frames.rbegin();
       iter != _s_frames.rend(); ++iter) {
    ShadowFrame *s_frame = *iter;
    s_frame->print();
    tty->print("\n");
  }
}

#endif
