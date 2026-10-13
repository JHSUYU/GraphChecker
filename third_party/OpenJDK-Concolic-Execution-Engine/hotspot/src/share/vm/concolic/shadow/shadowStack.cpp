#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/shadow/shadowStack.hpp"
#include "runtime/frame.inline.hpp"
#include "runtime/thread.hpp"

#include <algorithm>

ShadowStack::ShadowStack(JavaThread *jt)
    : _next_reflection_token(0), _reflection_ret_exp(NULL) {
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

    for (; !sfs.is_done(); sfs.next()) {
      ShadowFrame *s_frame = new ShadowFrame(*sfs.current());
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
  for (std::vector<PendingReflection *>::iterator iter =
           _pending_reflections.begin();
       iter != _pending_reflections.end(); ++iter) {
    delete *iter;
  }
  _pending_reflections.clear();
}

void ShadowStack::push(ZeroFrame *callee_frame, ZeroFrame *caller_frame,
                       bool symbolic_tracking_enabled,
                       bool concrete_boundary) {
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
  bool boundary = concrete_boundary || !effective_tracking;
  ShadowFrame *s_frame = new ShadowFrame(callee_frame, effective_tracking,
                                         boundary);
  s_frame->copy();
  if (boundary) {
    // Paused and method-symbolized callees still perform real JVM stack
    // transitions.  Consume their caller arguments even though no expression
    // is propagated into the callee frame: a non-tracking one, or one pushed
    // under the base pause alone, which tracks once the pause lifts in it
    // (a doors-only occurrence's door decided in a callee).
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
        int parameter_slots = callee_method->size_of_parameters();
        if (!callee_method->is_native()) {
          s_frame->get_local_tbl().copy_entries(
              last_opr_stack, begin_offset, 0,
              parameter_slots);
        }
        last_opr_stack.clear_slots(begin_offset,
                                   parameter_slots);
      }
    }
  } else if (callee_frame->is_entry_frame()) {
    JavaCallWrapper *call_wrapper =
        *callee_frame->as_entry_frame()->call_wrapper();
    Method *entry_target = call_wrapper == NULL
        ? NULL : call_wrapper->callee_method();
    if (entry_target != NULL) {
      JavaThread *java_thread = ConcolicMngr::ctx->get_thread();
      ZeroStack *zero_stack = java_thread->zero_stack();
      int stack_words = (intptr_t *) callee_frame - zero_stack->sp() - 2;
      take_reflection_stack(entry_target, stack_words,
                            s_frame->get_opr_stack());
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
  // deliberately not copied back into the symbolic caller state; nor are a
  // frame's pushed under the base pause, which ran paused but where a door
  // decided (its shadow is stale there).
  if (s_frame->concrete_boundary()) {
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
      if (is_java_primitive(type)
          && !ConcolicMngr::ctx->get_thread()->has_pending_exception()) {
        this->set_reflection_ret_exp(opr_stack.get_slot(type2size[type] - 1));
      }
    }
  }

  delete s_frame;
}

void ShadowStack::push_callback(ZeroFrame *callee_frame,
                                const std::vector<int> &anchors,
                                const exp_list_t &seeds) {
  ShadowFrame *s_frame = new ShadowFrame(callee_frame, true, false);
  s_frame->copy();
  for (size_t index = 0; index < anchors.size() && index < seeds.size();
       ++index) {
    if (seeds[index] != NULL) {
      s_frame->get_local_tbl().set_slot(anchors[index], seeds[index]);
    }
  }
  _s_frames.push_back(s_frame);
}

Expression *ShadowStack::pop_callback(ZeroFrame *callee_frame,
                                      BasicType result_type) {
  ShadowFrame *s_frame = _s_frames.back();
  s_frame->check(callee_frame);
  ConcolicMngr::ctx->cancel_pending_branch_for_frame(callee_frame);
  _s_frames.pop_back();
  Expression *result = NULL;
  if (result_type != T_VOID) {
    // Where pop() finds a returning frame's result.
    interpreterState istate =
        callee_frame->as_interpreter_frame()->interpreter_state();
    const int result_slots = type2size[result_type];
    intptr_t *callee_result = istate->stack() + result_slots;
    const int offset = istate->stack_base() - callee_result - 1;
    result = s_frame->get_opr_stack().get_slot(offset + result_slots - 1);
  }
  delete s_frame;
  return result;
}

jlong ShadowStack::register_reflection_call(Method *target, int entry_words,
                                            ShadowTable &carrier) {
  guarantee(target != NULL, "reflection target must be present");
  guarantee(entry_words >= 0 && carrier.size() >= entry_words,
            "reflection carrier must cover its argument footprint");
  guarantee(_next_reflection_token < max_jlong,
            "reflection token overflow");
  jlong token = ++_next_reflection_token;
  PendingReflection *pending =
      new PendingReflection(token, target, entry_words);
  pending->carrier.swap(carrier);
  _pending_reflections.push_back(pending);
  return token;
}

bool ShadowStack::take_reflection_stack(Method *target, int entry_words,
                                        ShadowTable &destination) {
  if (_pending_reflections.empty()
      || _pending_reflections.back()->target != target) {
    return false;
  }
  PendingReflection *pending = _pending_reflections.back();
  guarantee(entry_words == pending->entry_words,
            "reflection argument footprint must match its target entry");
  destination.swap(pending->carrier);
  _pending_reflections.pop_back();
  delete pending;
  return true;
}

bool ShadowStack::cancel_reflection_call(jlong token) {
  guarantee(token != 0, "reflection token must be present");
  for (int i = (int)_pending_reflections.size() - 1; i >= 0; --i) {
    PendingReflection *pending = _pending_reflections[i];
    if (pending->token != token) {
      continue;
    }
    guarantee(i == (int)_pending_reflections.size() - 1,
              "reflection calls must be cancelled in LIFO order");
    _pending_reflections.pop_back();
    delete pending;
    return true;
  }
  return false;
}

#endif
