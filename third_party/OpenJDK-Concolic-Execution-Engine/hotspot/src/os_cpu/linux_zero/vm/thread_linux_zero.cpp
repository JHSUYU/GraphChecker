/*
 * Copyright (c) 1997, 2010, Oracle and/or its affiliates. All rights reserved.
 * Copyright 2009, 2010 Red Hat, Inc.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "concolic/concolicMngr.hpp"
#include "precompiled.hpp"
#include "runtime/frame.inline.hpp"
#include "runtime/thread.inline.hpp"

void JavaThread::cache_global_variables() {
  // nothing to do
}

void JavaThread::push_zero_frame(ZeroFrame *zframe) {
  *(ZeroFrame **)zframe = _top_zero_frame;
  _top_zero_frame = zframe;
#ifdef ENABLE_CONCOLIC
//  if (_top_zero_frame && _top_zero_frame->is_interpreter_frame()) {
//    ResourceMark rm;
//    std::string name = _top_zero_frame->as_interpreter_frame()->interpreter_state()->method()->name()->as_C_string();
//    if (name == "execute") {
//      tty->print_cr("intercepted executeQuery from push zero frame, ConcolicMngr::can_do_concolic():%d", ConcolicMngr::can_do_concolic());
//    }
//  }
  // A callback a muted model call makes runs with propagation, in a frame
  // of its own (MethodSymbolizer::enter_callback).
  if (ConcolicMngr::has_symbolized_method()
      && ConcolicMngr::ctx->get_method_symbolizer().enter_callback(
             *(ZeroFrame **)zframe, _top_zero_frame)) {
    return;
  }
  if (ConcolicMngr::can_do_concolic()) {
    ConcolicMngr::ctx->get_method_symbolizer().invoke_method(
        *(ZeroFrame **)zframe, _top_zero_frame);
  }
  if (ConcolicMngr::can_maintain_shadow_stack()) {
    // A frame pushed under the base pause alone may still track once the
    // pause lifts in it (ConcolicMngr::can_track_pushed_frame).
    ConcolicMngr::ctx->get_shadow_stack().push(
        _top_zero_frame, *(ZeroFrame **)zframe,
        ConcolicMngr::can_track_pushed_frame(),
        !ConcolicMngr::can_do_concolic());
  }
#endif
}

void JavaThread::pop_zero_frame() {
#ifdef ENABLE_CONCOLIC
  ZeroFrame *temp_frame = _top_zero_frame;
#endif

  zero_stack()->set_sp((intptr_t *)_top_zero_frame + 1);
  _top_zero_frame = *(ZeroFrame **)_top_zero_frame;
#ifdef ENABLE_CONCOLIC
  // A callback's frame hands its result to the muted call that made it,
  // not to a shadow caller (MethodSymbolizer::exit_callback).
  if (ConcolicMngr::can_maintain_shadow_stack()
      && !ConcolicMngr::ctx->get_method_symbolizer().exit_callback(
             temp_frame)) {
    ConcolicMngr::ctx->get_shadow_stack().pop(temp_frame);
  }
  if (ConcolicMngr::has_symbolized_method()) {
    ConcolicMngr::ctx->get_method_symbolizer().finish_method(_top_zero_frame);
  }
#endif
}
