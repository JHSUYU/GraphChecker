#ifdef ENABLE_CONCOLIC

#include "nativeGetPrimitiveHandler.hpp"
#include "interpreterFrame_zero.hpp"
#include "runtime/thread.hpp"

std::set<std::string> NativeGetPrimitiveHandler::handle_method_name_sigs = init_handle_method_name_sigs();

std::set<std::string> NativeGetPrimitiveHandler::init_handle_method_name_sigs() {
  std::set<std::string> name_sigs;
  name_sigs.insert(std::string("sun.misc.Unsafe.getByte(Ljava/lang/Object;J)B"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getChar(Ljava/lang/Object;J)C"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getDouble(Ljava/lang/Object;J)D"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getFloat(Ljava/lang/Object;J)F"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getInt(Ljava/lang/Object;J)I"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getLong(Ljava/lang/Object;J)J"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getShort(Ljava/lang/Object;J)S"));
  name_sigs.insert(std::string("sun.misc.Unsafe.getBoolean(Ljava/lang/Object;J)Z"));

  return name_sigs;
}

bool NativeGetPrimitiveHandler::target(const std::string& name_sig) {
  return handle_method_name_sigs.find(name_sig) != handle_method_name_sigs.end();
}

void NativeGetPrimitiveHandler::handle_native(intptr_t *locals,
                                              BasicType result_type,
                                              int parameter_slots) {
  oop obj = reinterpret_cast<oop&>(locals[-1]);
  jlong offset = (jlong)locals[-3];

  int result_slots = type2size[result_type];
  assert(result_slots == 1 || result_slots == 2,
         "Unsafe primitive result occupies one or two stack words");
  int result_begin = 0;
  ZeroFrame *caller = ConcolicMngr::ctx->get_thread()->top_zero_frame();
  if (caller != NULL && caller->is_interpreter_frame()) {
    interpreterState caller_istate =
        caller->as_interpreter_frame()->interpreter_state();
    result_begin = caller_istate->stack_base() - locals - 1;
  }
  // Zero's native shadow frame does not copy or consume caller arguments.
  // The concrete interpreter pops them only after that frame is gone, so do
  // the equivalent shadow transition here before reusing the result slots.
  ConcolicMngr::ctx->clear_stack_words(result_begin, parameter_slots);
  if (ConcolicMngr::ctx->get_thread()->has_pending_exception()) return;

  SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(obj);
  Expression *exp = sym_inst == NULL ? NULL : sym_inst->get(offset);
  // Native returns bypass the ordinary bytecode producer.  They must still
  // obey the same stack layout and clear stale state for concrete results.
  ConcolicMngr::ctx->set_stack_value(
      result_begin + result_slots - 1, result_slots, exp);
}

#endif
