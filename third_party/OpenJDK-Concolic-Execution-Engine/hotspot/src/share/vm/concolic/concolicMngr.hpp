#ifndef SHARE_VM_CONCOLIC_CONCOLICMNGR_HPP
#define SHARE_VM_CONCOLIC_CONCOLICMNGR_HPP

#include "concolic/defs.hpp"
#include "concolic/methodSymbolizer.hpp"
#include "concolic/threadContext.hpp"
#include "runtime/handles.hpp"

#include <pthread.h>
#include <string>

class Thread;

class ConcolicMngr {
#ifdef ENABLE_CONCOLIC
public:
  static volatile int _num_threads_in_concolic;
  static jlong _next_context_id;
  static pthread_mutex_t mutex;
  static __thread ThreadContext *ctx;

  static jlong startConcolic(JavaThread *thread);
  static jlong startConcolicRegion(JavaThread *thread, const char *region_id,
                                   const char *task_id);
  static jlong endConcolic();
  static void abandonPendingBranchForException(Thread *thread);
  static void abortCurrentContext(const char *reason);
  static void cleanupAbandonedContext(JavaThread *thread);
  static void pausePathConditionRecording();
  static void resumePathConditionRecording();
  static jlong markBranch(const char *site_id, int occurrence);
  static std::string getBranchEvents();
  static std::string getSymbolicExpression(Handle handle);
  static std::string getSymbolicFieldExpression(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor, Handle concrete_value);
  static bool trackContainerExpression(Handle container,
                                       const char *prefix);
  static bool snapshotContainerExpression(
      Handle container, Handle keys, Handle values, jint kind);
  static std::string getRegionSummary();
  static void symbolize(Handle handle);
  static void symbolize(Handle handle, const char* prefix);
  static void symbolizeField(Handle handle, const char* field_name,
                             const char* prefix);
  static void symbolizeExactField(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor, const char *prefix);
  static void observeExactPrimitiveField(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor);
  static void symbolizeMethod(Handle holder_name_handle,
                              Handle callee_name_handle);
  static void printSymExp(Handle handle);
  static void recordStmtObj(Handle stmt, Handle obj);
  static void recordPersistentObj(Handle obj);

  /* let compiler not optimize this  code!! */
  inline static bool __attribute__((optimize("O0"))) has_symbolized_method() {
    return ctx && !ctx->is_aborted() && ctx->is_symbolizing_method();
  }

  inline static bool __attribute__((optimize("O0"))) has_active_context() {
    return ctx != NULL && !ctx->is_aborted();
  }
  
  /* let compiler not optimize this  code!! */
  inline static bool __attribute__((optimize("O0"))) can_do_concolic() {
    return ctx && !ctx->is_aborted()
        && ctx->path_condition_pause_depth() == 0
        && !ctx->is_symbolizing_method()
        && ctx->symbolic_tracking_enabled();
  }

  // Explicit System.symbolize* calls remain valid inside a paused Java
  // bookkeeping subtree.  The native entry frame itself is pushed while the
  // pause is active and is therefore deliberately marked non-tracking; do
  // not reject the explicit VM operation based on that frame-local flag.
  // Its native implementation temporarily enables PC recording only while
  // the VM mutates symbolic state, then restores the caller's pause depth.
  inline static bool __attribute__((optimize("O0"))) can_explicitly_symbolize() {
    return ctx && !ctx->is_aborted() && !ctx->is_symbolizing_method();
  }

  // A paused observation subtree must keep the Zero/shadow frame structure
  // balanced even though its bytecodes do not propagate symbolic state.
  inline static bool __attribute__((optimize("O0"))) can_maintain_shadow_stack() {
    return ctx && !ctx->is_aborted() && !ctx->is_symbolizing_method();
  }

  inline static bool __attribute__((optimize("O0"))) should_try_handle_method() {
    return can_do_concolic()
        && ctx->get_method_symbolizer().has_handling_methods();
  }

  static bool has_callback() {
    return can_do_concolic() && ctx->has_callback();
  }

  inline static void warning_reach_unhandled_bytecode(const char *bytecode) {
    if (can_do_concolic()) {
      tty->print_cr("[WARNING] reach unhandled bytecode %s!!!!", bytecode);
    }
  }

  /** unoptimize for breakpoint */
  inline static void __attribute__((optimize("O0"))) record_path_condition(Expression *sym_exp) {
    ctx->record_path_condition(sym_exp);

  }

  inline static void __attribute__((optimize("O0"))) record_branch_condition(
      Expression *sym_exp, bool outcome, int opcode) {
    ctx->record_branch_condition(sym_exp, outcome, opcode);
  }

  inline static void __attribute__((optimize("O0"))) record_branch_conditions(
      const exp_list_t &expressions, bool outcome, int opcode) {
    ctx->record_branch_conditions(expressions, outcome, opcode);
  }

  static void method_enter_callback(ZeroFrame *caller_frame, ZeroFrame *callee_frame) {

  }

  static void method_exit_callback(ZeroFrame *caller_frame) {
    ctx->get_method_symbolizer().method_exit(caller_frame);
  }
#else
  static jlong startConcolic();
  static jlong endConcolic();
  static void symbolize(Handle handle);
  static void symbolizeMethod(Handle holder_name_handle,
                              Handle callee_name_handle);
  static void recordStmtObj(Handle stmt, Handle obj) {};
  static void recordPersistentObj(Handle obj) {};
#endif // ENABLE_CONCOLIC
};

#endif // SHARE_VM_CONCOLIC_CONCOLICMNGR_HPP
