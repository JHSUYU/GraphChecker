#ifndef SHARE_VM_CONCOLIC_CONCOLICMNGR_HPP
#define SHARE_VM_CONCOLIC_CONCOLICMNGR_HPP

#include "concolic/defs.hpp"
#include "concolic/methodSymbolizer.hpp"
#include "concolic/threadContext.hpp"
#include "runtime/handles.hpp"

#include <pthread.h>
#include <string>

class Thread;

/**
 * Session membership, and the per-thread entry points into it.
 *
 * A Java thread joins the symbolic session by attaching, and leaves it by
 * detaching.  The session is opened by whichever thread attaches first and
 * closed by whichever detaches last, so it outlives any one region and any one
 * thread: expressions, object identity and handoff tokens minted anywhere in
 * it stay meaningful everywhere in it.
 *
 * A *workload session* is an explicit, thread-independent owner of that same
 * session.  Attach/detach alone makes the session's lifetime a function of
 * thread arrival and departure, so a workload whose selected threads happen to
 * be momentarily all gone -- between two regions, or after a producer thread
 * exits -- loses its arena, broker, shadow heap and versions, and the
 * next region starts a different expression universe.  openWorkloadSession()
 * takes one owning reference on the session so the "last one out closes it"
 * rule still holds while no longer being a statement about threads alone;
 * closeWorkloadSession() releases it.
 *
 * The workload's ownership is a *reference*, deliberately not a depth and not a
 * separate lifecycle state:
 *
 *   - a reference, because teardown here already is a reference-count rule
 *     ("the last owner closes"), and the workload is simply one more owner of
 *     the same session.  Nothing in detach() has to learn a second teardown
 *     condition beyond "is anyone else still holding this";
 *   - not a depth, because a workload is the outermost scope of one unit-test
 *     run.  Nesting workloads would make close() mean "maybe close", which is
 *     precisely the ambiguity an explicit lifetime exists to remove.  A second
 *     open is therefore reported as WORKLOAD_SESSION_ALREADY_OPEN and mints
 *     nothing, so one close still closes;
 *   - held apart from _session_members rather than folded into it, because
 *     that count is reported to Java as "how many Java threads are executing
 *     symbolically right now".  A non-thread owner inflating it would make
 *     that number lie.
 *
 * The workload owner is not a member: it has no ThreadContext, no shadow stack
 * and no path condition, and the thread that opened it may finish its own
 * regions, detach, and even exit while the session stays open.  Threads attach
 * and detach inside it exactly as they do without it.
 *
 * With no workload session open, every path below behaves as it did before the
 * workload session existed.
 *
 * This replaced a process-global "one region at a time" mutex that a region
 * held for its whole duration, and that a second thread's region start could
 * only trylock and be rejected by.  That rule made cross-thread and
 * cross-region symbolic flow impossible by construction, which is exactly what
 * the RPC and shared-field work needs.
 *
 * Locking:
 *   - `mutex` guards the membership count and the session state, and nothing
 *     else.  Every critical section under it is short and cannot block.
 *   - GlobalSymbolicSession::close() is deliberately called *outside* it.
 *     close() asks the VM thread for a safepoint; a thread parked on `mutex`
 *     is _thread_in_vm and would never reach that safepoint, so holding
 *     `mutex` across close() would wedge the VM.  The departing thread
 *     therefore publishes SESSION_CLOSING, drops the lock, tears the session
 *     down, and only then marks it SESSION_CLOSED.
 *   - A thread that tries to attach during SESSION_CLOSING is refused rather
 *     than made to wait, for the same reason: waiting there is what would
 *     block the safepoint.  This is the one remaining fail-closed rejection,
 *     and it is a narrow race against the last detach, not a standing rule.
 *   - Order with the other engine locks is membership -> {heap, broker} ->
 *     arena.  Attach takes membership and then the broker's table lock and the
 *     arena lock while opening; ordinary symbolic work takes the heap lock and
 *     then the arena lock.  The heap and broker locks are never held at the
 *     same time, and nothing ever runs in the reverse direction.
 */
class ConcolicMngr {
#ifdef ENABLE_CONCOLIC
public:
  enum SessionState {
    SESSION_CLOSED,
    SESSION_OPEN,
    SESSION_CLOSING
  };

  /**
   * Every answer openWorkloadSession()/closeWorkloadSession() can give other
   * than success.  Each is a named, reportable outcome: none of them is
   * undefined behaviour, and none of them tears anything down implicitly.
   */
  enum WorkloadSessionStatus {
    WORKLOAD_SESSION_OK              =  0,
    // open: a workload session is already open.  No second reference was
    // taken, so one close still closes.
    WORKLOAD_SESSION_ALREADY_OPEN    = -1,
    // close: no workload session is open.  This is also the answer to the
    // second of two closes, which makes closing idempotent.
    WORKLOAD_SESSION_NOT_OPEN        = -2,
    // close: Java threads are still attached.  Refused: the workload session
    // stays open and nothing is torn down under a live thread.  The caller is
    // one of the members if it is still inside a region of its own.
    WORKLOAD_SESSION_MEMBERS_REMAIN  = -3,
    // A previous teardown is still running.  Waiting for it would block the
    // safepoint that teardown needs, so this is refused rather than queued.
    WORKLOAD_SESSION_CLOSING         = -4
  };

  // Number of Java threads currently attached to the session.  The workload
  // session's own reference is deliberately not counted here.
  static int _session_members;
  // Whether an explicit workload session holds a reference on the session.
  static bool _workload_session_open;
  static SessionState _session_state;
  static volatile intptr_t _next_context_id;
  // Guards _session_members, _workload_session_open and _session_state.
  static pthread_mutex_t mutex;
  static __thread ThreadContext *ctx;

  /**
   * Joins this thread to the session, opening one if it is the first member.
   * Returns 0 on success, non-zero if the session is being torn down.  Already
   * attached threads succeed without changing the membership count.
   */
  static jlong attach(JavaThread *thread);
  /**
   * Releases this thread's execution state and its membership, closing the
   * session if it was the last member.
   */
  static void detach();
  static jlong next_context_id();

  /**
   * Takes the workload session's reference on the symbolic session, opening
   * one if none is open and adopting the live one otherwise.
   *
   * Returns the positive session id it now owns, or a negative
   * WorkloadSessionStatus.  While it is held, no region exit and no thread
   * detach closes the session: the arena, broker, shadow heap and field
   * versions stay live, so an expression exported by a region that has
   * finished -- on a thread that has since exited -- is still resolvable.
   *
   * The caller does not become a member and gets no execution state; it may
   * attach separately if it also wants to execute symbolically.
   */
  static jlong openWorkloadSession();
  /**
   * Releases the workload session's reference and tears the session down.
   *
   * Returns WORKLOAD_SESSION_OK, or a negative WorkloadSessionStatus.  In
   * particular it refuses with WORKLOAD_SESSION_MEMBERS_REMAIN while any Java
   * thread is still attached: a thread inside a region owns live shadow slots
   * and expressions, and freeing the arena under it is exactly the corruption
   * the session lifetime exists to prevent.  Closing when nothing is open, and
   * closing twice, both answer WORKLOAD_SESSION_NOT_OPEN and change nothing.
   */
  static jlong closeWorkloadSession();
  /**
   * The session facts Java needs to check a workload's lifetime: the current
   * session id, the number of attached Java threads, whether a workload
   * session holds the session open, and this thread's own membership.  One
   * consistent snapshot, taken under one lock.
   */
  static std::string getWorkloadSessionStatus();
  // One coherent read of everything `mutex` guards, plus the session id that
  // is only meaningful while the state is SESSION_OPEN.  Reporting these
  // separately would let a report claim a member count from one session and an
  // id from another.
  static void session_snapshot(int *members, bool *workload_open,
                               SessionState *state, jlong *session_id);
  static const char *session_state_name(SessionState state);

  static jlong startConcolicRegion(JavaThread *thread, const char *region_id,
                                   const char *task_id);
  /** Exact VM thread-context identity owning the current region. */
  static jlong currentContextId();
  /** Session-global identity of the current region-frame entry. */
  static jlong currentRegionEnterEventId();
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
  // Same-JVM symbolic value handoff.  Defined in expressionBroker.cpp next to
  // the broker that owns the exported expressions.  exportExpression returns
  // a positive opaque token, or a negative ExpressionBroker::HandoffStatus;
  // attachExpression returns the positive export endpoint identity it
  // attached, or a negative status. Session close reclaims every handle; no
  // VM pointer ever reaches Java.
  //
  // Each call also reports its session-global boundary identity through its
  // optional out-parameter. Both endpoint identities are explicit because one
  // export may be attached at several receivers. The out-parameter is written
  // only on success and may be NULL.
  static jlong exportExpression(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor, jlong *export_event_out);
  static jlong attachExpression(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor, jlong handle, jlong *attach_event_out);
  // One half-open index range of this thread's single append-only path
  // condition, as its conditions.  This is how a selected branch hook reads
  // back the exact predicate its recorded condition indices name; the region
  // summary deliberately omits the whole sequence.
  static std::string getPathConditionRange(jint start, jint end);

  // Shared-carrier selection and evidence.  Defined in sharedFieldVersions.cpp
  // next to the store that owns the versions.
  //
  // Selecting a location is what makes it versioned; nothing is versioned by
  // default, because the field hooks fire on every field of every shadowed
  // object and a bounded analysis cannot pay for state it will not ask about.
  // A positive return is the INITIAL fieldVersionId, zero means the location
  // was already selected, and a negative value is a
  // SharedFieldVersions::SelectStatus refusal.
  //
  // `owner` is the receiver for an instance field and the declaring class's
  // Class object for a static one; `index` selects one element of a
  // fixed-shape array.
  static jlong selectSharedFieldCarrier(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor);
  static jlong armSharedPrimitiveFieldRead(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor, jlong value_bits);
  static jlong confirmSharedPrimitiveFieldRead(jlong token);
  static jlong selectSharedElementCarrier(Handle array, jint index);
  /**
   * Selects one supported associative container's *whole state* as a carrier.
   *
   * A map has no stable per-member slot, so `selectSharedElementCarrier`'s
   * (owner, index) addressing does not apply to one.  What a map does have is
   * an immutable state per mutation, and that is what is versioned here: a
   * selected mutation publishes the state it produced, and a selected
   * `get`/`containsKey` binds to the state it may have observed.  Selecting
   * also roots the container's symbolic state and records an INITIAL version
   * holding it, so the state a query observes before any tracked mutation is
   * an ordinary candidate rather than a hole.
   *
   * The map and every view of it (`keySet`, `values`, `entrySet`, and their
   * iterators) are one location.
   *
   * @return a positive INITIAL version id, 0 if already selected, or a
   *         negative SharedFieldVersions::SelectStatus refusal
   */
  static jlong selectSharedMapCarrier(Handle map);
  static std::string getSharedFieldVersions(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor);
  static std::string getSharedElementVersions(Handle array, jint index);
  /** getSharedFieldVersions for one selected container's whole state. */
  static std::string getSharedMapVersions(Handle map);

  static bool trackContainerExpression(Handle container,
                                       const char *prefix);
  /** Members past which an initial snapshot keeps the opaque state root. */
  static int initialSnapshotMaxEntries();

  /**
   * What one initial-snapshot offer did.
   *
   * This used to be a bool, and three different situations answered `true`:
   * the chain was installed, a recorded mutation history for the container
   * was kept instead, and the content was refused over the entry bound.  The
   * caller mapped all three to "snapshot installed", so a carrier whose
   * INITIAL version carried no base content at all was published as though it
   * carried a complete one - a free INITIAL arm the solver then has to search
   * over, which is what turns one Boolean root into twelve 180 s timeouts.
   *
   * The values are stable: they cross the JNI boundary as the int
   * `System.snapshotContainerExpression` answers, and
   * `InitialContainerSnapshot` names the same numbers on the Java side.  0
   * and 1 keep the old bool's meaning so an older runtime paired with a newer
   * VM still reads a refusal as a refusal.
   */
  enum InitialSnapshotAnswer {
    // Nothing was stated and nothing is claimed: no active context, a null or
    // mis-shaped argument, or a container this engine does not carry.
    SNAPSHOT_NOT_SELECTABLE = 0,
    // The chain was installed; the container's state now states its content.
    SNAPSHOT_INSTALLED = 1,
    // The container already carried a recorded mutation history and the
    // content it started with cannot be recovered from that record, so the
    // history was kept and the base is unknown.
    SNAPSHOT_KEPT_EXISTING_HISTORY = 2,
    // The content held more members than the entry bound admits, so the
    // opaque state root was kept and the refusal recorded.
    SNAPSHOT_REFUSED_OVER_BOUND = 3,
    // The container already carried a recorded mutation history, that history
    // was undone against the offered content to recover the base, and the
    // history was rebuilt on top of the stated base.  Both facts survive: the
    // content is stated and the mutations still relate the container to this
    // activation's inputs.
    SNAPSHOT_REBASED_UNDER_HISTORY = 4,
    // An earlier offer already stated this container's content.
    SNAPSHOT_ALREADY_STATED = 5
  };

  static jint snapshotContainerExpression(
      Handle container, Handle keys, Handle values, jint kind);
  static std::string getRegionSummary();
  static void symbolize(Handle handle, const char* prefix);
  static void symbolizeField(Handle handle, const char* field_name,
                             const char* prefix);
  static void symbolizeExactField(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor, const char *prefix);
  static void observeExactPrimitiveField(
      Handle owner, const char *declaring_class, const char *field_name,
      const char *descriptor);
  inline static bool has_symbolized_method() {
    return ctx && !ctx->is_aborted() && ctx->is_symbolizing_method();
  }

  inline static bool has_active_context() {
    return ctx != NULL && !ctx->is_aborted();
  }

  inline static bool can_do_concolic() {
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
  inline static bool can_explicitly_symbolize() {
    return ctx && !ctx->is_aborted() && !ctx->is_symbolizing_method();
  }

  // A paused observation subtree must keep the Zero/shadow frame structure
  // balanced even though its bytecodes do not propagate symbolic state.
  inline static bool can_maintain_shadow_stack() {
    return ctx && !ctx->is_aborted() && !ctx->is_symbolizing_method();
  }

  inline static void warning_reach_unhandled_bytecode(const char *bytecode) {
    if (can_do_concolic()) {
      tty->print_cr("[WARNING] reach unhandled bytecode %s!!!!", bytecode);
    }
  }

  inline static void record_path_condition(Expression *sym_exp) {
    ctx->record_path_condition(sym_exp);
  }

  inline static void record_branch_condition(
      Expression *sym_exp, bool outcome, int opcode) {
    ctx->record_branch_condition(sym_exp, outcome, opcode);
  }

  inline static void record_branch_conditions(
      const exp_list_t &expressions, bool outcome, int opcode) {
    ctx->record_branch_conditions(expressions, outcome, opcode);
  }

#else
  static jlong endConcolic();
#endif // ENABLE_CONCOLIC
};

#endif // SHARE_VM_CONCOLIC_CONCOLICMNGR_HPP
