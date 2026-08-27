#ifndef SHARE_VM_CONCOLIC_EVENTLEDGER_HPP
#define SHARE_VM_CONCOLIC_EVENTLEDGER_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/vectorClock.hpp"

#include <pthread.h>

#include <map>
#include <string>
#include <utility>
#include <vector>

/**
 * The session's record of everything that can be ordered.
 *
 * Before Phase 2 the engine had two unrelated notions of "when": a per-thread
 * branch sequence and the index of a condition inside one thread's path
 * condition.  Neither says anything about another thread, so no cross-thread
 * fact could be stated at all, and `cache->is_volatile()` was read for fencing
 * and thrown away. This class is the one place where selected causal facts now
 * live.
 *
 * ---------------------------------------------------------------------------
 * What it holds
 * ---------------------------------------------------------------------------
 *
 * Two things, and they answer different questions:
 *
 *   - a *release map* for explicit thread lifecycle channels. A started or
 *     terminating thread publishes its clock through the Thread object, and
 *     the child or joiner acquires that clock;
 *
 *   - an *event log*, one entry per ordered action, drawn from the session's
 *     single event-id space.  This is evidence, not mechanism: it is what a
 *     consumer reads to see why a read resolved the way it did, and what the
 *     order domain is built over.
 *
 * ---------------------------------------------------------------------------
 * When it records
 * ---------------------------------------------------------------------------
 *
 * Only once the session has been *activated*: some task declared a selected
 * event site -- a shared carrier, a communication port, a synchronization
 * site, or the selected region itself -- and said so through `activate()`.
 *
 * The gate used to be `SharedFieldVersions::has_carriers()`, and that was a
 * correctness bug, not a cheaper spelling of the same rule (README EVENT-1).
 * A case whose selected sites are all RPC/SASL handoffs selects no carrier,
 * so every SYNCHRONIZATION channel silently went unrecorded for it: thread
 * start and join, volatile reads and writes, atomic RMW and CAS.  Those are
 * not decoration for such a case -- a sparse causal chain across a heartbeat
 * or a key rotation is made of exactly those edges -- so the case ended up
 * with its VALUE_HANDOFF edge and an order domain that claimed nothing else
 * happened.  The handoff and region recorders never consulted this gate,
 * which is why the loss was invisible.
 *
 * Activation is one-way inside a session.  Turning recording off partway
 * would leave a domain that reads as an absence of order rather than an
 * absence of recording, and no consumer can tell those apart.  The check is
 * still one relaxed load, so a workload that selects nothing keeps exactly
 * its old cost.
 *
 * ---------------------------------------------------------------------------
 * What creates order, and what deliberately does not
 * ---------------------------------------------------------------------------
 *
 * Thread lifecycle goes through the release map because start and termination
 * are explicit edges to or from one other thread.
 *
 * Volatile fields deliberately do *not*.  A volatile read happens-after the
 * particular write it read, not after the latest write to that location, and
 * a reader that joined "the location's last release" would claim to have seen
 * a write that may not even have executed yet.  The version store already
 * knows which write a read observed when it can prove it, so a volatile read
 * acquires the clock carried by *that* version, and acquires nothing when the
 * writer is ambiguous.  The clock therefore rides on the version rather than
 * on a per-location release slot.
 *
 * Unsafe and VarHandle are out of scope.  Unsafe's concolic support here is a
 * stub, and VarHandle does not exist on JDK 8, so neither can contribute an
 * ordering fact; a workload that orders shared state through them is a named
 * gap rather than a silently ordered execution.
 *
 * ---------------------------------------------------------------------------
 * Concurrency
 * ---------------------------------------------------------------------------
 *
 * `_mutex` guards the release map, the event log and the order domain.  Like
 * the version store's lock it is a leaf: no Expression is built under it, no
 * HotSpot Mutex is taken under it, and it is never held while the session heap
 * lock is held.  Clocks are copied in and out by value, so no caller ever
 * holds a reference into the map.  Engine-wide order is unchanged:
 *
 *     membership -> {heap, broker, versions, ledger} -> arena
 */
class EventLedger {
public:
  // Slot that is not a field offset.
  static const int SLOT_THREAD_LIFECYCLE = -1;

  enum EventKind {
    EVENT_VOLATILE_READ = 0,
    EVENT_VOLATILE_WRITE = 1,
    EVENT_THREAD_START = 2,
    EVENT_THREAD_JOIN = 3,
    EVENT_ATOMIC_RMW = 4,
    EVENT_ATOMIC_CAS = 5,
    EVENT_FIELD_WRITE = 6,
    EVENT_FIELD_READ = 7,
    EVENT_REGION_ENTER = 8,
    EVENT_REGION_EXIT = 9,
    EVENT_HANDOFF_EXPORT = 10,
    EVENT_HANDOFF_ATTACH = 11
  };

  /**
   * The one order domain.
   *
   * Every causal channel contributes to this single relation, which is what
   * makes a read-from edge and a lifecycle edge comparable at all. The kinds
   * are labels on edges of one graph, not separate graphs:
   *
   *   PROGRAM_ORDER   two events of one thread, in the order it executed them;
   *   SYNCHRONIZATION a release and the acquire that observed it;
   *   FIELD_READ_FROM a write and a read that provably took it.  A *guarded*
   *                   read contributes no edge at all -- that is exactly what
   *                   being unresolved means, and inventing one would be the
   *                   read-from guess the design forbids;
   *   VALUE_HANDOFF   a symbolic export and the attach that consumed it.  RPC
   *                   send/receive and async executor handoff share this kind
   *                   because they share one VM mechanism, the session broker;
   *                   protocol identity remains in the tracing layer;
   *   REGION          a region occurrence's own enter and exit;
   *   CANDIDATE       an order a consumer proposed, admitted only if it keeps
   *                   the relation acyclic.
   */
  enum EdgeKind {
    EDGE_PROGRAM_ORDER = 0,
    EDGE_SYNCHRONIZATION = 1,
    EDGE_FIELD_READ_FROM = 2,
    EDGE_VALUE_HANDOFF = 3,
    EDGE_REGION = 4,
    EDGE_CANDIDATE = 5
  };

  /** Why a proposed order was refused.  Zero is acceptance. */
  enum OrderStatus {
    ORDER_OK = 0,
    ORDER_NOT_OPEN = -1,
    ORDER_UNKNOWN_EVENT = -2,
    ORDER_SELF_EDGE = -3,
    ORDER_CYCLIC = -4,
    ORDER_DOMAIN_SATURATED = -5
  };

  struct Event {
    jlong event_id;
    int kind;
    jlong context_id;
    jlong java_thread_id;
    jlong step;
    sym_rid_t object;
    int slot;
    std::string region_id;
    std::string detail;
    Event()
        : event_id(0), kind(EVENT_VOLATILE_READ), context_id(0),
          java_thread_id(0), step(0), object(NULL_SYM_RID), slot(0) {}
  };

  static void open_session();
  static void close_session();

  /**
   * Declares that a selected event site exists in this session, so the hot
   * hooks may record.  Idempotent; see "when it records" above.
   */
  static void activate();

  /** See "when it records" above.  One relaxed load on the hot path. */
  static bool is_recording();

  /**
   * Appends one event drawn from the session's event-id space and returns its
   * id, linking it to this thread's previous event with a program-order edge.
   *
   * Ticking the caller's clock is the caller's job, because only the caller
   * knows whether its tick belongs before or after an acquire.  Recording
   * requires only an open session: the `is_recording()` gate belongs to the
   * hot bytecode hooks that decide whether to call at all, not to the ledger
   * that is told.
   */
  static jlong record(int kind, sym_rid_t object, int slot,
                      const char *detail);
  /**
   * Records a session-owned communication event from a thread that is not
   * executing a selected region.
   *
   * Such a thread has no ThreadContext, and therefore contributes neither a
   * local path condition nor an implicit program-order predecessor.  The
   * returned event still belongs to the session's one event-id domain and can
   * be joined to a later selected receiver by an explicit VALUE_HANDOFF edge.
   * This is intentionally narrower than making the thread symbolically
   * execute: it only records the value transfer that application tracing has
   * identified.
   */
  static jlong record_session_event(int kind, sym_rid_t object, int slot,
                                    const char *detail);

  /**
   * Adds one *observed* edge: a fact this run exhibited.  Not cycle-checked,
   * and deliberately so -- the run happened, so its own causal edges cannot
   * contradict each other. A *candidate* order is a different thing and goes
   * through propose_order.
   */
  static void add_observed_edge(jlong before, jlong after, int kind);

  /** Records one release, keyed by the releasing thread's context id. */
  static void publish_release(sym_rid_t object, int slot, jlong context_id,
                              jlong release_event_id,
                              const VectorClock &clock);
  /**
   * Copies out this object's release state.  `*releasers` receives the last
   * release event of every contributing thread, so the acquiring caller can
   * draw one synchronization edge per releaser rather than naming only the
   * most recent one.
   */
  static bool acquire_into(sym_rid_t object, int slot, VectorClock *clock,
                           std::vector<jlong> *releasers);

  /**
   * Offers one candidate order edge.  Accepted only if the relation stays
   * acyclic; a cyclic candidate is refused and nothing is added, because a
   * cyclic order describes no execution.
   *
   * This never completes the relation into a schedule.  The domain stays a
   * partial order: unrelated events remain unrelated, and no caller can ask
   * for a linearization of it.
   */
  static int propose_order(jlong before, jlong after);

  /** Whether the whole relation is currently acyclic. */
  static bool is_acyclic();

  static size_t event_count();
  static size_t edge_count();
  static std::string describe();

  static const char *event_kind_name(int kind);
  static const char *edge_kind_name(int kind);
  static const char *order_status_name(int status);

private:
  typedef std::pair<sym_rid_t, int> ReleaseKey;

  /**
   * One explicit lifecycle channel's release state: the join of every release
   * clock, and the last release event of each releasing thread.
   *
   * The clock is joined rather than replaced because multiple lifecycle
   * releases may contribute order to the acquiring thread. The per-context
   * event ids let the acquire draw one edge per releaser.
   */
  struct ReleaseRecord {
    VectorClock clock;
    std::map<jlong, jlong> last_release_event;
  };

  typedef std::map<ReleaseKey, ReleaseRecord> ReleaseStore;

  struct Edge {
    jlong before;
    jlong after;
    int kind;
    Edge() : before(0), after(0), kind(EDGE_PROGRAM_ORDER) {}
    Edge(jlong b, jlong a, int k) : before(b), after(a), kind(k) {}
  };

  // Evidence is bounded; losing the oldest costs an older report and is
  // recorded so a reader is never shown a truncated log as a whole one.
  static const size_t MAX_EVENTS = 4096;
  // The edge budget is *not* a truncation bound.  Dropping an edge could hide
  // a cycle from the check, so a saturated domain refuses further edges and
  // says so instead of silently accepting unchecked ones.
  static const size_t MAX_EDGES = 16384;

  static bool _open;
  // Whether any selected event site has been declared for this session.
  // Read without the lock on purpose: it only ever goes false -> true inside
  // a session, so a stale read costs one unrecorded event at the moment of
  // activation and never a wrong one.  open_session()/close_session() reset
  // it under the lock with everything else the session owns.
  static bool _activated;
  static ReleaseStore _releases;
  static std::vector<Event> _events;
  static bool _events_truncated;
  static std::vector<Edge> _edges;
  static std::map<jlong, std::vector<jlong> > _successors;
  static std::vector<jlong> _event_ids;
  static bool _domain_saturated;
  static pthread_mutex_t _mutex;

  static void add_edge_locked(jlong before, jlong after, int kind);
  static bool reaches_locked(jlong from, jlong target);
  static bool known_event_locked(jlong event_id);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_EVENTLEDGER_HPP
