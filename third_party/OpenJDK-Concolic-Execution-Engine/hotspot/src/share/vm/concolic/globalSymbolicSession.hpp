#ifndef SHARE_VM_CONCOLIC_GLOBALSYMBOLICSESSION_HPP
#define SHARE_VM_CONCOLIC_GLOBALSYMBOLICSESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "utilities/globalDefinitions.hpp"

#include <pthread.h>
#include <vector>

class Expression;
class SessionSymbolicHeap;

/**
 * One symbolic session per JVM.
 *
 * A session is the scope in which symbolic identity means something.  It owns
 * the expression arena, the expression and object id spaces, and the built-in
 * symbol singletons; a thread's frames, operand-stack shadow, locals and path
 * condition stay outside it, in that thread's own execution state.  Several
 * threads may therefore denote the same value with the same expression without
 * sharing anything about how they reached it.
 *
 * ---------------------------------------------------------------------------
 * Expression memory model
 * ---------------------------------------------------------------------------
 *
 * Expressions are immutable once built and are owned by the session, never by
 * the structures that name them:
 *
 *   1. Every Expression registers itself with this arena in its constructor.
 *   2. An Expression is destroyed only by close(), never by anything else.
 *      No shadow slot, field shadow, path condition, broker leaf or parent
 *      node may delete one, and a parent node does not own its children.
 *   3. Consequently, holding an Expression* is always safe for as long as the
 *      session is open, from any attached thread, with no reference counting
 *      and therefore no reference-count race.
 *
 * This replaces a non-atomic per-node reference count plus two process-global
 * std::set<Expression*> bookkeeping tables.  Those were sound only while a
 * single thread could ever touch symbolic state: two owners racing on
 * `--_ref_count == 0` free a live node, and one thread's teardown pass over
 * the bookkeeping tables force-deleted expressions another thread still
 * referenced.  Deferring every free to session teardown removes the whole
 * class of bug rather than making the race narrower.
 *
 * The cost is that a session's peak expression memory is its total, not its
 * live, expression count.  The bookkeeping it replaces was already O(every
 * expression ever created) -- two set nodes per expression, retained until
 * teardown -- so the additional cost is the node payload alone.  If a long
 * workload ever needs early reclamation, it has to come from an explicit
 * session-level sweep of nodes unreachable from any thread state, not from
 * ownership scattered across the naming structures.
 *
 * ---------------------------------------------------------------------------
 * Object identity
 * ---------------------------------------------------------------------------
 *
 * sym_rid values are minted from one session-wide atomic counter, so two
 * threads can allocate object shadows at the same time without aliasing each
 * other's ids in the shared oop header word.  The counter restarts per
 * session, which is what keeps MAX_SYM_RID meaningful across a long-running
 * JVM; close() therefore clears the header word on every surviving object so
 * no stale id from this session can be read as an id of the next one.
 *
 * That heap pass runs exactly once, at session teardown.  It used to run at
 * every ThreadContext destruction, which is precisely the operation that must
 * not exist once several threads share a session: one thread's region exit
 * would erase every other thread's live symbolic object identity.
 *
 * The same argument applies to the shadow heap those ids index, so the session
 * owns that too; see sessionSymbolicHeap.hpp.
 */
class GlobalSymbolicSession {
public:
  static void open();
  static void close();
  static bool is_open() { return _open; }

  /**
   * This session's identity, minted once by open() and retired by close().
   *
   * Every expression id, object id and event id above is only meaningful
   * relative to one session, so an artifact that carries any of them has to
   * carry this too: two runs of the same workload in one JVM restart all three
   * counters, and without a session id their records would be
   * indistinguishable.  It is strictly increasing per JVM and never reused, so
   * "the same session id" is a sound identity test across regions and threads,
   * and a different id is proof that a teardown happened in between.
   *
   * Zero means no session is open.
   */
  static jlong session_id() { return _session_id; }

  /**
   * Called by Expression's constructor.  Takes ownership: the caller must
   * never delete the expression it just handed over.
   */
  static void record_expression(Expression *expression);
  static size_t expression_count();

  /**
   * The session's shadow heap.  Valid only while the session is open; every
   * caller reaches it through its own ThreadContext, which is where the
   * "is a session open" question has already been answered.
   */
  static SessionSymbolicHeap *heap() { return _heap; }

  static uint next_expression_id();
  static sym_rid_t next_sym_rid();

  /**
   * The session's monotonic identity space for region occurrences, shared
   * versions, reads and handoff endpoints.  These ids correlate runtime facts;
   * their numeric order has no execution-order meaning.
   */
  static jlong next_event_id();

private:
  typedef std::vector<Expression *> ExprArena;

  static bool _open;
  static jlong _session_id;
  // Never reset: a session id retired by close() must not come back.
  static volatile intptr_t _next_session_id;
  static SessionSymbolicHeap *_heap;
  static ExprArena _arena;
  // Guards _arena only.  The critical section is one push_back: it never
  // blocks on a safepoint, so a thread holding it cannot stall the VM thread.
  static pthread_mutex_t _arena_mutex;
  static volatile intptr_t _next_expression_id;
  static volatile intptr_t _next_sym_rid;
  static volatile intptr_t _next_event_id;

  static void restore_object_symbolic_ids();
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_GLOBALSYMBOLICSESSION_HPP
