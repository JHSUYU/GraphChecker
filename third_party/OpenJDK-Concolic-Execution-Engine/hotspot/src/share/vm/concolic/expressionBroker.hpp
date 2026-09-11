#ifndef SHARE_VM_CONCOLIC_EXPRESSIONBROKER_HPP
#define SHARE_VM_CONCOLIC_EXPRESSIONBROKER_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"

#include <pthread.h>

#include <map>
#include <string>

/**
 * Same-JVM symbolic value handoff.
 *
 * Every other explicit input API mints a fresh symbol for the value it is
 * pointed at.  A traced communication boundary needs the opposite: the value
 * the receiver deserialized must denote the expression the sender already
 * built, so that the receiver's own arithmetic composes onto it directly.
 *
 * The broker is the indirection that makes this possible without handing a
 * raw VM pointer to Java.  A sender publishes one symbolic leaf and receives
 * an opaque jlong token; a receiver presents that token and the VM resolves
 * it back to the live Expression. The session arena keeps every published
 * expression valid until session teardown.
 *
 * Lifetime is session-scoped.  A published Expression* stays valid for as
 * long as the GlobalSymbolicSession that owns it is open, because expressions
 * are arena-owned and are freed only at session teardown.  The table used to
 * be scoped to one region for the opposite reason: ~ThreadContext
 * force-deleted every surviving Expression, so a leaf could not outlive the
 * context that produced it, and cross-region handoff was therefore
 * unsupported.  With the arena that restriction is gone -- a leaf published
 * by one region is still a live expression in the next -- and the remaining
 * scope is the session's, not the region's.
 *
 * A session now spans every region of every attached thread, so a handle
 * issued in one region resolves in the next region of that session, and on any
 * other thread attached to it.  That is the point: an exchange is exported by
 * the sender's region and attached by the receiver's, and the two are rarely
 * the same region and often not the same thread.  The boundary that still
 * rejects is the session: a token minted by a previous session is FOREIGN,
 * because the expression it named no longer exists.
 *
 * A handle is (epoch << 32) | serial.  The epoch is a fresh per-session salt,
 * which keeps handles from colliding across sessions and makes a guessed or
 * replayed token overwhelmingly likely to be rejected rather than resolved to
 * an unrelated leaf. A serial absent from the current session is unknown.
 *
 * Concurrency: _mutex guards the leaf table, the serial counter, the epoch and
 * the open flag.  It is a leaf lock -- no Expression is constructed under it,
 * no HotSpot Mutex is taken under it, and it is never held while the session
 * heap lock is taken -- so it participates in no lock order.  resolve()
 * copies the leaf out rather than returning a pointer into the table.
 * Copying a Leaf is cheap next to the communication boundary that asked for
 * it, and the Expression* inside the copy stays valid for the session's life.
 * is_open() reads the flag without the lock on purpose: it is an advisory
 * early-out for callers that want a NO_ACTIVE_REGION status before doing
 * field lookup work, and every operation that touches the table re-checks it
 * under the lock, so a stale answer costs a wasted lookup and never a wrong
 * binding. Session close owns reclamation.
 */
class ExpressionBroker {
public:
  enum LeafKind {
    FIELD_EXPRESSION = 0,
    CONTAINER_STATE = 1
  };
  /**
   * Every negative value is a distinguishable RPC handoff gap.  Java turns
   * these into named coverage gaps; none of them may silently fall back to a
   * guessed binding.
   */
  enum HandoffStatus {
    HANDOFF_OK                   = 0,
    HANDOFF_NO_ACTIVE_REGION     = -1,
    HANDOFF_MISSING_METADATA     = -2,
    HANDOFF_FIELD_NOT_FOUND      = -3,
    HANDOFF_NOT_SYMBOLIC         = -4,
    HANDOFF_FOREIGN_HANDLE       = -5,
    HANDOFF_UNKNOWN_HANDLE       = -6,
    // The destination's declared sort is not the exported leaf's. A live
    // handle names the expression, but a location of another sort cannot
    // hold it.
    HANDOFF_SORT_MISMATCH        = -9,
    HANDOFF_UNSUPPORTED_TARGET   = -12
  };

  /**
   * One published symbolic leaf. Communication provenance belongs to the
   * application trace; the broker retains only what attach consumes.
   */
  struct Leaf {
    Expression *expression;
    // Exact Java type descriptor of the exported location ("I", "J",
    // "Ljava/lang/String;", ...).  Sort compatibility is descriptor equality.
    std::string descriptor;
    // Container handoffs carry contents/state, never source object identity.
    LeafKind kind;
    std::string container_shape;
    // Arrays additionally keep the fixed runtime class and cardinality.
    // No source oop is retained by the broker.
    std::string array_class;
    int array_length;
    // Session-global identity of the sender's export endpoint. The receiver
    // returns it alongside its own attach endpoint identity.
    jlong export_event_id;
  };

  static void open_session(jlong session_id);
  static void close_session();
  static bool is_open() { return _open; }

  static jlong publish(Expression *expression,
                       const std::string &descriptor, jlong export_event_id,
                       LeafKind kind, const std::string &container_shape,
                       const std::string &array_class, int array_length);
  /**
   * Resolves one token against this session's table, atomically under the
   * table lock. On HANDOFF_OK, *leaf receives a copy of the entry; the caller owns that
   * copy, and the Expression it names stays valid for as long as the session
   * is open.
   *
   * This is the whole lookup.  A live handle already names one expression, so
   * there is no second identity to agree on afterwards and no tally: one
   * exported expression may be attached at several explicit receivers, and
   * each attach records its own VALUE_HANDOFF edge.
   */
  static HandoffStatus resolve(jlong handle, Leaf *leaf);
private:
  typedef std::map<jlong, Leaf> LeafStore;

  // _epoch keeps the last issued salt even while closed, so that the next
  // session is guaranteed to pick a different one and cannot silently accept
  // a token minted for its predecessor.
  static jlong _epoch;
  static bool _open;
  static jlong _next_serial;
  static LeafStore _leaves;
  static pthread_mutex_t _mutex;

  static HandoffStatus find_locked(jlong handle, LeafStore::iterator *found);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_EXPRESSIONBROKER_HPP
