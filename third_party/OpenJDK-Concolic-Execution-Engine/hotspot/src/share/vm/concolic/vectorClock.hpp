#ifndef SHARE_VM_CONCOLIC_VECTORCLOCK_HPP
#define SHARE_VM_CONCOLIC_VECTORCLOCK_HPP

#ifdef ENABLE_CONCOLIC

#include "jni.h"

#include <map>

/**
 * One participant's knowledge of the session's happens-before relation.
 *
 * A clock maps a thread context id to the highest local step of that context
 * the holder is known to have observed.  Threads tick their own entry; the
 * selected actions that create order (volatile provenance and thread
 * start/join) join one clock into another. A write stamped
 * `(context, step)` happens-before a read whose clock satisfies
 * `knows(context, step)`, and that implication is the only thing Phase 2 ever
 * uses to claim that a read's provenance is exact rather than guarded.
 *
 * The representation is deliberately sparse and copyable.  Only a bounded
 * carrier set stores clock snapshots, and a session has few attached threads,
 * so the map stays small; copying one is cheaper than the alternative of
 * chasing a shared, mutable predecessor graph from a Java thread.
 *
 * A clock is never shared between threads without a copy.  The owner mutates
 * its own clock with no lock (it is thread-local execution state); any clock
 * published into session state -- a lifecycle release or a version's write
 * stamp -- is a snapshot taken by value under the publishing structure's own
 * lock, so no reader ever observes a half-updated map.
 */
class VectorClock {
public:
  typedef std::map<jlong, jlong> Entries;

  VectorClock() {}

  jlong at(jlong context_id) const {
    Entries::const_iterator found = _entries.find(context_id);
    return found == _entries.end() ? (jlong) 0 : found->second;
  }

  /** Monotone: a clock entry never moves backwards. */
  void observe(jlong context_id, jlong step) {
    jlong &slot = _entries[context_id];
    if (step > slot) slot = step;
  }

  void join(const VectorClock &other) {
    for (Entries::const_iterator it = other._entries.begin();
         it != other._entries.end(); ++it) {
      observe(it->first, it->second);
    }
  }

  /** True when this clock has observed `(context_id, step)`, i.e. it is hb-after. */
  bool knows(jlong context_id, jlong step) const {
    return step > 0 && at(context_id) >= step;
  }

  bool is_empty() const { return _entries.empty(); }
  const Entries &entries() const { return _entries; }
  void clear() { _entries.clear(); }

private:
  Entries _entries;
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_VECTORCLOCK_HPP
