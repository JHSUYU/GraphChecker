#ifndef SHARE_VM_CONCOLIC_SESSIONSYMBOLICHEAP_HPP
#define SHARE_VM_CONCOLIC_SESSIONSYMBOLICHEAP_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "oops/oop.inline.hpp"

#include <pthread.h>

#include <map>
#include <string>

/**
 * The session's shadow heap: everything a symbolic value's *identity* is
 * anchored to, as opposed to how one thread reached it.
 *
 * This state used to live in ThreadContext, which made a region exit destroy
 * it.  That is exactly the operation a shared session forbids: an object's
 * symbolic shadow, its detached-identity handle and its container state
 * describe the object, not the thread that happened to touch it first, and one
 * thread finishing its region must not erase them for everyone else.  They are
 * therefore owned by the session and torn down only at session teardown.
 *
 * ThreadContext keeps what is genuinely per-thread -- frames, shadow operand
 * stack and locals, path condition, branch events, region metadata -- and
 * forwards heap questions here.  Because the forwarding happens in one place,
 * every existing `ConcolicMngr::ctx->find_sym_inst(...)` style call site keeps
 * working unchanged and automatically reaches the shared heap.
 *
 * ---------------------------------------------------------------------------
 * Concurrency contract
 * ---------------------------------------------------------------------------
 *
 * _mutex guards the six containers below, and the oop header word that indexes
 * _sym_refs.  Four rules make that lock usable from a Java thread:
 *
 *   1. Every read and every write of a container happens under _mutex, and a
 *      composite operation re-reads under the lock whatever it decided on
 *      outside it.  A lookup that escapes the lock is a use-after-free waiting
 *      for the first concurrent insert.
 *
 *   2. Nothing that can block runs inside a critical section: no Expression is
 *      constructed, no HotSpot Mutex is taken, no VM operation is requested.
 *      This is not a style rule.  JNIHandles::make_global takes
 *      JNIGlobalHandle_lock, and acquiring a HotSpot Mutex from _thread_in_vm
 *      can block for a safepoint.  A second thread parked on this pthread
 *      mutex is also _thread_in_vm and never reaches that safepoint, so the VM
 *      thread waits for it, it waits for the lock holder, and the lock holder
 *      waits for the VM thread.  Nobody can yield: the whole VM is wedged.
 *      Allocation, GC-root retention and expression construction therefore all
 *      happen before the lock is taken.
 *
 *   3. Lock order is heap -> arena, never the reverse.  The session's arena
 *      lock is a leaf, taken by every Expression constructor and by nothing
 *      else, which is the other reason rule 2 forbids building a node here.
 *
 *   4. Publication is check / build / re-check.  Whatever was built outside
 *      the lock is installed only if no other thread got there first; the
 *      loser discards its own copy and returns the winner's.  Discarding is
 *      safe precisely because of the session ownership model: an Expression
 *      belongs to the arena and is freed at teardown rather than here, and an
 *      unpublished Sym* shadow is named by nobody else.  Object identity is
 *      therefore stable -- one oop resolves to one shadow for the life of the
 *      session, whichever thread reached it first.
 *
 * The destructor deliberately takes no lock: it runs only when the session has
 * no attached threads left, and it calls JNIHandles::destroy_global, which
 * rule 2 forbids inside a critical section.
 *
 * ---------------------------------------------------------------------------
 * Field-shadow write policy
 * ---------------------------------------------------------------------------
 *
 * The lock above makes concurrent access to this heap memory-safe.  Symbolic
 * read-from choice is enabled only for locations selected as carriers.
 *
 *   Unselected locations.  A field shadow holds exactly one expression, the
 *   most recently completed write.  Last writer wins.  A read returns some
 *   completed write's expression -- never a partially installed one, and never
 *   a mixture -- and the engine records nothing about which write that was.
 *
 * SymInstance::_field_mutex is what makes this literally true.  Without it the
 * behaviour would not be "an arbitrary winner"; it would be two threads
 * rebalancing one red-black tree, which is undefined, and calling that
 * last-writer-wins would be a description of a crash.  A single Expression*
 * shadow (SymString, SymStrBuilder, SymPrimitive, SymBigDecimal::_exp) is a
 * naturally aligned pointer store and already satisfies the policy on its own,
 * as do SymRef::set_ref_exp and SymArr's length/reference slots.
 * set_container_state and SymArr::store() follow the same rule: the last
 * completed write is the state, and a lost ++_version only makes an array
 * identity label coarser, never unsafe.
 *
 *   Selected carriers.  Every completed write to a selected instance field,
 *   static field or fixed-shape array element appends an immutable version
 *   carrying its expression, case identity and path guard.  Every read becomes
 *   a bounded exactlyOne(rf1, ..., rfk) over all retained versions, including
 *   the singleton case.  Replay does not pin a writer and synchronization does
 *   not prune this symbolic choice.  Incomplete writer coverage is metadata
 *   that prevents a closed conclusion, never a fresh solver value.  The
 *   last-writer-wins shadow remains the JVM's concrete value, while the version
 *   set supplies the symbolic alternatives.
 *
 * This replaces the CONCURRENT_FIELD_SHADOW_WRITE gap for selected locations.
 * The gap still describes every location nobody selected, and that is a
 * deliberate cost decision rather than an oversight: the interpreter's field
 * hooks fire for every field of every shadowed object, so versioning all of
 * them would charge a bounded analysis for state it never asks about.  A
 * consumer must therefore still report CONCURRENT_FIELD_SHADOW_WRITE for any
 * field it reasons about that was not selected as a carrier.
 *
 * Two limits of the replacement are named rather than approximated:
 *
 *   - a resizable collection's contents have no stable slot -- its members
 *     move under insertion and removal -- so per-slot read-from over one is
 *     not expressible here.  Such containers keep the existing container
 *     state-transformer algebra, and the gap above applies to them;
 *   - a store the interpreter hooks do not see (a JNI, reflective or otherwise
 *     unobserved write) publishes no version.  It is not silently ignored: the
 *     first read whose observed value no tracked writer wrote marks that
 *     location's writer set incomplete for good, and every later read of it
 *     stays guarded.
 *
 * Deliberately *not* done anywhere here: guessing.  Choosing a winner by
 * concrete value alone, by event id or by thread would manufacture a read-from
 * edge the run never showed, which is the one thing the design forbids
 * outright.  Ruling a writer *out* because the read returned a value it did
 * not store is the opposite operation and is sound; ruling one *in* requires a
 * complete writer set, and is claimed only when there is one.
 */
class SessionSymbolicHeap {
  /**
   * TODO: make this hashtable!
   */
  typedef std::map<sym_rid_t, SymRef *> SymStore;
  // Some VM-managed objects, most notably interned Strings, must never have
  // their shared oop header marked symbolic.  Keep their session-scoped
  // symbolic identity behind a GC-stable handle instead.  SymStore remains the
  // sole owner of the SymInstance; this map is only an identity lookup index.
  typedef std::map<jobject, SymInstance *> DetachedObjectStore;
  typedef std::map<sym_rid_t, Expression *> ContainerStateStore;
  typedef std::map<sym_rid_t, int> ContainerPositionStore;
  typedef std::map<sym_rid_t, sym_rid_t> ContainerOwnerStore;

private:
  SymStore _sym_refs;
  DetachedObjectStore _detached_object_store;
  ContainerStateStore _container_states;
  ContainerPositionStore _container_positions;
  // Iterator traversal ordinals name members in the entry state and must not
  // move backwards after Iterator.remove().  Removal itself addresses the
  // current (compacted) state, so remember how many earlier members this
  // cursor removed and translate the stable ordinal to a live index there.
  ContainerPositionStore _container_removals;
  ContainerOwnerStore _container_owners;

  // Guards the containers above.  See the concurrency contract at the top
  // of this file before adding a call under it.
  mutable pthread_mutex_t _mutex;

  class HeapLock {
  public:
    HeapLock(const SessionSymbolicHeap *heap) : _heap(heap) {
      pthread_mutex_lock(&_heap->_mutex);
    }
    ~HeapLock() { pthread_mutex_unlock(&_heap->_mutex); }
  private:
    const SessionSymbolicHeap *_heap;
  };

  // ---- the _locked suffix means "_mutex is already held by the caller" ----
  void set_sym_ref_locked(sym_rid_t sym_rid, SymRef *sym_ref) {
    _sym_refs.insert(std::make_pair(sym_rid, sym_ref));
  }
  SymInstance *find_sym_inst_locked(oop obj) const;
  SymArr *find_sym_array_locked(arrayOop array_obj) const;
  sym_rid_t canonical_container_id_locked(sym_rid_t id) const;

  static sym_rid_t get_next_sym_rid();

public:
  SessionSymbolicHeap();
  ~SessionSymbolicHeap();

  /**
   * This object's session identity, minting one if it has none.
   *
   * The identity a recording needs to *name* what a reference read returned,
   * and nothing else: no shadow, no store entry, no GC root, and the object
   * stays non-symbolic (`SYM_RID_NAMED_ONLY`), so naming it cannot change
   * which loads take the symbolic path or which expressions exist.  An object
   * that already has an identity -- named earlier, or symbolic -- keeps it, so
   * one object has one identity for the session however it was reached.
   *
   * Returns NULL_SYM_RID only for a NULL object.
   */
  sym_rid_t name_reference(oop obj);

  SymInstance *get_or_alloc_sym_inst(oop obj);
  SymInstance *alloc_sym_inst(oop obj);
  SymInstance *get_sym_inst(sym_rid_t sym_rid);
  SymInstance *find_sym_inst(oop obj) const;
  bool requires_detached_object_shadow(oop obj) const;

  // `named`: the shadow exists only because a load or store named the array
  // (SymArr::named).  Decided by the call that allocates the shadow, under
  // the heap lock, and by no later caller: a symbolization that cleared it
  // must not see a racing load set it back.
  SymArr *get_or_alloc_sym_array(arrayOop array, Expression *length_exp = NULL,
                                 bool named = false);
  SymArr *alloc_sym_array(arrayOop array, Expression *length_exp = NULL,
                          bool named = false);
  SymArr *get_sym_array(sym_rid_t sym_rid);
  SymArr *find_sym_array(arrayOop array_obj) const;

  void write_array_element(arrayOop array, int index, Expression *expression,
                           const ElementWord &word = ElementWord());
  Expression *track_container(oop container, const char *shape,
                              const std::string &prefix);
  Expression *container_state(oop container, const char *shape);
  /**
   * The one id that names this container and every view of it, or
   * NULL_SYM_RID when it has no shadow yet.
   *
   * Deliberately a pure lookup: it allocates no shadow and mints no id, so
   * asking which location a container is cannot be the thing that gives it
   * one.  A view and its owner answer the same id, which is what makes
   * `map.keySet().clear()` a mutation of the map's location rather than of a
   * second location nobody reads.
   */
  sym_rid_t canonical_container_id(oop container) const;
  Expression *find_container_state(oop container) const;
  void set_container_state(oop container, Expression *state);
  // Drops the state of the container (and of every view or cursor aliased to
  // it): a later modeled operation roots it afresh.
  void forget_container_state(oop container);
  void alias_container(oop derived, oop owner);
  int next_container_position(oop cursor);
  int current_container_position(oop cursor);
  int current_container_index(oop cursor);
  int next_container_removal_position(oop cursor);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_SESSIONSYMBOLICHEAP_HPP
