#ifndef SHARE_VM_CONCOLIC_UNSAFEACCESS_HPP
#define SHARE_VM_CONCOLIC_UNSAFEACCESS_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/sharedFieldVersions.hpp"

class MethodSymbolizerHandle;

/**
 * Heap accesses sun.misc.Unsafe performs in native code.
 *
 * No bytecode runs for them, so no field or array hook sees them, and the
 * whole Unsafe class is muted: an AtomicInteger bumped by a thread outside
 * every region, a CHM table slot, a field updater, `lazySet`, reflection's
 * Field.set -- each changed a tracked location and left no version, and the
 * next reader found a word no version stored (SOLR's SolrCore.refCount,
 * unobs/).  Each one is now a versioned access, in one critical section with
 * its concrete operation exactly as a bytecode store is: `begin` takes the
 * location's stripe before the operation, `end_put`/`end_cas` publish and
 * release it after.
 *
 * What the stored value IS comes from the caller that knew it:
 *
 *   - the atomic model (AtomicInteger/AtomicLong) states the linearization
 *     it expects -- `new = old op delta`, or a CAS's expect/update -- as this
 *     thread's Intent before the muted body runs; the compare-and-swap that
 *     performs it resolves `old` as a read of the word it compared, and
 *     publishes `new` as the RMW version, in the same critical section, so a
 *     concurrent reader can never see the word before the version, and a
 *     failed CAS decides on the word it lost to, never on a later re-read
 *     (item 2);
 *   - an Unsafe write called from ordinary code states its operands' shadows
 *     the same way (SymbolicUnsafe captures them at the call boundary);
 *   - a thread outside every region writes concretely, unattributed, as its
 *     bytecode stores do;
 *   - anything else -- a write from inside a muted subtree, whose operand's
 *     shadow nobody could capture -- is versioned with its concrete word and
 *     the location's writer set is marked incomplete by name
 *     (UNSAFE_WRITE_UNCAPTURED): detected, never silent.
 *
 * A write to a shadowed object also updates the field shadow (or the array's
 * container state), which it used to leave stale.
 */
class UnsafeAccess {
public:
  enum Kind { NONE = 0, PUT = 1, CAS = 2, ADD = 3, SET = 4 };

  /** What this thread's next Unsafe write of one location is.  POD. */
  struct Intent {
    int kind;
    // Set by the atomic model, whose finish reads the result back.
    bool model;
    sym_rid_t owner;
    jlong offset;
    // ADD: op_add or op_sub.
    int op;
    // PUT/SET: the value; ADD: the delta; CAS: the update.  NULL: concrete.
    Expression *operand;
    // CAS: the expected value.  NULL: concrete.
    Expression *expect;
    // The model's pre-state of a location with no log, and the word it stood
    // for when the call began: a CAS that compares another word read a
    // concurrent write, not this pre-state.
    Expression *prior;
    bool prior_stated;
    jlong prior_bits;
    // Filled by the write.
    bool done;
    bool succeeded;
    Expression *old_value;
    Expression *new_value;
  };

  /** This thread's intent; kind NONE when there is none. */
  static Intent *intent();
  static void clear_intent();

  /** Captures an ordinary caller's Unsafe write operands (SymbolicUnsafe). */
  static void capture(MethodSymbolizerHandle &handle);
  /** Drops a capture its call did not consume. */
  static void release_capture();

  /** One access, bracketing its concrete operation. */
  struct Access {
    bool active;
    SharedFieldVersions::Location location;
    SharedFieldVersions::Cell cell;
    SharedFieldVersions::ReadPlan plan;
    Expression *path_guard;
    Intent *intent;
    // A reference store's referent's container state, asked before the
    // stripe (SharedFieldVersions::referent_state).
    SharedFieldVersions::ReferentState referent;
    bool referent_prepared;
    Access()
        : active(false), path_guard(NULL), intent(NULL),
          referent_prepared(false) {}
  };

  /**
   * Before a concrete Unsafe write of `holder` at `offset` of `type`: the
   * location it names, and its stripe taken when it is or may become
   * tracked.  `stored` is the referent a reference write stores.
   */
  static void begin(Access *access, oop holder, jlong offset, BasicType type,
                    oop stored = NULL);

  /** After a put of `stored` (a reference's word, if boxed, and itself). */
  static void end_put(Access *access, const SharedFieldVersions::ConcreteBits &stored,
                      oop stored_reference);

  /**
   * After a compare-and-swap: `witnessed` is the word the compare read (the
   * expected one on success, the one it lost to otherwise); `stored` what a
   * success left.
   */
  static void end_cas(Access *access, bool succeeded,
                      const SharedFieldVersions::ConcreteBits &witnessed,
                      oop witnessed_reference,
                      const SharedFieldVersions::ConcreteBits &stored,
                      oop stored_reference);

  /** The word of one primitive, in its Java type. */
  static SharedFieldVersions::ConcreteBits word(jboolean value) {
    return SharedFieldVersions::ConcreteBits(
        T_BOOLEAN, SharedFieldVersions::raw_bits((jboolean)(value & 1)));
  }
  static SharedFieldVersions::ConcreteBits word(jbyte value) {
    return SharedFieldVersions::ConcreteBits(
        T_BYTE, SharedFieldVersions::raw_bits(value));
  }
  static SharedFieldVersions::ConcreteBits word(jchar value) {
    return SharedFieldVersions::ConcreteBits(
        T_CHAR, SharedFieldVersions::raw_bits(value));
  }
  static SharedFieldVersions::ConcreteBits word(jshort value) {
    return SharedFieldVersions::ConcreteBits(
        T_SHORT, SharedFieldVersions::raw_bits(value));
  }
  static SharedFieldVersions::ConcreteBits word(jint value) {
    return SharedFieldVersions::ConcreteBits(
        T_INT, SharedFieldVersions::raw_bits(value));
  }
  static SharedFieldVersions::ConcreteBits word(jlong value) {
    return SharedFieldVersions::ConcreteBits(
        T_LONG, SharedFieldVersions::raw_bits(value));
  }
  static SharedFieldVersions::ConcreteBits word(jfloat value) {
    return SharedFieldVersions::ConcreteBits(
        T_FLOAT, SharedFieldVersions::raw_bits(value));
  }
  static SharedFieldVersions::ConcreteBits word(jdouble value) {
    return SharedFieldVersions::ConcreteBits(
        T_DOUBLE, SharedFieldVersions::raw_bits(value));
  }

private:
  // Clears a caller's capture its write has used.
  static void consume(Intent *intent);
  static void update_shadow(const Access &access, Expression *value,
                            const SharedFieldVersions::ConcreteBits &stored,
                            oop stored_reference);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_UNSAFEACCESS_HPP
