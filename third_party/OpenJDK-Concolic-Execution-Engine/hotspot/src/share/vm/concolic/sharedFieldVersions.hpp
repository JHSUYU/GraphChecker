#ifndef SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP
#define SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/vectorClock.hpp"
#include "oops/oop.inline.hpp"

#include <pthread.h>

#include <map>
#include <string>
#include <vector>

/**
 * Versioned writes to the session's selected shared locations.
 *
 * Phase 1 gave a field shadow exactly one expression -- the most recently
 * completed write -- and recorded nothing about who wrote it.  That is the
 * named CONCURRENT_FIELD_SHADOW_WRITE gap, and this class is what replaces it:
 * every write to a *selected* location appends an immutable version carrying
 * the writer's evidence, so a later read can name its provenance instead of
 * inheriting whatever pointer happened to survive.
 *
 * ---------------------------------------------------------------------------
 * What is versioned, and why not everything
 * ---------------------------------------------------------------------------
 *
 * The field hooks in the interpreter fire for every field of every shadowed
 * object.  Versioning all of them would append a record, a clock snapshot and
 * a folded path guard on a bytecode that a workload executes millions of
 * times, which is a cost no bounded analysis can pay for state it will never
 * ask about.  A location therefore has to be *selected* before it is
 * versioned, and selection is explicit: `ConcolicMngr::selectSharedCarrier*`
 * names one owner and one slot.
 *
 * Selection is what makes the hook affordable.  When no carrier exists at all
 * the hooks read one relaxed counter and stop, which is why every pre-existing
 * workload keeps its old cost exactly.  When carriers do exist, a location is
 * still rejected by one map lookup, and only a selected location pays for a
 * version.
 *
 * Selecting a location also publishes an INITIAL version holding the value the
 * location had at that moment.  Without it the value a read observes before
 * any tracked write would have no candidate at all, and the resolver would
 * have to invent one.  With it, "the state this location started in" is an
 * ordinary candidate with ordinary evidence.
 *
 * ---------------------------------------------------------------------------
 * Ordering the concrete access and the version
 * ---------------------------------------------------------------------------
 *
 * A version is published *after* the concrete store has completed, and it
 * records the value that store wrote, taken from the operand stack rather than
 * re-read from the heap.  Re-reading would report whatever a concurrent writer
 * left behind and attribute it to this thread; taking the operand it actually
 * stored is exact regardless of what else is running.  The pairing is
 * one-to-one: no version exists for a store that did not happen, and no store
 * to a selected location fails to produce one.
 *
 * ---------------------------------------------------------------------------
 * Retention, and what an incomplete writer set means
 * ---------------------------------------------------------------------------
 *
 * A location keeps at most MAX_VERSIONS_PER_LOCATION versions.  Dropping the
 * oldest is not free: it makes the writer set incomplete, and a resolver that
 * treated an incomplete set as complete would report an exact writer that the
 * evidence does not support.  Truncation therefore clears
 * `writer_set_complete`, which is a permanent property of the location and is
 * reported with every answer derived from it.
 *
 * The read log is bounded the same way and is *not* silent about it.  A read
 * is evidence of a decision that was already made, so losing one leaves every
 * writer set exactly as complete as it was; what it does destroy is the claim
 * that the log is the whole record.  A consumer that counted the retained
 * rows would otherwise read a truncated log as closed read coverage, which is
 * a stronger statement than the store can make.  Truncation therefore clears
 * `read_log_complete` permanently -- reported as `readLogTruncated` -- and
 * keeps `reads_observed` (how many reads really happened) next to
 * `reads_dropped` (how many are no longer shown), so "the log holds every
 * read" and "the log holds the most recent reads" are distinguishable in the
 * emitted evidence.  The two flags are deliberately separate: conflating them
 * would let a lost audit row mark a writer set incomplete that is
 * demonstrably whole.
 *
 * ---------------------------------------------------------------------------
 * Concurrency
 * ---------------------------------------------------------------------------
 *
 * `_mutex` guards the carrier set, the version store and the read log.  It is
 * a leaf lock in the same sense as ExpressionBroker's: no Expression is
 * constructed under it, no HotSpot Mutex is taken under it, and it is never
 * held while the session heap lock or the broker lock is held.  Callers
 * resolve object shadows (which takes and releases the heap lock) and fold
 * path guards (which takes and releases the arena lock) *before* entering it.
 * The engine-wide order is therefore unchanged:
 *
 *     membership -> {heap, broker, versions} -> arena
 *
 * `has_carriers()` reads a plain counter without the lock on purpose.  It is
 * an advisory early-out on the hottest bytecode in the interpreter; every
 * operation that acts on the answer re-checks under the lock, so a stale read
 * costs one wasted lookup and can never produce a wrong version.
 */
class SharedFieldVersions {
public:
  /**
   * The four addressable shapes.
   *
   * An array element is the fixed-shape container case: its identity is
   * (array shadow, index), which is stable for the array's life.  A resizable
   * collection has no such slot -- its members move under insertion and
   * removal -- so per-member read-from over one is not something this store
   * can express, and asking it to would be inventing a slot the program does
   * not have.
   *
   * LOC_MAP_STATE is the answer to that, and it deliberately does not try to
   * be a slot: it addresses the container's *whole state*, not one member.  A
   * mutation publishes the immutable state that mutation produced, and a query
   * resolves to the state it may have observed; which member the query then
   * reads out of that state is the container algebra's business and stays in
   * the container code.  The owner is the canonical container id, so a view
   * and the map it views are one location; the slot is SLOT_WHOLE_STATE,
   * because a whole state has no offset.
   */
  enum LocationKind {
    LOC_INSTANCE_FIELD = 0,
    LOC_STATIC_FIELD = 1,
    LOC_ARRAY_ELEMENT = 2,
    LOC_MAP_STATE = 3
  };

  /**
   * The slot of a location that has no offset.
   *
   * Negative on purpose: every real field offset and every array index is
   * non-negative, so this can never be mistaken for one even by a consumer
   * that reads the slot without the kind.
   */
  static const int SLOT_WHOLE_STATE = -3;

  /** Negative values are refusals; see select_carrier and the Java API. */
  enum SelectStatus {
    SELECT_ALREADY_SELECTED   = 0,
    SELECT_NO_ACTIVE_CONTEXT  = -1,
    SELECT_MISSING_METADATA   = -2,
    SELECT_FIELD_NOT_FOUND    = -3,
    SELECT_UNSUPPORTED_TARGET = -4,
    SELECT_VERSION_NOT_FOUND  = -5,
    SELECT_VERSION_AMBIGUOUS  = -6,
    SELECT_INVALID_EDGE       = -7
  };

  /**
   * How comparable the concrete value of a write is.
   *
   * A fingerprint is evidence, never a constraint.  It lets a read rule a
   * writer *out* -- a writer that stored 5 is not the source of a read that
   * observed 10 -- and it never rules one in.  FP_NONE means the value cannot
   * be compared at all, so such a candidate survives every filter; that is the
   * conservative direction and it is deliberate.
   */
  enum FingerprintKind {
    FP_NONE = 0,
    FP_PRIMITIVE = 1,
    FP_NULL = 2,
    // Session-stable identity of the referent.  A raw oop address is not
    // usable here: GC moves it, and a comparison against a moved object would
    // silently exclude the true writer.
    FP_IDENTITY = 3
  };

  enum VersionKind {
    VERSION_INITIAL = 0,
    VERSION_WRITE = 1,
    // One linearized read-modify-write, published as `new = f(old)` by the
    // atomic model rather than by the field store hook.
    VERSION_RMW = 2,
    // One immutable whole-state publication.  The mutation that produced the
    // state is named by the publisher and travels in Version::operation
    // rather than as an enumerator here: the operation vocabulary belongs to
    // whichever model published the state, and baking a collection's verbs
    // into this store would make a generic service the owner of one model's
    // semantics.
    VERSION_STATE = 3
  };

  struct Fingerprint {
    int kind;
    jlong bits;
    Fingerprint() : kind(FP_NONE), bits(0) {}
    Fingerprint(int k, jlong b) : kind(k), bits(b) {}
    /** True only when both sides are comparable and provably different. */
    bool excludes(const Fingerprint &observed) const {
      if (kind == FP_NONE || observed.kind == FP_NONE) return false;
      if (kind != observed.kind) return true;
      return bits != observed.bits;
    }
  };

  struct Location {
    sym_rid_t owner;
    int slot;
    int kind;
    Location() : owner(NULL_SYM_RID), slot(0), kind(LOC_INSTANCE_FIELD) {}
    Location(sym_rid_t owner_id, int location_slot, int location_kind)
        : owner(owner_id), slot(location_slot), kind(location_kind) {}
    bool is_valid() const { return owner != NULL_SYM_RID; }
    bool operator<(const Location &other) const {
      if (owner != other.owner) return owner < other.owner;
      if (slot != other.slot) return slot < other.slot;
      return kind < other.kind;
    }
  };

  struct Version {
    // Drawn from the session's single event-id space, so a fieldVersionId and
    // an event id are the same kind of thing and are directly comparable.
    jlong version_id;
    int version_kind;
    // The publisher's own name for the mutation, for a version whose kind does
    // not name it by itself (VERSION_STATE).  Empty otherwise.
    std::string operation;
    jlong writer_context_id;
    jlong writer_java_thread_id;
    std::string region_id;
    std::string task_id;
    // The value written.  Never NULL: a concrete store publishes a constant.
    Expression *value;
    // Conjunction of the writer's path condition at the write, or NULL for the
    // empty conjunction (true).
    Expression *path_guard;
    Fingerprint fingerprint;
    bool volatile_write;
    // The writer's local step, and its clock at the moment of the write.  The
    // step is what a reader tests against its own clock; the clock is what one
    // candidate is tested against another with.
    jlong writer_step;
    VectorClock writer_clock;
    Version()
        : version_id(0), version_kind(VERSION_WRITE), writer_context_id(0),
          writer_java_thread_id(0),
          value(NULL), path_guard(NULL), volatile_write(false),
          writer_step(0) {}
  };

  typedef std::vector<Version> VersionList;

  /**
   * What a read of a selected location resolved to.
   *
   * RESOLVE_NONE means the location is not selected and the caller keeps
   * whatever answer it already had; the read is not recorded and nothing about
   * it is claimed.
   */
  enum Resolution {
    RESOLVE_NONE = 0,
    RESOLVE_EXACT = 1,
    RESOLVE_GUARDED = 2
  };

  /**
   * Why a read resolved the way it did.  These are the provenance rules, and
   * every one of them is reported with the answer, because "exact" is a claim
   * about evidence and a consumer has to be able to see which evidence.
   *
   *   UNIQUE_VERSION       one candidate existed at all.
   *   VALUE_DISTINGUISHED  several existed, and the value the read actually
   *                        returned is one only one of them wrote.  Sound only
   *                        because the writer set is complete: with a writer
   *                        missing, an untracked store could have written the
   *                        same value.
   *   SYNC_ORDERED         several existed, all of them happen-before this
   *                        read, and one of them happens-after every other.
   *                        Volatile, thread-lifecycle and explicit handoff
   *                        order can create that relation.
   *   AMBIGUOUS_WRITERS    several survived, and nothing in the run separates
   *                        them.  Guarded.
   *   UNTRACKED_WRITER     the value observed is one no candidate wrote, so
   *                        some store outside the tracked set produced it.
   *                        The location is marked incomplete from here on.
   *   INCOMPLETE_WRITER_SET the candidate would have been exact, but this
   *                        location has already lost writers, so exactness
   *                        cannot be claimed.
   */
  enum ReadReason {
    REASON_NOT_SELECTED = 0,
    REASON_UNIQUE_VERSION = 1,
    REASON_VALUE_DISTINGUISHED = 2,
    REASON_SYNC_ORDERED = 3,
    REASON_AMBIGUOUS_WRITERS = 4,
    REASON_UNTRACKED_WRITER = 5,
    REASON_INCOMPLETE_WRITER_SET = 6,
    REASON_PLANNED_PRODUCER_STATE = 7
  };

  struct ReadResult {
    int resolution;
    int reason;
    jlong read_event_id;
    // The selected fieldVersionId when exact; 0 otherwise.
    jlong chosen_version_id;
    // The writer's own expression when exact, a ReadFromExpression when
    // guarded, NULL when nothing was resolved.
    Expression *expression;
    // The chosen writer's clock, meaningful only when exact.  A volatile read
    // acquires this rather than the location's latest release, because a read
    // happens-after the write it actually read and after no other.
    VectorClock writer_clock;
    ReadResult()
        : resolution(RESOLVE_NONE), reason(REASON_NOT_SELECTED),
          read_event_id(0), chosen_version_id(0), expression(NULL) {}
  };

  /**
   * The decision, without the expression.
   *
   * `resolve_read` below answers a scalar read, and the expression it builds
   * has a scalar's shape: the arm of candidate W is W's own value.  That shape
   * is wrong for a location whose versions are whole states -- there the arm
   * has to be *the query applied to* W's state, and only the model that owns
   * the query knows how to write one.  Splitting the decision from the node
   * lets that model reuse every filter here (program order, happens-before,
   * fingerprint, retention) and the same Resolution/ReadReason vocabulary,
   * without this file learning what a map read is.
   *
   * plan_read performs the whole read: it draws the read event, records the
   * observed read-from edge when the writer is proven, and appends the audit
   * record.  The caller's only remaining job is to name the value.
   */
  struct ReadPlan {
    int resolution;
    int reason;
    jlong read_event_id;
    // The proven writer's version id when exact; 0 when guarded.
    jlong chosen_version_id;
    // The versions that survived every filter, in publication order.  For a
    // guarded plan these are exactly the arms the caller must build, in the
    // order rf1..rfk; for an exact plan the chosen one is among them.
    VersionList candidates;
    // Whether the disjunction over `candidates` may be treated as closed.
    // False once a writer has been lost or an untracked one was detected.
    bool writer_set_complete;
    // The chosen writer's clock; meaningful only when exact.
    VectorClock writer_clock;
    ReadPlan()
        : resolution(RESOLVE_NONE), reason(REASON_NOT_SELECTED),
          read_event_id(0), chosen_version_id(0), writer_set_complete(true) {}
  };

  static bool plan_read(const Location &location, const Fingerprint &observed,
                        ReadPlan *plan);

  /**
   * Resolves one read of a selected location against its versions.
   *
   * `observed` is the fingerprint of the value the concrete read actually
   * returned, captured in the same hook as the load.  It is used only to rule
   * writers *out*: a writer that stored a different value is not the source of
   * this read.  It is never asserted as a constraint, and it never rules a
   * writer in on its own.
   *
   * Returns false when the location is not selected, leaving *result at
   * RESOLVE_NONE.
   */
  static bool resolve_read(const Location &location,
                           const Fingerprint &observed, BasicType type,
                           ReadResult *result);

  static const char *resolution_name(int resolution);
  static const char *read_reason_name(int reason);

  static void open_session();
  static void close_session();

  /**
   * Advisory: false means no location in this session is selected, so a hook
   * may skip every version question.  See the concurrency note above.
   */
  static bool has_carriers() { return _carrier_count > 0; }

  /**
   * Selects one location and publishes its INITIAL version.  `initial` and
   * `fingerprint` describe the value the location holds now; the caller builds
   * both outside every engine lock.  Returns the INITIAL version id, or 0 if
   * the location was already selected or is not addressable.
   */
  static jlong select_carrier(const Location &location, Expression *initial,
                              const Fingerprint &fingerprint,
                              const char *descriptor = NULL);
  static bool is_carrier(const Location &location);
  static int carrier_count();

  /**
   * Appends one version for a completed write.  `value` and `path_guard` must
   * already exist; nothing is constructed under the lock.  Returns the new
   * fieldVersionId, or 0 when the location is not selected.
   *
   * `operation` is the publisher's name for the mutation, for a version kind
   * that does not name it by itself.  It is what the ledger event and the
   * evidence report call this write; NULL falls back to the kind's own name.
   */
  static jlong publish(const Location &location, Expression *value,
                       Expression *path_guard, const Fingerprint &fingerprint,
                       bool volatile_write, int version_kind,
                       const char *operation = NULL);

  /**
   * Records that this location has a writer nobody can name.
   *
   * An operation the engine does not model is still a write: it changed the
   * location and left no version behind.  Saying so permanently is what keeps
   * every later read of it guarded with an honest rf_unknown arm instead of
   * answering from a writer set that is quietly missing one.  Returns false
   * when the location is not selected, which is the case where there is
   * nothing to keep honest.
   */
  static bool mark_writer_set_incomplete(const Location &location);

  /** Copies out this location's versions.  Empty when it is not selected. */
  static bool versions_of(const Location &location, VersionList *out,
                          bool *writer_set_complete);

  /**
   * Returns the retained STATE version that is both this task's publication
   * and the location's current Expression, without creating state, events or
   * read records.  A non-positive result is a SelectStatus refusal.
   */
  static jlong current_state_version(const Location &location,
                                     Expression *current,
                                     const std::string &task_id);

  /** Pure session-wide lookup of one retained STATE version by its event id. */
  static jlong lookup_state_version(jlong version_id,
                                    Location *source_location,
                                    Expression **state);

  /**
   * Records the exact read after its destination state alias is installed.
   * The selected edge is provenance, not a Java or VM object identity.
   */
  static jlong record_planned_state_read(const Location &source_location,
                                         jlong version_id,
                                         const char *selected_edge_id);

  /**
   * Pure lookup of the latest scalar/reference field version published by the
   * current task.  The concrete fingerprint and optional field shadow are
   * checks on the current field value; the lookup creates no event, shadow,
   * carrier, INITIAL version or expression.
   */
  static jlong current_field_version(const Location &location,
                                     Expression *current,
                                     const Fingerprint &observed,
                                     const std::string &task_id,
                                     const char *descriptor);

  /**
   * Looks up one retained scalar/reference field version and verifies its
   * exact descriptor.  This is also a pure query.
   */
  static jlong lookup_field_version(jlong version_id,
                                    const char *descriptor,
                                    Location *source_location,
                                    Version *version);

  /**
   * Arms one destination field for a scheduled exact producer read.  The
   * destination is not selected as a carrier and therefore receives no local
   * INITIAL version.  The actual getfield/getstatic consumes the arm and is
   * the operation that records the read and FIELD_READ_FROM edge.
   */
  static jlong plan_exact_field_read(const Location &destination,
                                     jlong version_id,
                                     const char *descriptor,
                                     const char *selected_edge_id);
  static bool has_planned_field_reads() {
    return _planned_field_read_count > 0;
  }
  static bool has_field_evidence_aliases() {
    return _field_evidence_alias_count > 0;
  }
  static bool is_planned_field_read(const Location &destination);
  static bool consume_planned_field_read(const Location &destination,
                                         Expression *current_shadow,
                                         const Fingerprint &observed,
                                         BasicType type,
                                         ReadResult *result);
  static void cancel_planned_field_reads(const Location &destination);
  /** Pure per-field evidence alias for getSharedFieldVersions. */
  static Location evidence_location(const Location &destination);

  // Raw bits of one stored primitive, in the one encoding both the version
  // and the read compare against.  Float and double go through their bit
  // patterns rather than a numeric widening, so that -0.0 and NaN compare as
  // the values the program actually stored.
  static jlong raw_bits(jboolean value) { return (jlong)(value & 1); }
  static jlong raw_bits(jbyte value)    { return (jlong) value; }
  static jlong raw_bits(jchar value)    { return (jlong) value; }
  static jlong raw_bits(jshort value)   { return (jlong) value; }
  static jlong raw_bits(jint value)     { return (jlong) value; }
  static jlong raw_bits(jlong value)    { return value; }
  static jlong raw_bits(jfloat value)   { return (jlong) jint_cast(value); }
  static jlong raw_bits(jdouble value)  { return jlong_cast(value); }

  /** Builds the constant/reference expression that describes a stored value. */
  static Expression *primitive_expression(BasicType type, jlong bits);
  static Expression *reference_expression(oop value);
  static Fingerprint primitive_fingerprint(BasicType type, jlong bits);
  static Fingerprint reference_fingerprint(oop value);

  static const char *location_kind_name(int kind);
  static const char *version_kind_name(int kind);
  static const char *fingerprint_kind_name(int kind);
  /**
   * What one version's `versionKind` reads as.
   *
   * The kind's own name, except for a whole-state version, which reads as
   * `STATE_<operation>` so that the mutation is named where a consumer
   * already looks for the kind.  This is a wider vocabulary in an existing
   * string member, not a new member: the record's shape is unchanged and
   * schemaVersion stays 1.
   */
  static std::string version_label(const Version &version);

  /** Serializes one location's versions as evidence, for tests and tracing. */
  static std::string describe(const Location &location);

private:
  // Bounded on purpose; see the retention note above.  A location that needs
  // more than this many live writers is not a bounded carrier.
  static const size_t MAX_VERSIONS_PER_LOCATION = 64;
  // The read log is evidence rather than a constraint, so its bound is larger
  // and its truncation is reported separately from the writer set.  Sized for
  // a service workload in which one selected map is read by the target path
  // and by every observer of it: a few hundred reads per location is ordinary,
  // so this is generous enough that hitting it means something unexpected.
  static const size_t MAX_READS_PER_LOCATION = 1024;

  /** One resolved read, kept so that a consumer can audit the decision. */
  struct ReadRecord {
    jlong read_event_id;
    jlong reader_context_id;
    jlong reader_java_thread_id;
    std::string region_id;
    int resolution;
    int reason;
    jlong chosen_version_id;
    int candidate_count;
    std::string selected_edge_id;
    Fingerprint observed;
    ReadRecord()
        : read_event_id(0), reader_context_id(0), reader_java_thread_id(0),
          resolution(RESOLVE_NONE),
          reason(REASON_NOT_SELECTED), chosen_version_id(0),
          candidate_count(0) {}
  };

  struct Slot {
    VersionList versions;
    std::vector<ReadRecord> reads;
    // Exact JVM field descriptor for scalar/reference field locations.  Empty
    // for arrays and whole-container state, whose admission APIs are separate.
    std::string descriptor;
    bool writer_set_complete;
    // The read log's own completeness, kept apart from the writer set's.
    // Dropping a read never makes the writer set incomplete -- a read is
    // evidence of a decision, not a writer -- but it does make the log a
    // sample instead of the whole record, and the two must not be confused.
    bool read_log_complete;
    // How many were really published or served, next to how many are no
    // longer shown.  Without the totals a reader cannot tell a location that
    // sits well under its bound from one sitting exactly on it, and those are
    // different findings: the second is one more event away from truncating.
    jlong versions_observed;
    jlong versions_dropped;
    jlong reads_observed;
    jlong reads_dropped;
    Slot()
        : writer_set_complete(true), read_log_complete(true),
          versions_observed(0), versions_dropped(0),
          reads_observed(0), reads_dropped(0) {}
  };

  typedef std::map<Location, Slot> SlotStore;

  struct PlannedFieldKey {
    Location destination;
    jlong reader_context_id;
    PlannedFieldKey() : reader_context_id(0) {}
    PlannedFieldKey(const Location &location, jlong context_id)
        : destination(location), reader_context_id(context_id) {}
    bool operator<(const PlannedFieldKey &other) const {
      if (destination < other.destination) return true;
      if (other.destination < destination) return false;
      return reader_context_id < other.reader_context_id;
    }
  };

  struct PlannedFieldRead {
    Location source;
    jlong version_id;
    std::string descriptor;
    std::string selected_edge_id;
    Expression *expression;
    Fingerprint fingerprint;
    VectorClock writer_clock;
    PlannedFieldRead() : version_id(0), expression(NULL) {}
  };

  typedef std::map<PlannedFieldKey, PlannedFieldRead> PlannedFieldReadStore;
  typedef std::map<PlannedFieldKey, Location> FieldEvidenceAliasStore;

  static bool _open;
  static SlotStore _slots;
  // Relaxed reader, mutex-guarded writer.  Deliberately not the map's size:
  // reading std::map::size() without the lock is not safe.
  static volatile int _carrier_count;
  // Advisory early-out for ordinary getfield/putfield bytecodes.  Every use
  // re-checks the pending store under _mutex.
  static volatile int _planned_field_read_count;
  static volatile int _field_evidence_alias_count;
  static pthread_mutex_t _mutex;
  static PlannedFieldReadStore _planned_field_reads;
  static FieldEvidenceAliasStore _field_evidence_aliases;

  static Slot *find_slot_locked(const Location &location);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP
