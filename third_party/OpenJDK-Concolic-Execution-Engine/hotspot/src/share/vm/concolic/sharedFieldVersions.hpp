#ifndef SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP
#define SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"
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
 * object.  Versioning all of them would append a record and a folded path
 * guard on a bytecode that a workload executes millions of
 * times, which is a cost no bounded analysis can pay for state it will never
 * ask about.  A location is therefore *tracked* before it is versioned, and
 * tracking is by value: the first symbolic value stored here starts the log
 * (`is_tracked`, `publish_value`).  Nothing declares a location in advance,
 * because a declaration is a guess about what will matter and a symbolic
 * store is evidence that it already does.
 *
 * Tracking by value is what makes the hook affordable.  When no location is
 * tracked at all the hooks read one relaxed counter and stop, which is why
 * every pre-existing workload keeps its old cost exactly.  When tracked
 * locations do exist, an untracked one is still rejected by one map lookup,
 * and only a tracked location pays for a version.
 *
 * A container's log opens with an INITIAL version holding the state the
 * location started in (`publish_initial`).  Without it the mutation chain
 * would have no receiver a reader can resolve, and the resolver would have to
 * invent one.  With it, "the state this location started in" is an ordinary
 * candidate with ordinary evidence.
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
 * treated an incomplete set as complete could omit a feasible writer.
 * Truncation therefore clears
 * `writer_set_complete`, which is a permanent property of the location and is
 * reported with every answer derived from it.
 *
 * The read log is bounded the same way and is *not* silent about it.  A read
 * is evidence of a decision that was already made, so losing one leaves every
 * writer set exactly as complete as it was; what it does destroy is the claim
 * that the log is the whole record.  A consumer that counted the retained
 * rows would otherwise read a truncated log as closed read coverage, which is
 * a stronger statement than the store can make.  Truncation therefore clears
 * `read_log_complete` permanently, reported as `readLogTruncated`.  The two
 * completeness flags stay separate because losing a read record does not
 * remove a writer candidate.
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

  /** Negative values are refusals; see the Java API. */
  enum SelectStatus {
    SELECT_ALREADY_SELECTED   = 0,
    SELECT_NO_ACTIVE_CONTEXT  = -1,
    SELECT_MISSING_METADATA   = -2,
    SELECT_FIELD_NOT_FOUND    = -3,
    SELECT_UNSUPPORTED_TARGET = -4
  };

  /** Refusals for one replay-only concrete primitive read operand. */
  enum ReplayReadStatus {
    REPLAY_READ_PENDING          = 0,
    REPLAY_READ_NO_CONTEXT       = -1,
    REPLAY_READ_MISSING_METADATA = -2,
    REPLAY_READ_FIELD_NOT_FOUND  = -3,
    REPLAY_READ_UNSUPPORTED      = -4,
    REPLAY_READ_NOT_SELECTED     = -5,
    REPLAY_READ_ALREADY_PENDING  = -6,
    REPLAY_READ_UNKNOWN_TOKEN    = -7,
    REPLAY_READ_WRONG_CONTEXT    = -8
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

  /**
   * The bytecode site one logged event stood at.
   *
   * Identity v3 asks every read and write endpoint where in the region's
   * control structure it happened, and the frames are the runtime's to
   * journal -- but the innermost one is a bytecode site, and only the VM
   * stands at it.  The log used to record no site at all, so two reads of one
   * location by one occurrence at different places in the code were
   * indistinguishable and collapsed onto one endpoint id.
   *
   * Kept as the JVM's own components, never as a rendered site id: the
   * consumer spells the method part its own way and must be the only place
   * that does.  `bci` is -1, and every member empty, when the event was
   * published from a VM entry with no bytecode under it.
   *
   * No loop iteration count: this engine does not count loop back edges, so
   * it has nothing to say about LOOPOWN and says nothing rather than 0.
   */
  struct EventSite {
    std::string class_name;
    std::string method_name;
    std::string method_descriptor;
    int bci;
    EventSite() : bci(-1) {}
    bool stated() const { return !class_name.empty(); }
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

  /**
   * What one whole-state carrier's INITIAL value says about the content the
   * container held before the region selected it.
   *
   * Three states, not two, and the third is the one that used to be missing.
   * `stated` means the value stands on a SNAPSHOT_BASE this recorder
   * installed, so the content is exactly `entries` members and zero is a real
   * answer - the exact empty collection, which is the most constrained
   * initial state there is.  `truncated` means the engine knows it did not
   * state the content: the entry bound refused it, or the container already
   * carried a recorded mutation history whose base could not be recovered.
   * Neither means nothing was ever offered, and a reader must then treat the
   * contents as unknown for want of an offer rather than for want of an
   * answer.
   */
  struct InitialSnapshot {
    bool stated;
    bool truncated;
    // Set when the container's class is admitted by a model but is not one
    // the engine can read the members of.  Published by name so the runtime
    // raises a blocking gap instead of reading an absent snapshot as "held
    // nothing".
    std::string unsupported_class;
    // Members the INITIAL value states, or the count that went unstated, or
    // -1 when even the count is unknown.
    int entries;
    InitialSnapshot() : stated(false), truncated(false), entries(0) {}
    // Whether the version should publish an `initialSnapshot` block at all.
    bool present() const {
      return stated || truncated || !unsupported_class.empty();
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
    std::string region_id;
    std::string task_id;
    jlong region_enter_event_id;
    // The value written.  Never NULL: a concrete store publishes a constant.
    Expression *value;
    // Conjunction of the writer's path condition at the write, or NULL for the
    // empty conjunction (true).
    Expression *path_guard;
    // Set only on the INITIAL version of a whole-state carrier the recorder
    // was told the contents of.  `entries` is how many the container held;
    // `truncated` says the snapshot was refused for holding too many, so the
    // value above is still the opaque state root and a reader must treat the
    // pre-selection contents as unknown rather than empty.
    bool initial_snapshot_present;
    int initial_snapshot_entries;
    bool initial_snapshot_truncated;
    // Non-empty when the snapshot was refused because the container's class
    // is not one this engine walks.
    std::string initial_snapshot_unsupported_class;
    // Where this event stood; see EventSite.
    EventSite site;
    Version()
        : version_id(0), version_kind(VERSION_WRITE), writer_context_id(0),
          region_enter_event_id(0), value(NULL), path_guard(NULL),
          initial_snapshot_present(false), initial_snapshot_entries(0),
          initial_snapshot_truncated(false) {}
  };

  typedef std::vector<Version> VersionList;

  /**
   * What a read of a selected location resolved to.
   *
   * RESOLVE_NONE means the location is not selected and the caller keeps
   * whatever answer it already had; the read is not recorded and nothing about
   * it is claimed.
   */
  struct ReadResult {
    // A boundary over a ReadFromExpression containing every retained writer.
    Expression *expression;
    ReadResult() : expression(NULL) {}
  };

  /**
   * The decision, without the expression.
   *
   * `resolve_read` below answers a scalar read, and the expression it builds
   * has a scalar's shape: the arm of candidate W is W's own value.  That shape
   * is wrong for a location whose versions are whole states -- there the arm
   * has to be *the query applied to* W's state, and only the model that owns
   * the query knows how to write one.  Splitting the decision from the node
   * lets that model reuse the same complete retained writer set without this
   * file learning what a map read is.  Runtime order and concrete equality do
   * not filter the set.
   */
  struct ReadPlan {
    jlong read_event_id;
    // The site the read stood at, for the node build_read_from emits.
    EventSite site;
    // The version live when the read ran: the newest one retained for the
    // location.  The run performed one read and the location held one value;
    // the set of versions it did not hold was never evidence about it.
    Version observed;
    // Coverage metadata.  False once a writer has been lost or an untracked
    // one was detected; it blocks closed/final claims but never changes which
    // version the read observed.
    bool writer_set_complete;
    ReadPlan() : read_event_id(0), writer_set_complete(true) {}
  };

  /**
   * The version live at `location` right now, without selecting or recording.
   *
   * Returns 0 when the location is not a tracked carrier or holds no version.
   * `version_kind`, when non-NULL, receives that version's label.
   */
  static jlong live_version(const Location &location,
                            std::string *version_kind);

  static bool plan_read(const Location &location, ReadPlan *plan);

  /**
   * The read-from node every reader of a selected location publishes.
   *
   * `observed_value` is what the observed version resolves to for this
   * particular read: its own value for a scalar location, the query applied to
   * its state for a container one.  That one substitution is the whole
   * difference between the scalar reader here and the container reader in
   * containerSupport.cpp -- the version id, version label and the consumer
   * boundary around it are identical.
   *
   * `type_name` is the emitted Java type for both the node and the boundary.
   */
  static Expression *build_read_from(
      const ReadPlan &plan, const Location &location,
      const std::string &type_name, Expression *observed_value);

  /**
   * Resolves one read of a selected location against its versions.
   *
   * Returns false when the location is not selected, leaving *result at
   * its empty value.
   */
  static bool resolve_read(const Location &location, BasicType type,
                           ReadResult *result);

  /**
   * One-shot concrete operand override; symbolic resolve_read is unchanged.
   *
   * `region_enter_event_id` is the region occurrence that armed the read, so
   * that closing that region -- and only that region -- abandons it.
   */
  static jlong arm_primitive_read(jlong context_id,
                                  jlong region_enter_event_id,
                                  const Location &location,
                                  BasicType type, jlong value_bits);
  static bool consume_primitive_read(jlong context_id,
                                     const Location &location,
                                     BasicType type, jlong *value_bits);
  /** Positive iff consumed; zero cancels an armed but unconsumed receipt. */
  static jlong confirm_primitive_read(jlong context_id, jlong token);

  /**
   * Drops the arms one region left behind when it ended.
   *
   * An arm is a one-shot override of *the read that the arming code is about
   * to perform*.  If that read never happens -- the branch was not taken, the
   * frame threw, the replay decided otherwise -- the entry used to survive
   * keyed only by (context, location), so the next read of the same field,
   * arbitrarily later and in a different region of the same thread, silently
   * consumed a value that was never meant for it.  A region boundary is the
   * point at which such an arm is provably abandoned, so it is dropped there.
   *
   * Regions nest on one thread context, so the boundary that abandons an arm
   * is the region that armed it and not merely the thread it ran on: purging
   * every arm of the context when an INNER region closes would drop the
   * enclosing region's still-pending arms.  `region_enter_event_id` names the
   * closing region occurrence; zero means every region of this context, which
   * is what forget_context() needs.
   *
   * Receipts for arms that *were* consumed are deliberately kept: they are
   * evidence the caller still has to confirm, and confirmation happens during
   * region close.  forget_context() below is what retires those, at the point
   * where no caller can reach them any more.
   */
  static void discard_armed_reads(jlong context_id,
                                  jlong region_enter_event_id);

  /**
   * Retires every replay-read record owned by one thread context.
   *
   * Called when the context itself goes away (detach, or an owner thread that
   * exited).  Both stores are keyed by context id and were previously purged
   * only in close_session(), so a workload session that outlived many thread
   * contexts accumulated their records and let a later context with a
   * recycled id observe them.
   */
  static void forget_context(jlong context_id);

  static void open_session();
  static void close_session();

  /**
   * Advisory: false means no location in this session is selected, so a hook
   * may skip every version question.  See the concurrency note above.
   */
  static bool has_carriers() { return _carrier_count > 0; }

  /**
   * Whether this location's contents are being kept.
   *
   * They are, from the first symbolic value written here onwards.  There is
   * no declaration: a location is tracked because of what was stored in it,
   * not because anything said in advance that it might matter.
   */
  static bool is_tracked(const Location &location);

  /**
   * Every tracked location, as the envelopes `describe()` emits.
   *
   * The read-out the runtime needs once retention is by value: it no longer
   * knows which locations exist, because it never saw the writes that started
   * them.  One document, `SHARED_TRACKED_LOCATIONS`, holding one
   * `SHARED_FIELD_VERSIONS` envelope per location and one expression table
   * for all of them.
   *
   * `after_event_id` selects every location carrying a version or a read at
   * or after that point on the session clock, and each selected location is
   * returned with its *complete* retained version list -- a read that
   * observed an older version still needs that version's expression.  0 means
   * everything.  A region scopes itself by passing its entry event.
   *
   * `max_bytes` bounds one answer: the read-out stops at a location boundary,
   * reports `complete: false` and names `nextAfterEventId` to resume from.  0
   * means no budget.  The first location is always emitted, so a budget
   * smaller than one envelope makes progress rather than looping.
   *
   * Locations ascend by their lowest event id, so a resume is well defined.
   */
  static std::string tracked_locations(jlong after_event_id, jint max_bytes);

  /**
   * Versions one completed write, by value.
   *
   * `symbolic` says whether the value being stored is itself symbolic.  A
   * symbolic store is always kept, and starts this location's log if it is
   * the first.  A concrete store is kept only where a log already exists --
   * there it must be, or a later read would resolve to an expression this
   * store has overwritten -- and is free everywhere else.
   *
   * Returns the new fieldVersionId, or 0 when nothing was recorded.
   */
  static jlong publish_value(const Location &location, Expression *value,
                             Expression *path_guard, bool symbolic,
                             int version_kind,
                             const char *operation = NULL);

  /**
   * Starts an untracked location's log with an INITIAL base version.
   *
   * A container's relation chain resolves as base + PUT/REMOVE..., so the
   * base has to be a version of its own or the first mutation has no
   * receiver a reader can resolve.  Under retention by value the log begins
   * at the first symbolic write, so the base is published there rather than
   * at a declaration that may never come or may come later.
   *
   * Returns 0 when the location is already tracked.
   */
  static jlong publish_initial(const Location &location, Expression *base,
                               const InitialSnapshot &snapshot);

  /**
   * Appends one version for a completed write.  `value` and `path_guard` must
   * already exist; nothing is constructed under the lock.  Returns the new
   * fieldVersionId, or 0 when the location has no log and `start_tracking` is
   * false.
   *
   * `operation` is the publisher's name for a whole-state mutation; NULL
   * falls back to the version kind.  Prefer publish_value(): it is the one
   * that decides, from the value, whether the write is kept at all.
   */
  static jlong publish(const Location &location, Expression *value,
                       Expression *path_guard, int version_kind,
                       const char *operation = NULL,
                       bool start_tracking = false,
                       const InitialSnapshot *snapshot = NULL);

  /**
   * Records that this location has a writer nobody can name.
   *
   * An operation the engine does not model is still a write: it changed the
   * location and left no version behind.  Saying so permanently prevents a
   * later query over the retained candidates from being published as closed.
   * Returns false when the location is not selected, which is the case where
   * there is nothing to keep honest.
   */
  static bool mark_writer_set_incomplete(const Location &location);

  /** Copies out this location's versions.  Empty when it is not selected. */
  static bool versions_of(const Location &location, VersionList *out,
                          bool *writer_set_complete);

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

  /**
   * What a field holds right now, as an expression.
   *
   * Read straight from the object rather than from an operand stack, so a
   * projection can state the value this run observed wherever it is built --
   * including before the concrete load has been pushed.
   *
   * A primitive field answers with its constant.  A reference-typed one
   * answers with the referent's identity in the one spelling an owner
   * identity has (`reference_expression`), so that a read reference and the
   * owner of another read are the same term, and with the null symbol when
   * the field held null.  Either way the read states what it read: a
   * reference-typed field used to answer NULL, which left its projection
   * with nothing for the composer to value it by.
   */
  static Expression *field_value(oop owner, int field_offset,
                                 BasicType type);

  static const char *location_kind_name(int kind);
  static const char *version_kind_name(int kind);
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

  /**
   * Installs the guarded-store table for this session and returns how many
   * store methods it names.
   *
   * A concrete store is evidence only when it is CONTROL-DEPENDENT on a
   * symbolic decision -- the store a flipped branch would change.  "Anything
   * after any symbolic branch" is not that: on 17960's seed it logged
   * DigestBase#engineUpdate, HeapByteBuffer#_put and nine more protobuf
   * serialization internals reached from the anchor's own decision, and the
   * explorer read those versions as six BLOCKING TOPOLOGY_DIVERGENCE.
   *
   * Control dependence is a static fact the PLAN stage already computes by
   * post-dominance and publishes per write site, so the VM is told it rather
   * than guessing: one line per store method,
   * `<internal/Class>#<name><descriptor>\t<guardSite>[,<guardSite>...]`,
   * where the guard sites are the woven branch site ids the runtime passes to
   * markConcolicBranch.  A method the table does not name never starts a log
   * by a concrete store, and neither does one whose guard sites have all not
   * decided anything on this path.
   *
   * Installing replaces the whole table; an empty one admits nothing, which
   * is the fail-closed state before a plan has been installed.
   */
  static int install_guarded_store_sites(const char *table);

  /**
   * Whether a concrete store by the calling thread, right here, is
   * control-dependent on a symbolic decision it has already taken.
   */
  static bool guarded_store_admitted();

  /** Where the calling thread stands, for one logged event to state. */
  static EventSite current_site();

  /** The one writer of a logged event's `site` member. */
  static void write_site(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      const EventSite &site);

  /** One resolved read, kept so that a consumer can audit the decision. */
  struct ReadRecord {
    jlong read_event_id;
    jlong reader_context_id;
    std::string region_id;
    std::string task_id;
    jlong region_enter_event_id;
    // Where this event stood; see EventSite.
    EventSite site;
    ReadRecord()
        : read_event_id(0), reader_context_id(0),
          region_enter_event_id(0) {}
  };

  /**
   * One location's retained history.
   *
   * Public only because the read-out's ordering helpers take one by
   * reference; it is engine-internal state and nothing outside this file
   * constructs or mutates one.
   */
  struct Slot {
    VersionList versions;
    std::vector<ReadRecord> reads;
    bool writer_set_complete;
    bool read_log_complete;
    Slot() : writer_set_complete(true), read_log_complete(true) {}
  };

  /** Serializes one location's versions as evidence, for tests and tracing. */
  static std::string describe(const Location &location);

private:
  /**
   * Writes one SHARED_FIELD_VERSIONS envelope, without closing its object and
   * without an expression table: the caller owns both, so a single-location
   * answer and the whole read-out emit byte-identical envelopes.  Returns
   * true when the envelope was cut short by `budget_bytes` (0 = the default
   * per-envelope bound).
   */
  static bool write_versions_envelope(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      const rapidjson::StringBuffer &buffer,
      VmExpressionArtifactScope &expression_artifact,
      const Location &location, const VersionList &versions,
      const std::vector<ReadRecord> &reads, bool selected, bool complete,
      bool read_log_complete, size_t budget_bytes);

  // Bounded on purpose; see the retention note above.  A location that needs
  // more than this many live writers is not a bounded carrier.
  static const size_t MAX_VERSIONS_PER_LOCATION = 64;
  // The read log is evidence rather than a constraint, so its bound is larger
  // and its truncation is reported separately from the writer set.  Sized for
  // a service workload in which one selected map is read by the target path
  // and by every observer of it: a few hundred reads per location is ordinary,
  // so this is generous enough that hitting it means something unexpected.
  static const size_t MAX_READS_PER_LOCATION = 1024;

  typedef std::map<Location, Slot> SlotStore;

  struct PendingReadKey {
    jlong context_id;
    Location location;
    PendingReadKey() : context_id(0) {}
    PendingReadKey(jlong context, const Location &field)
        : context_id(context), location(field) {}
    bool operator<(const PendingReadKey &other) const {
      if (context_id != other.context_id) return context_id < other.context_id;
      return location < other.location;
    }
  };

  struct PendingPrimitiveRead {
    jlong token;
    // The region occurrence that armed this read.  Consumption does not look
    // at it -- the arming code's own read is the consumer wherever it is --
    // but a region-boundary purge drops only what that region armed.
    jlong region_enter_event_id;
    BasicType type;
    jlong value_bits;
    PendingPrimitiveRead()
        : token(0), region_enter_event_id(0), type(T_ILLEGAL),
          value_bits(0) {}
  };

  typedef std::map<PendingReadKey, PendingPrimitiveRead> PendingReadStore;
  /** receipt token -> the armed entry it names, so confirm is a lookup. */
  typedef std::map<jlong, PendingReadKey> ArmedTokenIndex;
  typedef std::map<jlong, jlong> ConsumedReadStore;

  static bool _open;
  static SlotStore _slots;
  static PendingReadStore _pending_primitive_reads;
  static ArmedTokenIndex _armed_read_tokens;
  /** receipt token -> consuming context */
  static ConsumedReadStore _consumed_primitive_reads;
  // Relaxed reader, mutex-guarded writer.  Deliberately not the map's size:
  // reading std::map::size() without the lock is not safe.
  static volatile int _carrier_count;
  static pthread_mutex_t _mutex;

  static Slot *find_slot_locked(const Location &location);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP
