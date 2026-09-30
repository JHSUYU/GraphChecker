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

class ConstantPoolCacheEntry;
class Method;
class fieldDescriptor;

/**
 * Versioned writes to the session's tracked shared locations.
 *
 * Every write to a *tracked* location appends an immutable version carrying
 * the writer's evidence, so a later read names its provenance instead of
 * inheriting whatever pointer happened to survive in a field shadow.
 *
 * ---------------------------------------------------------------------------
 * What is versioned, and why not everything
 * ---------------------------------------------------------------------------
 *
 * A location is tracked before it is versioned, and tracking is by value:
 * the first symbolic value stored here starts the log, as does a concrete
 * store control-dependent on a symbolic decision (`publish_value`), a mint,
 * an attach, or a woven observation (`publish_initial`).  Nothing declares a
 * location in advance.  When no location is tracked the hooks read one
 * relaxed counter and stop; an untracked location is rejected by one lookup.
 *
 * A container's log opens with an INITIAL version holding the state the
 * location started in; so does a scalar's whose log a guarded concrete store
 * starts (the word the store replaced), so that "this store did not happen"
 * is an ordinary candidate with ordinary evidence.
 *
 * ---------------------------------------------------------------------------
 * One critical section per tracked access
 * ---------------------------------------------------------------------------
 *
 * A tracked scalar access and its log entry are one critical section under
 * the location's lock (a stripe, `lock`): a store does the concrete store,
 * mints its version id and appends; a load does the concrete load, compares
 * the word it loaded with the newest version's `stored` word, and records
 * the read.  Log order is therefore heap order.  It used to be two sections
 * -- a store published after its concrete store, a read compared after its
 * concrete load -- and both windows produced spurious UNOBSERVED versions
 * (a reader that loaded the new word before its version landed, or the old
 * word after it had): unobs/results-s48.txt and review1.
 *
 * So a mismatch can only mean a writer no hook saw (a muted subtree, JNI),
 * and the location is marked incomplete.  The read names a retained version
 * that stored exactly the loaded word when there is one, but is NOT exact:
 * log order is heap order, so a newer hooked version certainly overwrote
 * that one and an unhooked writer put the word back -- a join to it would be
 * an edge that did not happen, and the read is pinned to what it returned
 * instead.  Otherwise it publishes a VERSION_UNOBSERVED version holding the
 * loaded constant, minted under the lock so that it precedes the read on the
 * session clock and lands before any later store.
 *
 * Every read states whether its observation is exact (`observed_exact`): the
 * word it loaded equals its observed version's stored word, the version is
 * the newest, and no unhooked write came between.  An exact read joins its
 * version even at an incomplete location.  `writer_set_complete` keeps its
 * meaning, the location's writer set; `unnamed_writer` says a writer the log
 * never named reached the location (every reason but the version bound),
 * which is what removes alternative writers from a read.
 *
 * A reference cell's word is its referent's session id (named on demand,
 * 0 for null), so a read of a reference is verified the same way: a
 * reflective or Unsafe set no hook saw is an UNOBSERVED version holding the
 * loaded referent's identity.  Whole-state (container) versions carry no
 * word: a container's mutation is a Java call no lock can span, so its
 * version is published by the model after the call, and its reads are never
 * exact.
 *
 * A reference store states what the referent's container state was
 * (`referentState`): the version of the MAP_STATE location of the container
 * the referent is, or views or wraps, live at the store.  It is taken
 * before the carrier's stripe (prepare_referent), never under it: the
 * referent's stripe is released first, and a container with no log starts
 * one there, with a stated snapshot.
 *
 * ---------------------------------------------------------------------------
 * Retention, and what an incomplete writer set means
 * ---------------------------------------------------------------------------
 *
 * A location keeps at most MAX_VERSIONS_PER_LOCATION versions; dropping the
 * oldest clears `writer_set_complete` permanently, as does a writer the VM
 * detected but could not version (`mark_writer_set_incomplete`).  Its
 * reasons are published (`incompleteReasons`).  Only the version bound drops
 * writers the log once named -- every retained one is still a real, exact
 * writer -- so only it leaves `unnamed_writer` false: a hot field past 64
 * stores keeps its alternatives.  The read log is bounded too and says so
 * (`readLogTruncated`).
 *
 * ---------------------------------------------------------------------------
 * Locks
 * ---------------------------------------------------------------------------
 *
 * A stripe guards the contents of every Slot that hashes to it and the heap
 * word of every location that does.  `_mutex` guards the slot map's shape
 * (find/insert), the carrier count and the guarded-store table, and is taken
 * inside a stripe, never around one.  Nothing that can block is done under
 * either; an Expression may be built under a stripe (the arena lock is a
 * leaf), which is how a concrete store's constant or an UNOBSERVED constant
 * is made only when the location turns out to be tracked.  The engine-wide
 * order is
 *
 *     membership -> {heap, broker, stripe -> versions} -> arena
 *
 * and a caller holding several stripes takes them in ascending index order
 * (`lock_stripes`).  `has_carriers()` reads a plain counter on purpose: an
 * advisory early-out on the hottest bytecodes, re-checked under the lock.
 */
class SharedFieldVersions {
public:
  /**
   * The four addressable shapes.  LOC_MAP_STATE addresses a container's
   * whole state: its owner is the canonical container id (a view and the map
   * it views are one location) and its slot is SLOT_WHOLE_STATE.
   */
  enum LocationKind {
    LOC_INSTANCE_FIELD = 0,
    LOC_STATIC_FIELD = 1,
    LOC_ARRAY_ELEMENT = 2,
    LOC_MAP_STATE = 3
  };

  /** The slot of a location that has no offset; never a real offset. */
  static const int SLOT_WHOLE_STATE = -3;

  enum VersionKind {
    VERSION_INITIAL = 0,
    VERSION_WRITE = 1,
    // One linearized read-modify-write, `new = f(old)`, published by the
    // compare-and-swap that performed it (see UnsafeWrite).
    VERSION_RMW = 2,
    // One immutable whole-state publication; the mutation is named by the
    // publisher in Version::operation.
    VERSION_STATE = 3,
    // A write no hook saw, published by the read that found its word in the
    // heap: the loaded constant, no writer, no region, no guard.
    VERSION_UNOBSERVED = 4
  };

  /**
   * The concrete word one store left, or one read loaded, in the raw_bits()
   * encoding for a scalar.  A reference's word is T_OBJECT and its
   * referent's session id, not its address (which the collector moves); null
   * is 0.  A box of an integral wrapper stored in a wrapper-typed field
   * states its primitive (boxed_word), and null the null word: the field
   * holds a value or nothing, and the two are different words.  T_ILLEGAL
   * means no word is stated: a whole container state has none.
   */
  struct ConcreteBits {
    BasicType type;
    jlong bits;
    ConcreteBits() : type(T_ILLEGAL), bits(0) {}
    ConcreteBits(BasicType word_type, jlong word_bits)
        : type(word_type), bits(word_bits) {}
    bool stated() const { return type != T_ILLEGAL; }
    bool is_reference() const { return type == T_OBJECT; }
    bool is_null() const { return type == T_OBJECT && bits == 0; }
    bool contradicts(const ConcreteBits &other) const {
      return stated() && other.stated()
          && (bits != other.bits || type != other.type);
    }
    bool equals(const ConcreteBits &other) const {
      return stated() && other.stated() && bits == other.bits
          && type == other.type;
    }
  };

  /**
   * The bytecode site one logged event stood at, in the JVM's own
   * components.  `bci` is -1, and every member empty, when the event was
   * published from a VM entry with no bytecode under it.
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
   * container held before its log began: `stated` (exactly `entries`
   * members), `truncated` (over the bound), or refused by name
   * (`unsupported_class`).  Only `stated` is a statement of content.
   */
  struct InitialSnapshot {
    bool stated;
    bool truncated;
    std::string unsupported_class;
    int entries;
    InitialSnapshot() : stated(false), truncated(false), entries(0) {}
    // Whether the version should publish an `initialSnapshot` block at all.
    bool present() const {
      return stated || truncated || !unsupported_class.empty();
    }
  };

  /**
   * What a reference store's referent was, when it is a modeled container
   * (or a view or wrapper of one): its MAP_STATE location's owner and the
   * version live when the store ran, or why that cannot be stated.  Neither
   * for any other referent.
   */
  struct ReferentState {
    sym_rid_t owner;
    jlong version_id;
    std::string refused;
    ReferentState() : owner(NULL_SYM_RID), version_id(0) {}
    bool present() const { return version_id > 0 || !refused.empty(); }
  };

  /** Who wrote or read: the calling thread's region, and where it stood. */
  struct Attribution {
    jlong context_id;
    std::string region_id;
    std::string task_id;
    jlong region_enter_event_id;
    EventSite site;
    Attribution() : context_id(0), region_enter_event_id(0) {}
  };

  struct Version {
    // Drawn from the session's single event-id space.
    jlong version_id;
    int version_kind;
    // The publisher's own name for a whole-state mutation; empty otherwise.
    std::string operation;
    Attribution writer;
    // The value written.  Never NULL.
    Expression *value;
    // The concrete word the store left, when it is a scalar's.
    ConcreteBits stored;
    // `stored` as a constant, built once for the reads that return it
    // (item 6: a read of a matching word shares it instead of minting one).
    Expression *stored_constant;
    // Conjunction of the writer's path condition, or NULL for true.
    Expression *path_guard;
    bool initial_snapshot_present;
    bool initial_snapshot_stated;
    int initial_snapshot_entries;
    bool initial_snapshot_truncated;
    std::string initial_snapshot_unsupported_class;
    // A reference store's referent's container state (see ReferentState).
    ReferentState referent;
    Version()
        : version_id(0), version_kind(VERSION_WRITE), value(NULL),
          stored_constant(NULL), path_guard(NULL),
          initial_snapshot_present(false), initial_snapshot_stated(false),
          initial_snapshot_entries(0), initial_snapshot_truncated(false) {}
  };

  typedef std::vector<Version> VersionList;

  /**
   * One store, prepared outside the lock: its value (NULL for a concrete
   * store, whose constant is built only if the location turns out tracked),
   * its guard and attribution, and whether it may start the location's log.
   */
  struct Store {
    Location location;
    Expression *value;
    Expression *path_guard;
    bool symbolic;
    // Symbolic, or control-dependent on a decision the thread took (D5).
    bool starts_log;
    int version_kind;
    std::string operation;
    Attribution writer;
    // What the stored referent's container state was, taken before the
    // lock (prepare_referent); `referent_prepared` says it was asked.
    ReferentState referent;
    bool referent_prepared;
    // Filled under the lock by begin_store_locked: whether the store is
    // versioned, whether its cell holds a reference (whose word is its
    // referent's id), and, when it starts the log, the value it replaced,
    // which is published first as the INITIAL.
    bool versioned;
    bool reference_cell;
    Expression *base_value;
    ConcreteBits base;
    Store()
        : value(NULL), path_guard(NULL), symbolic(false), starts_log(false),
          version_kind(VERSION_WRITE), referent_prepared(false),
          versioned(false), reference_cell(false), base_value(NULL) {}
  };

  /**
   * One heap cell a location names: its holder (the owner object, a static
   * mirror, or the array) and what it holds.  `type` is the field's or
   * element's BasicType; `boxed` marks a wrapper-typed field
   * (wrapper_value_type), whose word is its box's primitive.
   */
  struct Cell {
    oop holder;
    BasicType type;
    bool boxed;
    Cell() : holder(NULL), type(T_ILLEGAL), boxed(false) {}
    Cell(oop cell_holder, BasicType cell_type, bool cell_boxed = false)
        : holder(cell_holder), type(cell_type), boxed(cell_boxed) {}
    // Holds a reference whose word is its referent's id: not a wrapper.
    bool reference() const {
      return !boxed && (type == T_OBJECT || type == T_ARRAY);
    }
  };

  /**
   * The decision one read made, without the expression.  A container query
   * reuses it and substitutes its own observed value.
   */
  struct ReadPlan {
    jlong read_event_id;
    Attribution reader;
    // The version live when the read ran (see the class comment).
    Version observed;
    // The word the read loaded equals `observed.stored`, and no unhooked
    // write came between.
    bool observed_exact;
    // The location's writer set, as of this read.
    bool writer_set_complete;
    // A writer the log never named reached the location, as of this read.
    bool unnamed_writer;
    ReadPlan()
        : read_event_id(0), observed_exact(false),
          writer_set_complete(true), unnamed_writer(false) {}
  };

  // ---- sessions ------------------------------------------------------------

  static void open_session();
  static void close_session();

  /** Advisory: false means no location in this session is tracked. */
  static bool has_carriers() { return _carrier_count > 0; }

  /** Whether this location's contents are being kept. */
  static bool is_tracked(const Location &location);

  // ---- the location lock ---------------------------------------------------

  /** Takes / releases the stripe guarding `location`.  Not reentrant. */
  static void lock(const Location &location);
  static void unlock(const Location &location);
  /** The stripe index of a location; for callers holding several. */
  static int stripe_of(const Location &location);
  /** Takes each stripe of `stripes` (sorted, distinct) in order. */
  static void lock_stripes(const std::vector<int> &stripes);
  static void unlock_stripes(const std::vector<int> &stripes);

  // ---- writes --------------------------------------------------------------

  /**
   * Prepares one store outside every lock: nothing is built here, so a
   * store the location turns out not to keep costs nothing more.  `value`
   * NULL is a concrete store; `path_guard` is the writer's guard, already
   * folded; `starts_log` says the store may start the location's log
   * (symbolic, or an admitted guarded store).  The writer's attribution is
   * taken under the lock, and only for a version.
   */
  static void prepare_store(Store *store, const Location &location,
                            Expression *value, Expression *path_guard,
                            bool symbolic, bool starts_log,
                            int version_kind = VERSION_WRITE);

  /**
   * For a store of `referent` into a reference cell at `location`, outside
   * every lock: when the store will be versioned (the location is tracked,
   * or `starts_log`) and the referent is a modeled container (or views or
   * wraps one), its state version live now, starting its log first when it
   * has none.  True when it asked.  Only a store that asked states it; one
   * whose location became tracked after it asked states a refusal.
   */
  static bool referent_state(const Location &location, bool starts_log,
                             oop referent, ReferentState *out);
  /** referent_state for a prepared store. */
  static void prepare_referent(Store *store, oop referent);

  /**
   * Under the location's stripe, before the concrete store: whether the
   * store is versioned at all (tracked, or starting the log), and the value
   * a starting log publishes as its INITIAL, read from `cell`.
   */
  static bool begin_store_locked(Store *store, const Cell &cell);

  /**
   * Under the stripe, after the concrete store: appends the version.  A
   * concrete store's value is the constant of `stored`, else (a reference)
   * the identity of `stored_reference`; a reference cell's word is its
   * referent's id whatever `stored` says.
   */
  static jlong end_store_locked(Store *store, const ConcreteBits &stored,
                                oop stored_reference);

  /**
   * One complete write that is not a bytecode store (a mint, an attach, a
   * container mutation): prepared, locked and appended here.  `symbolic`
   * starts the log.  Returns the version id, or 0 when nothing was kept.
   */
  static jlong publish_value(const Location &location, Expression *value,
                             const ConcreteBits &stored,
                             Expression *path_guard, bool symbolic,
                             int version_kind,
                             const char *operation = NULL);

  /**
   * Starts an untracked location's log with an INITIAL base version whose
   * word is `stored`.  Returns 0 when the location is already tracked.
   */
  static jlong publish_initial(const Location &location, Expression *base,
                               const ConcreteBits &stored,
                               const InitialSnapshot &snapshot);

  /**
   * The same for a value a cell already holds: the word and its constant are
   * read under the stripe, so no store can fall between them and the log's
   * start.  `*base_out` receives the INITIAL's value (NULL when the location
   * was already tracked).
   */
  static jlong publish_initial_held(const Location &location,
                                    const Cell &cell, Expression **base_out);

  /**
   * A version stating the value a cell already holds, read under the stripe
   * (a mint, an attach): `value` is its expression.
   */
  static jlong publish_held(const Location &location, const Cell &cell,
                            Expression *value, Expression *path_guard,
                            int version_kind);

  /**
   * Records that this location has a writer nobody can name, and why.
   * Returns false when the location is not tracked.
   */
  static bool mark_writer_set_incomplete(const Location &location,
                                         const char *reason);
  static bool mark_writer_set_incomplete_locked(const Location &location,
                                                const char *reason);

  // ---- reads ---------------------------------------------------------------

  /** Fills the reader's attribution outside every lock. */
  static void prepare_read(ReadPlan *plan);

  /**
   * Decides and records one read of a tracked location, under its stripe,
   * right after the concrete load.  `loaded` is the word the load took
   * (unstated for a container query), `loaded_reference` the referent a
   * reference load took.  False when the location is not tracked.
   */
  static bool plan_read_locked(const Location &location,
                               const ConcreteBits &loaded,
                               oop loaded_reference, ReadPlan *plan);

  /** prepare_read + lock + plan_read_locked + unlock, for a container. */
  static bool plan_read(const Location &location, const ConcreteBits &loaded,
                        ReadPlan *plan);

  /**
   * The read-from node every reader of a tracked location publishes, around
   * `observed_value` (a scalar's own version value, or a container query
   * applied to the observed state), stating `returned`.
   */
  static Expression *build_read_from(
      const ReadPlan &plan, const Location &location,
      const std::string &type_name, Expression *observed_value,
      const ReturnedValue &returned);

  /**
   * The expression of one scalar read, built after the stripe is released:
   * `loaded` and `reference` are what the load returned.  A read that
   * returned its observed version's word states that version's constant.
   */
  static Expression *scalar_read(const ReadPlan &plan,
                                 const Location &location,
                                 const std::string &type_name,
                                 const ConcreteBits &loaded, oop reference);

  /**
   * What a scalar read or a call returned, as its node states it: the
   * constant of a stated scalar `word`, else null or a String's content
   * (capped at MAX_RETURNED_STRING_BYTES, past which it says only that it
   * was cut) for `reference`, else, for a reference word, the referent's
   * identity (`identity` when the caller has it), else nothing.
   */
  static ReturnedValue returned_value(const ConcreteBits &word,
                                      oop reference,
                                      Expression *identity = NULL);

  /**
   * The newest version's value of a tracked `location` when `cell` (another
   * object's copy of it: an Object.clone) holds what that version wrote,
   * else NULL: the word it stored, or for a reference, which loads no word,
   * the expression `held` the copied shadow gave it.  What a copy of the
   * location is, without recording.
   */
  static Expression *newest_value_if_held(const Location &location,
                                          const Cell &cell,
                                          Expression *held);

  /** The version live at `location` right now, without recording. */
  static jlong live_version(const Location &location,
                            std::string *version_kind);

  /** The tracked element slots of array `owner` in [from, to), ascending. */
  static void tracked_elements(sym_rid_t owner, int from, int to,
                               std::vector<int> *slots);

  // ---- words and constants -------------------------------------------------

  static jlong raw_bits(jboolean value) { return (jlong)(value & 1); }
  static jlong raw_bits(jbyte value)    { return (jlong) value; }
  static jlong raw_bits(jchar value)    { return (jlong) value; }
  static jlong raw_bits(jshort value)   { return (jlong) value; }
  static jlong raw_bits(jint value)     { return (jlong) value; }
  static jlong raw_bits(jlong value)    { return value; }
  static jlong raw_bits(jfloat value)   { return (jlong) jint_cast(value); }
  static jlong raw_bits(jdouble value)  { return jlong_cast(value); }

  static Expression *primitive_expression(BasicType type, jlong bits);
  /** A referent's identity (or its value, for a box or a String). */
  static Expression *reference_expression(oop value);
  /** A referent's identity node alone, never a value it carries. */
  static Expression *identity_expression(oop value);
  /** The value a word stands for: a scalar's constant, else `reference`'s
   *  expression (reference_expression). */
  static Expression *word_value(const ConcreteBits &word, oop reference);
  /** A reference cell's word: `referent`'s id, naming it if it has none, 0
   *  for null; a wrapper-typed (`boxed`) cell's is its box's. */
  static ConcreteBits reference_word(oop referent, bool boxed = false);

  /** The word a primitive field holds right now, as `type`. */
  static ConcreteBits field_bits(oop owner, int field_offset, BasicType type);
  /** The word a primitive array element holds right now. */
  static ConcreteBits element_bits(arrayOop array, int index);
  /** The word a cell holds right now. */
  static ConcreteBits cell_word(const Location &location, const Cell &cell);
  /** What a cell holds right now, as an expression (its word's constant,
   *  else the referent's identity). */
  static Expression *cell_value(const Location &location, const Cell &cell,
                                const ConcreteBits &word);
  /** What a field holds right now, as an expression. */
  static Expression *field_value(oop owner, int field_offset,
                                 BasicType type);

  /**
   * The word a wrapper-typed cell holds: the primitive of a box of
   * Boolean/Byte/Character/Short/Integer/Long, the null word for null, and
   * unstated for any other object.
   */
  static ConcreteBits boxed_word(oop box);
  /** The primitive a wrapper-typed field holds, or T_ILLEGAL. */
  static BasicType wrapper_value_type(Symbol *field_signature);
  /** The same, for the field a getfield/putfield cache entry names. */
  static BasicType wrapper_value_type(ConstantPoolCacheEntry *entry);
  /** Whether the field at `offset` of `holder` (a static field's mirror
   *  included) is wrapper-typed; false for an array. */
  static bool wrapper_field_at(oop holder, jlong offset);

  /**
   * Resolves a field a Java caller named -- an instance field of `owner`,
   * or a static one when `owner` is the declaring class's Class -- into its
   * location (owner left NULL_SYM_RID for the caller), its descriptor and
   * the object holding it (the mirror, for a static).
   */
  static bool resolve_field(oop owner, const char *declaring_class,
                            const char *field_name, const char *descriptor,
                            Location *location, fieldDescriptor *field,
                            oop *holder);

  static const char *location_kind_name(int kind);
  static const char *version_kind_name(int kind);
  /** A version's `versionKind`: its kind, or STATE_<operation>. */
  static std::string version_label(const Version &version);

  // ---- guarded stores ------------------------------------------------------

  /**
   * Installs the guarded-store table and returns how many store sites it
   * names.  One line per store site the scope map lists as control-dependent:
   * `<internal/Class>#<name><descriptor> TAB <store> (TAB <guard site>)*`,
   * where <store> is `FIELD <internal/Owner>.<field>` for a field store and
   * `CALL <method name>` for a container mutation's call, and the guard
   * sites are the woven branch site ids the runtime passes to
   * markConcolicBranch.  Empty admits nothing.
   */
  static int install_guarded_store_sites(const char *table);

  /**
   * Whether a concrete store by the calling thread at the store site
   * (`store_method`, or the innermost frame's method when NULL; `store` as
   * the table spells it) is control-dependent on a symbolic decision one of
   * that site's guards took on this path.  A method's rows are found once
   * per thread per table, with no lock.
   */
  static bool guarded_store_admitted(Method *store_method,
                                     const std::string &store);

  /** The same for a putfield/putstatic, whose store names its field. */
  static bool guarded_field_store_admitted(Method *store_method,
                                           ConstantPoolCacheEntry *entry);

  /** Where the calling thread stands, for one logged event to state. */
  static EventSite current_site();
  /** The calling thread's attribution (empty without a context). */
  static Attribution current_attribution();

  /** The one writer of a logged event's `site` member. */
  static void write_site(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      const EventSite &site);

  // ---- read-outs -----------------------------------------------------------

  /**
   * Every tracked location with an event at or after `after_event_id` (0:
   * all), as SHARED_FIELD_VERSIONS envelopes with one expression table.
   * Locations ascend by their highest event id and `max_bytes` stops the
   * answer at a location boundary: `nextAfterEventId` is one past the last
   * emitted location's highest event, so a resume neither repeats nor skips
   * a location (event ids are unique per location) and never goes back.
   */
  static std::string tracked_locations(jlong after_event_id, jint max_bytes);

  /** One location's versions as evidence, for tests and tracing. */
  static std::string describe(const Location &location);

  /** One resolved read, kept so that a consumer can audit the decision. */
  struct ReadRecord {
    jlong read_event_id;
    Attribution reader;
    ReadRecord() : read_event_id(0) {}
  };

  /** One location's retained history; guarded by its stripe. */
  struct Slot {
    VersionList versions;
    std::vector<ReadRecord> reads;
    bool writer_set_complete;
    bool read_log_complete;
    // Every reason, first first; see the retention note above.
    std::vector<std::string> incomplete_reasons;
    bool unnamed_writer;
    Slot()
        : writer_set_complete(true), read_log_complete(true),
          unnamed_writer(false) {}
  };

  // Bounded on purpose; see the retention note above.
  static const size_t MAX_VERSIONS_PER_LOCATION = 64;
  static const size_t MAX_READS_PER_LOCATION = 1024;
  // A String a read returned is stated up to this many bytes (item 6).
  static const size_t MAX_RETURNED_STRING_BYTES = 4096;
  static const int STRIPES = 64;

private:
  static bool write_versions_envelope(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      const rapidjson::StringBuffer &buffer,
      VmExpressionArtifactScope &expression_artifact,
      const Location &location, const Slot &slot, bool selected,
      size_t budget_bytes);

  typedef std::map<Location, Slot> SlotStore;

  static bool _open;
  static SlotStore _slots;
  static volatile int _carrier_count;
  // Relaxed reader, _mutex writer: the guarded-store table's size, and its
  // install count (thread-local lookups of an older table are discarded).
  static volatile int _guarded_store_count;
  static volatile int _guarded_store_epoch;
  static pthread_mutex_t _mutex;
  static pthread_mutex_t _stripes[STRIPES];

  // Under the stripe: the slot, or NULL (takes _mutex for the lookup).
  static Slot *find_slot(const Location &location);
  // Under the stripe: the slot, created when absent (takes _mutex).
  static Slot *find_or_create_slot(const Location &location);
  // Under the stripe: appends, dropping the oldest version past the bound.
  static jlong append_locked(Slot *slot, Version *version);
  static void incomplete_locked(Slot *slot, const char *reason);
  static void fill_version(Version *version, const Store &store);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_SHAREDFIELDVERSIONS_HPP
