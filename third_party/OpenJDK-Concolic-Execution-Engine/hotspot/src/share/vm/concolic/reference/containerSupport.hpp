#ifndef SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "oops/oop.inline.hpp"
#include <string>
#include <vector>

class ContainerExpression;
class MethodSymbolizerHandle;
class SymArr;

namespace ContainerSupport {
/**
 * What this engine models of one container object, decided by the
 * receiver's concrete class (never by the method holder: an application
 * subclass of HashMap reaches HashMap.put and may override
 * removeEldestEntry).  Semantics come from the interface the call belongs
 * to; the capability says the class honors it and how its heap is walked.
 */
enum Capability {
  CAPABILITY_NONE = 0,
  // Arrays, AbstractList subclasses, ArrayDeque: positional.
  CAPABILITY_INDEXED,
  // HashMap, LinkedHashMap in insertion order.
  CAPABILITY_HASH_MAP,
  // ConcurrentHashMap and Hashtable: null-free (present <=> READ != null).
  CAPABILITY_CONCURRENT_MAP,
  CAPABILITY_HASHTABLE,
  // HashSet, LinkedHashSet: a set with its own state.
  CAPABILITY_HASH_SET
};
Capability capability(oop value);
// The shape a capability's state has: "INDEXED", "ASSOCIATIVE", or NULL.
const char *shape(oop value);
// The order Java's iterator of this container's class walks its members
// in, as a snapshot states it: "INSERTION" (LinkedHashMap, LinkedHashSet:
// the order keys were first put) or "HASH" (HashMap, HashSet,
// ConcurrentHashMap, Hashtable: the table decides it, and an insertion may
// rebin or resize it); NULL for a positional container.
const char *iteration_order(oop value);
// Why a map- or set-like receiver is not modeled, or empty when it is one
// or is nothing of the kind: CONTAINER_SUBCLASS_UNMODELED:<class> for a
// subclass of a modeled class, ACCESS_ORDER_UNMODELED for a LinkedHashMap
// whose get reorders it.
std::string unmodeled_reason(oop value);
// The modeled container `value` is, or views, iterates or wraps -- through
// the backing fields of the JDK's views (`this$0`, `map`), iterators and
// Collections wrappers (`m`, `c`, `s`) -- or NULL.
oop backing_container(oop value);
// Whether `value`'s class is a modeled container, view, iterator or
// wrapper, by class name alone: no field is read and no lock taken, so it
// may be asked under a stripe.
bool names_container(oop value);
// Resolves a view or wrapper built by bytecode to its backing container, so
// its state is that container's: one logical container, one location.
// Returns the backing container (or `value` itself).
oop canonicalize(oop value);

BasicType result_type(oop result, BasicType declared);
std::string java_type(oop result, BasicType declared);
Expression *concrete_value(oop value);
// Returns the semantic expression already carried by this object, without
// allocating an identity shadow or replacing a missing expression with a
// concrete value.  Container iterators use this to preserve a key's upstream
// lineage while keeping the no-lineage fallback explicit and bounded.
Expression *semantic_value(oop value);
Expression *concrete_result(MethodSymbolizerHandle &handle);
void constrain_result(MethodSymbolizerHandle &handle,
                      Expression *expression);
void constrain_position(const char *shape, Expression *state,
                        Expression *position, bool allow_end = false);
// What a load at a concrete position of an array returns when the recording
// already decides it, with no READ: true with `*stored` the value the newest
// recorded write at that position stored, or with `*stored` NULL when no
// recorded write replaced the element, which is then the heap's own and
// concrete.  False -- the load stays a READ -- for a symbolic `position`
// (NULL is the concrete `index`), below a write at a symbolic position, and
// for an array whose elements are an input: one a symbolization reached, or
// whose shadow stands for a semantic value.  hdfs-17960's FSImageSaver
// scanned the NameNode's 2^21-bucket inode map, which an earlier region had
// stored into under symbolic guards, and built a READ, its index and an
// `== null` condition for every untouched bucket, a million nodes a second,
// until the replay JVM passed 24 GB.  A recorded write that stored a
// concrete value, or whose word the element no longer holds (a write no hook
// saw; the container's log is then marked incomplete), answers concrete too.
bool recorded_element(arrayOop heap_array, SymArr *array, Expression *state,
                      Expression *position, jint index, Expression **stored);
void attach_result(oop result, Expression *expression, oop owner = NULL);
// True for a call whose body the engine can follow instead of summarizing:
// a constructor, or a method that only reads its container (its result is
// concrete).  A constructor's receiver is freshly allocated, so no tracked container
// state exists that letting the body run could make stale; and the body's
// own container operations are already modeled, so a copy constructor over a
// tracked container is rebuilt exactly by the hooks that are already there.
// Aborting one instead discards the whole thread's path condition for an
// operation the engine can already follow, and it punishes a tracked
// destination class more harshly than an untracked one, which is silently
// tolerated on the same line today.
bool follows_callee_body(const std::string &callee_name);
// True when this invocation carries a receiver expression, or the engine
// holds semantic/container state for the receiver (its own, or an owner's
// if it is a view).  Merely allocating an identity shadow is not a claim.  An
// unmodeled operation only has something to contradict when such a claim
// exists, and only then must it fail closed.  On a receiver the engine
// claims nothing about, the body's concrete answer is the only answer there
// is, and a symbolic argument reaching an *internal* helper is not evidence
// to the contrary: every public operation of these classes is checked over
// its whole parameter list first, so a helper is reachable only after that
// check already declined.  Charging the helper for an operand the public
// entry point had already cleared abandons the region for nothing.
bool claims_state(MethodSymbolizerHandle &handle);
// True when `length` is exactly the element count of `state`, so an array
// declared with it holds a collection of that state and nothing else.  This
// is the `new T[c.size()]` destination `Collection.toArray(T[])` fills
// without leaving a trailing slot, and the indexed vocabulary has no way to
// say "these elements, but that many slots" for the destinations that do.
bool measures(Expression *length, Expression *state);
// Why `measures` said no, as a name a report can be read for.  A gap whose
// cause cannot be told from its name costs a whole pipeline run to diagnose.
std::string measurement(Expression *length, Expression *state);
// Names the exact container operation a modeling gap was hit on.  A bare
// category tells a reader that some unmodeled operation aborted the region
// but not which one, and the abort silently truncates everything after it,
// so the category alone is indistinguishable from a dozen other causes.
std::string unsupported(const char *category,
                        MethodSymbolizerHandle &handle);

// ---- selected whole-container state ---------------------------------------
//
// A resizable container has no stable per-member slot, so its members are not
// separately addressable.  Its *state* is: the container algebra already makes
// every mutation produce one immutable state expression, and that is what a
// selected container publishes a version of.  Everything below is the bridge
// between that algebra and the generic version store, and it lives here rather
// than in the store because the store must not learn what PUT means.
//
// Each of these is a no-op on a container nobody selected, and the first thing
// each of them does is the store's own one-counter early-out, so an unselected
// workload keeps exactly its old cost.

// Members a recorded initial snapshot states, or -1 when `state` is not one.
//
// A snapshot is a SNAPSHOT_BASE base with one PUT/APPEND per member, which
// is the same node shape every later state version uses, so counting the
// chain down to its base is exactly counting what the snapshot said.
//
// Zero is a real answer and -1 is not.  A container that held nothing states
// a bare SNAPSHOT_BASE, which is the exact empty collection and the most
// constrained initial state there is; reporting that as the same 0 an opaque
// root reports would publish no snapshot block for it and leave the one
// carrier nobody has to reconstruct marked unknown.
int snapshot_entry_count(Expression *state);

/**
 * Reads a container's concrete members straight from the heap.
 *
 * Retention is by value, so when a symbolic operand first reaches a container
 * the engine must state what it already held and has nobody to ask.  This
 * walks the backing storage of the classes the models admit -- HashMap and
 * LinkedHashMap (and HashSet/LinkedHashSet through the map they wrap),
 * ArrayList, ArrayDeque, and object arrays.
 *
 * `keys` is filled only for an associative container; every shape fills
 * `values`.  Returns false when the class is not one this engine walks, and
 * then sets `*unsupported_class` to its name so the refusal can be published
 * by name rather than mistaken for an empty container.
 */
bool read_concrete_members(oop container, std::vector<oop> *keys,
                           std::vector<oop> *values,
                           const char **unsupported_class,
                           bool *over_bound);

/**
 * Installs a SNAPSHOT_BASE chain stating what `container` holds right now,
 * and reports how many members it stated.
 *
 * Same node shape the Java-driven offer used to install, so nothing
 * downstream changes: a bare SNAPSHOT_BASE for an empty container, one
 * PUT/APPEND per member on top of it.  Returns -1 and sets
 * `*unsupported_class` when the class cannot be walked, and -2 when the
 * member count is over the engine's snapshot bound -- both of which are
 * published as a stated refusal rather than as an empty container.
 */
int install_receiver_snapshot(oop container, const char *shape,
                              bool *truncated,
                              const char **unsupported_class);

/**
 * Fills `out` with what `container` holds, for the INITIAL version that
 * starts its log.
 *
 * `receiver_is_base` says whether the container is still in the state the
 * log should begin from -- true on a first symbolic read, false on a first
 * symbolic write, where the concrete mutation has already run and a walk
 * would overstate the base by the entry being written.  When it cannot be
 * stated exactly the refusal is recorded by name; the snapshot is never
 * guessed.
 */
void snapshot_for_receiver(oop container,
                           SharedFieldVersions::InitialSnapshot *out,
                           bool receiver_is_base);

/**
 * Starts `container`'s log with the contents it holds right now, from a
 * model's invoke hook or a reference store of it.
 *
 * The callee body has not run yet (the store has not happened), so the
 * receiver is still the base -- which is what makes a write-first container
 * statable at all.  A no-op once the container is tracked, and for a
 * container with no modelled shape.  Returns its location, and in
 * `*snapshot` what a log started here stated.
 */
SharedFieldVersions::Location state_base_before_operation(
    oop container, SharedFieldVersions::InitialSnapshot *snapshot = NULL);

/**
 * What a reference store of `referent` states about the container it is,
 * views or wraps: that container's location and the version live now,
 * starting its log with a stated snapshot when it has none; or why not
 * (`UNREADABLE_CONTAINER:<class>`, `TRUNCATED`, `RESIZING`, `NO_CONTEXT`).
 * Nothing for a referent that is no modeled container.  Called before the
 * carrier's stripe is taken.
 */
void referent_state(oop referent, SharedFieldVersions::ReferentState *out);

// Whether `state` stands on a base this recorder stated, however many
// recorded mutations sit on top of it.  A chain that bottoms out in the bare
// STATE root does not, and is the state whose contents are unknown.
bool states_initial_content(Expression *state);

// The mutations the recorder watched, oldest first, and the opaque STATE root
// they stand on.  False when `state` is not a chain of container relations
// bottoming out in a STATE root -- which includes a chain that already stands
// on a stated base, and a chain rooted in another container's state.
bool recorded_history(Expression *state, Expression **root,
                      std::vector<ContainerExpression *> *history);

// Undoes an indexed `history` against the `member_count` members the
// container holds now, answering which of them -- by index, in order -- the
// container already held at the history's root.
//
// Only a record that carries its own inverse is undone.  APPEND put one
// member at the end, so dropping the last member undoes it; INSERT at a
// recorded concrete position put one member there, so dropping that position
// undoes it.  WRITE, REMOVE and CLEAR each destroyed a member this record
// does not carry, so they have no inverse and the answer is false: the base
// is unknown and must be reported unknown rather than guessed.
bool undo_indexed_history(const std::vector<ContainerExpression *> &history,
                          int member_count,
                          std::vector<int> *base_members);

// Where this container's whole state lives, or an invalid location when it
// has no shadow.  A view or wrapper answers its backing container's
// location: one logical container is one location.  Allocates nothing, and
// needs no thread context (a store outside every region asks it too).
SharedFieldVersions::Location state_location(oop container);

// Publishes `new_state` as the immutable state this mutation produced.
// `operation` names the mutation (PUT, REMOVE, CLEAR, ...) in evidence. Returns the new
// version id, or 0 when the container is not a selected carrier.
//
// The caller must already have installed `new_state` as the container's
// current state: a version is published for a mutation that happened, and the
// pairing is one-to-one.
/**
 * Whether one modelled call is a container mutation this thread is taking
 * BECAUSE of a symbolic decision.
 *
 * A container becomes a symbolic state variable at its first symbolic-or-
 * guarded write.  Until now only a symbolic *value* admitted the model, so a
 * concrete mutation of a concrete container was invisible even when the
 * program only performed it on one arm of a symbolic branch -- HDFS-11741's
 * removeExpiredKeys(), whose removals are concrete and whose decision
 * (`expiryDate < now`) is a declared CLOCK root.  What the container holds
 * afterwards is a function of that predicate, so the mutation is evidence and
 * the log starts here.
 *
 * Only a mutation: a read under a guard tells a reader nothing it did not
 * already have, and the rule is about writes.  The names are the mutators the
 * three container models publish state for -- put/remove/clear (associative),
 * add/offer/set/remove/clear (indexed), add/remove/clear (set).
 */
bool guarded_mutation(const std::string &callee);

jlong publish_state(oop container, Expression *new_state,
                    const char *operation);

// Records that a mutation this engine does not model has run on a selected
// container.  Later queries keep the recorded candidates available for
// exploration but cannot close coverage.  `reason` names the gap in the
// evidence report. Returns true when a selected location was marked.
bool mark_state_gap(oop container, const char *reason);
// An attach replaced `destination`'s whole state with `attached`: published
// as its STATE_ATTACH version, and for an array as a version of each tracked
// element (D7).
void publish_attached_state(oop destination, Expression *attached);
// An operation the model cannot follow reached a container: its writer set is
// marked incomplete (mark_state_gap) and its modeled state is dropped, so it
// runs concretely until a modeled operation roots it again.  The thread's
// symbolic execution goes on: only this container left the model.  Aborting
// the thread instead lost every other value it carried (SOLR-18413: the
// update whose expiry clock decides the rule, at replicas.removeIf).
void abandon_state(oop container, const std::string &reason);

/** One query bound to the state it may have observed. */
struct StateQuery {
  // NULL when the container is not selected or when the selected location
  // has no recorded writer candidate.
  Expression *expression;
  // True once this query addressed a selected location, including the gap
  // case where no recorded candidate can provide an expression.
  bool selected;
  StateQuery() : expression(NULL), selected(false) {}
};

/**
 * Resolves one query of a selected container against its state versions.
 *
 * The arm of candidate W is
 * `operation(W.state, arguments)`, never W's state itself, because selecting a
 * writer has to change what the reader observes and not merely which state is
 * named.  A guarded answer contains only recorded writer states; incomplete
 * coverage is reported separately and never lowered as a free state.
 */
StateQuery query_state(oop container, const char *shape,
                       const char *operation, const exp_list_t &arguments,
                       BasicType result_type, const std::string &java_type,
                       Expression *owner = NULL);

/**
 * The owner a call's container relation carries (ContainerExpression's
 * `owner`): the receiver slot's own shadow when it is a guarded reference
 * read -- a tracked reference field, an AtomicReference, a container READ
 * result -- so the choice that read made survives; the owner of the view,
 * iterator or entry the receiver is, which it inherits; else NULL.
 */
Expression *receiver_owner(Expression *receiver);

/**
 * `container`'s state as a read of it: a read of its location's observed
 * version when it is tracked, else its chain when it has one, else NULL.
 * A source a mutation copies from (putAll).
 */
Expression *observed_state(oop container);
}

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
