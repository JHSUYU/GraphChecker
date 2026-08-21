#ifndef SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "oops/oop.inline.hpp"
#include <string>

class MethodSymbolizerHandle;

namespace ContainerSupport {
const char *shape(oop value);
bool indexed(oop value);
bool associative(oop value);
BasicType result_type(oop result, BasicType declared);
std::string java_type(oop result, BasicType declared);
Expression *concrete_value(oop value);
Expression *concrete_result(MethodSymbolizerHandle &handle);
void constrain_result(MethodSymbolizerHandle &handle,
                      Expression *expression);
void constrain_position(const char *shape, Expression *state,
                        Expression *position, bool allow_end = false);
void attach_result(oop result, Expression *expression, oop owner = NULL);
// True for a call whose body the engine can follow instead of summarizing.
// A constructor's receiver is freshly allocated, so no tracked container
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

// Where this container's whole state lives, or an invalid location when it
// has no shadow.  A view answers its owner's location: one logical container
// is one location.  Allocates nothing.
SharedFieldVersions::Location state_location(oop container);

// Publishes `new_state` as the immutable state this mutation produced.
// `operation` names the mutation (PUT, REMOVE, CLEAR, ...) and is what the
// ledger event and the evidence report call this write.  Returns the new
// version id, or 0 when the container is not a selected carrier.
//
// The caller must already have installed `new_state` as the container's
// current state: a version is published for a mutation that happened, and the
// pairing is one-to-one.
jlong publish_state(oop container, Expression *new_state,
                    const char *operation);

// Records that a mutation this engine does not model has run on a selected
// container, so every later read of it keeps an honest rf_unknown arm.
// `reason` names the gap in the ledger.  Returns true when a selected
// location was marked, i.e. when there was a claim to keep honest.
bool mark_state_gap(oop container, const char *reason);

/** One query bound to the state it may have observed. */
struct StateQuery {
  // NULL when the container is not a selected carrier, in which case the
  // caller keeps whatever answer it already had.
  Expression *expression;
  // True when one writer was proven, so the observation may still be tied to
  // the concrete value the run returned.  False for a guarded choice: tying an
  // undecided disjunction to one concrete value would let concrete equality
  // pick the writer, which is the guess this whole mechanism exists to avoid.
  bool exact;
  StateQuery() : expression(NULL), exact(false) {}
};

/**
 * Resolves one query of a selected container against its state versions.
 *
 * The decision -- program order, happens-before, retention, and the
 * Resolution/ReadReason vocabulary -- is the generic store's, unchanged.  What
 * is built here is only the value: the arm of candidate W is
 * `operation(W.state, arguments)`, never W's state itself, because selecting a
 * writer has to change what the reader observes and not merely which state is
 * named.  A guarded answer keeps the unconditional rf_unknown arm, typed with
 * the query's own result type.
 */
StateQuery query_state(oop container, const char *shape,
                       const char *operation, const exp_list_t &arguments,
                       BasicType result_type, const std::string &java_type);
}

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
