#ifndef SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
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
}

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
