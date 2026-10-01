#ifndef SHARE_VM_CONCOLIC_LEAFBROKER_HPP
#define SHARE_VM_CONCOLIC_LEAFBROKER_HPP

#ifdef ENABLE_CONCOLIC

#include "runtime/handles.hpp"

#include <string>

/**
 * The two natives a serialization boundary uses (System.exportLeaf and
 * System.mintLeaf): a leaf is one value inside a message graph, addressed by
 * the slot that holds it.
 *
 *   - exportLeaf peeks at a leaf's expression for the encoding side.  It
 *     answers the slot's shadow first (a field shadow; an array element, a
 *     map entry or a list position as the container's recorded state decides
 *     it), then the leaf object's own shadow (a String's or a box's), then a
 *     typed constant.  It records no path condition, no read and no container
 *     event.
 *   - mintLeaf states a decoded leaf as a template over fresh boundary
 *     symbols ("holes"): one symbol for a primitive or a box, and for a String
 *     `concat` of literals, `toString` of a decimal or boolean hole symbol,
 *     and String hole symbols.  The expression lands on the slot for a field
 *     or an array element, and on the leaf object for a value, a map entry or
 *     a list position.  A mint never puts an expression on a JVM-shared
 *     object (jvm_shared_object: an interned String, a JDK box-cache entry or
 *     cache array, Boolean.TRUE/FALSE), as the landing object or the slot's
 *     holder (SHARED), and never replaces one: a landing object or a field or
 *     element slot that already carries an expression is SHADOWED.  For a
 *     leaf landing on its object the caller can store a fresh equal object
 *     through the holder and mint again; a slot's refusal stands.
 *
 * Both run on any thread of the open session: one inside a region, or one
 * outside every region while a workload session holds the session
 * (ConcolicMngr::may_use_session_heap).  Neither needs a ThreadContext: they
 * read and write the session heap and the version store directly.  A mint on
 * a thread with a context opens its path-condition gate, as every mint does.
 *
 * Both answer one JSON document; a refusal is a named status, never a guess.
 */
class LeafBroker {
public:
  /** The slotKind argument; System.java documents the same numbers. */
  enum SlotKind {
    SLOT_FIELD = 0,     // slot: a java.lang.reflect.Field of the parent
    SLOT_ELEMENT = 1,   // parent: an array; slot: an Integer index
    SLOT_ENTRY = 2,     // parent: a modeled Map; slot: the key
    SLOT_POSITION = 3,  // parent: an ArrayList or ArrayDeque; slot: Integer
    SLOT_VALUE = 4      // parent: the leaf itself; slot: null
  };

  static std::string export_leaf(Handle parent, jint slot_kind, Handle slot);
  /** `template_json` is the Java String of the template (System.java). */
  static std::string mint_leaf(Handle parent, jint slot_kind, Handle slot,
                               Handle template_json);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_LEAFBROKER_HPP
