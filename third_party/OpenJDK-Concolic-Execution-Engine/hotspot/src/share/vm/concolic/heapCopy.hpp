#ifndef SHARE_VM_CONCOLIC_HEAPCOPY_HPP
#define SHARE_VM_CONCOLIC_HEAPCOPY_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/sharedFieldVersions.hpp"

#include <vector>

/**
 * The two ways the JVM copies values without a bytecode: System.arraycopy
 * (and Arrays.copyOf, which calls it) and Object.clone.
 *
 * Propagation here is by JVM-level shadows -- a slot's, a field's, an
 * array's container state -- so a copy the interpreter does not execute must
 * copy the shadows itself, or the destination keeps a stale one and the
 * relation is silently wrong.  arraycopy used to leave every destination
 * element's shadow and version as they were: CharArrayBuffer's growth copied
 * characters a region had written symbolically, and 1,136 of the 1,139
 * UNOBSERVED reads of one Solr session were that copy (unobs/s3).  clone
 * used to copy the identity word with the object, so the clone shared the
 * original's shadow, container state and version log (jvm.cpp, JVM_Clone).
 */
class HeapCopy {
public:
  /**
   * One arraycopy, bracketing the concrete copy: the source values are
   * taken before it (the ranges may overlap), the destination's tracked
   * elements are locked across it, and its shadows and versions are written
   * after it.
   */
  struct ArrayCopy {
    bool active;
    arrayOop destination;
    int destination_position;
    int length;
    // Per element of the range: what it copies (NULL: the concrete word),
    // and the word it leaves.
    std::vector<Expression *> values;
    std::vector<SharedFieldVersions::ConcreteBits> words;
    std::vector<jlong> identities;
    // The destination's tracked elements, and the stripes they take.
    std::vector<int> tracked;
    std::vector<int> stripes;
    bool shadowed;
    bool modeled;
    Expression *path_guard;
    ArrayCopy()
        : active(false), destination(NULL), destination_position(0),
          length(0), shadowed(false), modeled(false), path_guard(NULL) {}
  };

  /** Past this many elements a shadowed destination is not modeled. */
  static const int ARRAYCOPY_MODEL_LIMIT = 16384;

  static void before_array_copy(ArrayCopy *copy, arrayOop source,
                                int source_position, arrayOop destination,
                                int destination_position, int length);
  static void after_array_copy(ArrayCopy *copy, bool failed);

  /**
   * An Object.clone: the copy has already been given no identity of its
   * own (the copied header word is cleared where the copy is made); it gets
   * a shadow holding the original's field shadows or container state.
   */
  static void cloned(oop original, oop clone);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_HEAPCOPY_HPP
