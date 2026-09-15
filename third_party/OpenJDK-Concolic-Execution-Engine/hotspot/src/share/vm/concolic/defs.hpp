#ifndef SHARE_VM_CONCOLIC_DEFS_HPP
#define SHARE_VM_CONCOLIC_DEFS_HPP

#ifdef ENABLE_CONCOLIC

#include "jni.h"

#include <set>
#include <string>
#include <sys/types.h>

// Symbolioc Reference ID related
#define NULL_SYM_RID 0
// A symbolic reference id occupies a full sym_rid_t word of every oop header
// (oops/oop.hpp), so the representation imposes no bound worth enforcing.  The
// only real limit is that the session's minting counter must not wrap onto an
// id that is already live, which next_sym_rid() checks directly; there is no
// separate small cap.
typedef ulong sym_rid_t;

// The id word's top bit says the object has been *named* and nothing more.
//
// A recording states the identity of what a reference read returned, and an
// object it had to name that way needs a session identity to be named by.
// Naming is not a claim that anything about the object is symbolic: a named
// object has an id, no shadow, and `is_symbolic() == false`, so every gate
// that asks whether to run symbolic machinery -- which loads become container
// reads, which values propagate, which path conditions exist -- keeps
// answering exactly what it answered before the object was named.
//
// The id itself is the remaining bits and is never rewritten, so an object
// that is named first and becomes symbolic later keeps one id, and therefore
// one identity spelling, for the whole session; the shadow allocators reuse
// it and clear this bit.  It lives in the header rather than in a side map
// because the lookup has to be one load on a bytecode path and has to survive
// a GC that moves the object.
#define SYM_RID_NAMED_ONLY (((sym_rid_t) 1) << (8 * sizeof(sym_rid_t) - 1))

#define FIELD_INDEX_ARRAY_LENGTH -1

typedef std::set<std::string> method_set_t;

#endif
#endif // SHARE_VM_CONCOLIC_DEFS_HPP