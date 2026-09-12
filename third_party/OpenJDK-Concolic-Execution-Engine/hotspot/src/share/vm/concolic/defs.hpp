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

typedef ulong tx_id_t;

#define FIELD_INDEX_ARRAY_LENGTH -1

typedef std::set<std::string> method_set_t;

#endif
#endif // SHARE_VM_CONCOLIC_DEFS_HPP