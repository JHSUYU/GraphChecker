#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/pathCondition.hpp"
#include "runtime/arguments.hpp"
#include "utilities/ostream.hpp"
#include "webridge/utils/rapidjson/document.h"

#include <errno.h>
#include <stdlib.h>

/**
 * Resolves the serialization byte bound, once.
 *
 * `-Dcausynth.vm.pathcondition.bytes` accepts a decimal count with an
 * optional k/m/g suffix; anything unparseable, negative or overflowing leaves
 * the default in place rather than silently choosing a bound nobody asked
 * for.  Zero is honoured and means "truncate everything", which is how the
 * smoke forces the marker path at a cost of a few kilobytes.
 *
 * The memo is a benign race: concurrent resolvers compute the same value from
 * an immutable property list and store a word.  A sentinel distinct from every
 * legal bound keeps zero configurable.
 */
static const size_t PATH_CONDITION_BYTES_UNRESOLVED = ~(size_t) 0;
static size_t _path_condition_max_bytes = PATH_CONDITION_BYTES_UNRESOLVED;

size_t PathCondition::max_serialized_range_bytes() {
  size_t resolved = _path_condition_max_bytes;
  if (resolved != PATH_CONDITION_BYTES_UNRESOLVED) {
    return resolved;
  }

  resolved = DEFAULT_MAX_SERIALIZED_RANGE_BYTES;
  const char *configured =
      Arguments::get_property("causynth.vm.pathcondition.bytes");
  if (configured != NULL && *configured != '\0') {
    char *tail = NULL;
    errno = 0;
    unsigned long long value = strtoull(configured, &tail, 10);
    bool ok = errno == 0 && tail != configured;
    if (ok && tail != NULL && *tail != '\0') {
      switch (*tail) {
        case 'k': case 'K': value *= 1024ull;               tail++; break;
        case 'm': case 'M': value *= 1024ull * 1024ull;      tail++; break;
        case 'g': case 'G': value *= 1024ull * 1024ull * 1024ull;
                                                             tail++; break;
        default: ok = false; break;
      }
      if (ok && *tail != '\0') ok = false;
    }
    // Never let a bound of ~0 be configured: serialize_range() computes
    // `max_bytes - emitted_bytes`, and the sentinel would re-resolve forever.
    if (ok && value < (unsigned long long) PATH_CONDITION_BYTES_UNRESOLVED) {
      resolved = (size_t) value;
    } else {
      tty->print_cr("[causynth] ignoring causynth.vm.pathcondition.bytes=%s"
                    " (unparseable); keeping " SIZE_FORMAT " bytes",
                    configured, resolved);
    }
  }

  _path_condition_max_bytes = resolved;
  return resolved;
}

int __attribute__((optimize("O0"))) PathCondition::add(Expression *exp) {
  // getPathCondition() may be queried repeatedly by Java branch hooks while
  // the region is still running.  The old implementation cached the first
  // serialized prefix forever, so every later query (and the final summary)
  // silently omitted newly recorded conditions.
  if (_pc_str != NULL) {
    delete[] _pc_str;
    _pc_str = NULL;
  }
  const std::string &code_pos = ConcolicMngr::ctx->get_current_code_pos();
//  guarantee(code_pos.find("valueOf") == std::string::npos, "we should permit cache when use valueOf");
  // Condition kept the location only for debug printing.  Copy it onto the
  // expression as well so the JSON path condition can be joined with stable
  // bytecode/Jimple branch sites by an external scheduler.
  exp->set_java_code_position(code_pos);
  Condition *cond = new Condition(code_pos, exp);
  _conds.push_back(cond);
  return (int) _conds.size() - 1;
}

Expression *PathCondition::conjunction() {
  const int size = (int) _conds.size();
  if (size == 0) return NULL;
  if (_conjunction != NULL && _conjunction_size == size) return _conjunction;

  // Extend the memoized prefix rather than refolding it.  The nodes are
  // session-owned, so keeping a pointer to the previous fold across calls is
  // safe for the life of the session.
  Expression *folded = _conjunction_size <= size ? _conjunction : NULL;
  int start = _conjunction_size <= size ? _conjunction_size : 0;
  for (int index = start; index < size; ++index) {
    Expression *condition = _conds[index]->getExp();
    if (condition == NULL) continue;
    folded = folded == NULL
        ? condition
        : (Expression *) new OpSymExpression(folded, condition, op_land);
  }
  _conjunction = folded;
  _conjunction_size = size;
  return folded;
}

void PathCondition::gc() {
  int size = _conds.size();
  for (int i = 0; i < size; ++i) {
    delete _conds[i];
  }
  _conds.clear();
  if (_pc_str != NULL) {
    delete[] _pc_str;
    _pc_str = NULL;
  }
  _conjunction = NULL;
  _conjunction_size = 0;
}

#endif
