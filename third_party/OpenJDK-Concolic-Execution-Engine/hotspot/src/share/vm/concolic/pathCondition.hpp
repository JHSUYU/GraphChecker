#ifndef SHARE_VM_CONCOLIC_PATHCONDITION_HPP
#define SHARE_VM_CONCOLIC_PATHCONDITION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <vector>

class PathCondition {
  /**
   * Byte bound on one serialize_range() answer.
   *
   * This is a bound on the *evidence document*, not on the path condition:
   * every recorded index is always reported, and an index whose expression
   * would push the document past the bound is reported as an explicit
   * TruncatedExpression marker rather than dropped.  See serialize_range().
   *
   * The default accommodates large region paths. It is overridable with
   * `-Dcausynth.vm.pathcondition.bytes=<n>[k|m|g]`, which is how a test forces
   * the truncation path without producing hundreds of megabytes.
   */
  static const size_t DEFAULT_MAX_SERIALIZED_RANGE_BYTES =
      256u * 1024u * 1024u;

  // Resolved once from the system property, then memoized.  Defined out of
  // line so this header need not pull in the runtime argument machinery.
  static size_t max_serialized_range_bytes();

  struct Condition {
    std::string _code_pos;
    Expression *_exp;
    char *_cache;

    Condition(std::string code_pos, Expression *exp)
        : _code_pos(code_pos), _exp(exp), _cache(NULL) {}

    // A recorded condition names a session-owned expression; it owns only its
    // serialization cache.
    ~Condition() {
      delete[] _cache;
    }

    Expression *getExp() const {
      return _exp;
    }
  };

private:
  std::vector<Condition *> _conds;
  char *_pc_str;
  // Memoized fold of the first _conjunction_size conditions.  The vector only
  // ever grows between gc()s, so a prefix fold stays valid and a longer
  // condition list extends it instead of rebuilding it.
  Expression *_conjunction;
  int _conjunction_size;

public:
  PathCondition()
      : _pc_str(NULL), _conjunction(NULL), _conjunction_size(0) {}

  const std::vector<Condition *> &getConds() const {
    return _conds;
  }

  // Appends one condition and returns its stable, zero-based index in this
  // thread context.  Exact branch-event accounting uses the returned index;
  // callers that only contribute auxiliary constraints may ignore it.
  int add(Expression *exp);

  inline int size() const { return (int) _conds.size(); }

  /**
   * The conjunction of everything recorded so far, or NULL for the empty
   * conjunction -- which denotes `true`, and is reported as such rather than
   * fabricated as a constant node.
   *
   * This is the guard a shared write is published under: it says on which
   * branch of the writing thread the write happened, which is what a reader
   * needs in order to select that writer conditionally rather than
   * unconditionally.  It is folded here, outside every engine lock, because no
   * Expression may be constructed inside one.
   */
  Expression *conjunction();

  // A range fold used to live here for get_path_condition_range().  It is
  // gone with the `conjunction` member it served: the fold of a window is the
  // left fold of the window's own conditions in index order, so serializing it
  // beside them restated every one of them a second time and allocated one
  // op_land node per condition to do it.  Only the whole-prefix guard above is
  // real evidence -- it is what a shared write is published under, and it is
  // memoized.
  void gc();

private:
  /**
   * The stand-in emitted at an index whose expression is not in the document.
   *
   * It occupies exactly one array slot, so it keeps the positional
   * correspondence between `conditions` and `pathConditionIndices`, and it
   * names both which index it stands for and why, so a truncated answer is
   * distinguishable from a short one.
   */
  static void write_truncation_marker(
      rapidjson::Writer<rapidjson::StringBuffer> &writer, const char *kind,
      int index, const Condition *cond) {
    writer.StartObject();
    writer.Key("_type");
    writer.String("TruncatedExpression");
    writer.Key("_index");
    writer.Int(index);
    if (cond != NULL && !cond->_code_pos.empty()) {
      writer.Key("_code_position");
      writer.String(cond->_code_pos.c_str());
    }
    writer.Key("expressionAuthority");
    writer.String("VM_SERIALIZATION_TRUNCATION_V1");
    writer.Key("truncationKind");
    writer.String(kind);
    writer.EndObject();
  }

public:
  /**
   * Serializes the half-open index range [start, end) as a JSON array, and
   * returns the number of array entries written.
   *
   * Uses the same per-condition serialization cache as the whole-sequence
   * form, so asking for a range costs nothing beyond the conditions it names
   * and allocates no new expression node.
   *
   * **One entry per index, always.**  The array is positional: entry i of the
   * result is the condition at index `start + i`, so a reader may join it
   * against a parallel index vector (`pathConditionIndices`) without
   * re-deriving anything.  Two cases used to break that correspondence and
   * made the emitted array shorter than the declared count, which downstream
   * can only read as a cardinality fault:
   *
   *   1. hitting the byte bound `break`-ed out of the loop, dropping every
   *      remaining index silently after a single marker;
   *   2. a condition with a NULL expression was `continue`-d past, emitting
   *      nothing at all for that index.
   *
   * Both now emit a named TruncatedExpression in place of the expression, so
   * the entry count equals the index count unconditionally and the reason a
   * particular index is missing its expression is visible at that index.
   * Truncation is sticky: once the bound is hit no further expression is
   * serialized (that is the point of the bound), but the remaining indices are
   * still named.
   */
  int serialize_range(rapidjson::Writer<rapidjson::StringBuffer> &writer,
                      int start, int end) const {
    const int limit = (int) _conds.size();
    if (start < 0) start = 0;
    if (end > limit) end = limit;
    const size_t max_bytes = max_serialized_range_bytes();
    size_t emitted_bytes = 0;
    bool truncated = false;
    int emitted = 0;
    writer.StartArray();
    for (int index = start; index < end; index++) {
      Condition *cond = _conds[index];
      emitted++;
      if (truncated) {
        write_truncation_marker(writer, "PATH_CONDITION_RANGE_BYTE_LIMIT",
                                index, cond);
        continue;
      }
      VmExpressionArtifactScope *artifact =
          VmExpressionArtifactScope::active();
      if (artifact != NULL) {
        Expression *expr = cond->_exp;
        if (expr == NULL) {
          write_truncation_marker(writer, "NULL_EXPRESSION", index, cond);
          continue;
        }
        // An artifact condition is a fixed-size session/id reference.  Apply
        // the existing range bound to that reference before recording the
        // root, so a rejected condition neither leaves a dangling reference
        // nor pulls an unreachable DAG into vmExpressionTable.  Definitions
        // shared by admitted roots are emitted once at the envelope end.
        const size_t condition_bytes = artifact->reference_size(expr);
        if (condition_bytes > max_bytes - emitted_bytes) {
          truncated = true;
          write_truncation_marker(writer,
                                  "PATH_CONDITION_RANGE_BYTE_LIMIT",
                                  index, cond);
          continue;
        }
        expr->serialize(writer);
        emitted_bytes += condition_bytes;
        continue;
      }
      if (cond->_cache == NULL) {
        Expression *expr = cond->_exp;
        if (expr == NULL) {
          // Not a bound problem -- this index never had an expression.  Say
          // so by name instead of leaving a hole the reader must guess at.
          write_truncation_marker(writer, "NULL_EXPRESSION", index, cond);
          continue;
        }

        using namespace rapidjson;
        StringBuffer s;
        Writer<StringBuffer> cache_writer(s);
        expr->serialize(cache_writer);
        cond->_cache = new char[s.GetLength() + 1];
        strcpy(cond->_cache, s.GetString());
      }
      const size_t condition_bytes = strlen(cond->_cache);
      if (condition_bytes > max_bytes - emitted_bytes) {
        truncated = true;
        write_truncation_marker(writer, "PATH_CONDITION_RANGE_BYTE_LIMIT",
                                index, cond);
        continue;
      }
      writer.RawValue(cond->_cache, condition_bytes,
                      rapidjson::kObjectType);
      emitted_bytes += condition_bytes;
    }
    writer.EndArray();
    return emitted;
  }

  // Returns the number of array entries written, which equals size().
  int serialize(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
    return serialize_range(writer, 0, (int) _conds.size());
  }

  const char *toString() {
    if (_pc_str != NULL) {
      return _pc_str;
    }

    using namespace rapidjson;
    StringBuffer s;
    Writer<StringBuffer> writer(s);
    serialize(writer);
    const char *res = s.GetString();
    guarantee(_pc_str == NULL, "should be null");
    _pc_str = new char[s.GetLength() + 1];
    strcpy(_pc_str, res);
    return _pc_str;
  }
};

#endif

#endif // SHARE_VM_CONCOLIC_PATHCONDITION_HPP
