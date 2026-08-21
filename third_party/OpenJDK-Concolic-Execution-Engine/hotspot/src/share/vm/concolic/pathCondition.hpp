#ifndef SHARE_VM_CONCOLIC_PATHCONDITION_HPP
#define SHARE_VM_CONCOLIC_PATHCONDITION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <vector>

class PathCondition {
  static const size_t MAX_SERIALIZED_RANGE_BYTES = 32u * 1024u * 1024u;
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

  void print();

  /**
   * Serializes the half-open index range [start, end) as a JSON array.
   *
   * Uses the same per-condition serialization cache as the whole-sequence
   * form, so asking for a range costs nothing beyond the conditions it names
   * and allocates no new expression node.
   */
  void serialize_range(rapidjson::Writer<rapidjson::StringBuffer> &writer,
                       int start, int end) const {
    const int limit = (int) _conds.size();
    if (start < 0) start = 0;
    if (end > limit) end = limit;
    size_t emitted_bytes = 0;
    writer.StartArray();
    for (int index = start; index < end; index++) {
      if (emitted_bytes >= MAX_SERIALIZED_RANGE_BYTES) {
        writer.StartObject();
        writer.Key("_type");
        writer.String("TruncatedExpression");
        writer.Key("expressionAuthority");
        writer.String("VM_SERIALIZATION_TRUNCATION_V1");
        writer.Key("truncationKind");
        writer.String("PATH_CONDITION_RANGE_BYTE_LIMIT");
        writer.EndObject();
        break;
      }
      Condition *cond = _conds[index];
      if (cond->_cache == NULL) {
        Expression *expr = cond->_exp;
        if (expr == NULL) {
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
      if (condition_bytes > MAX_SERIALIZED_RANGE_BYTES - emitted_bytes) {
        writer.StartObject();
        writer.Key("_type");
        writer.String("TruncatedExpression");
        writer.Key("expressionAuthority");
        writer.String("VM_SERIALIZATION_TRUNCATION_V1");
        writer.Key("truncationKind");
        writer.String("PATH_CONDITION_RANGE_BYTE_LIMIT");
        writer.EndObject();
        break;
      }
      writer.RawValue(cond->_cache, condition_bytes,
                      rapidjson::kObjectType);
      emitted_bytes += condition_bytes;
    }
    writer.EndArray();
  }

  void serialize(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
    serialize_range(writer, 0, (int) _conds.size());
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
