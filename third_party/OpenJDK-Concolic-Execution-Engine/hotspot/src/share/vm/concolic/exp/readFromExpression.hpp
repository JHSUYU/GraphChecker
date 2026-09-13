#ifndef SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"

#include <string>
#include <vector>

/**
 * The value an ordinary concurrent read observed, when the run does not prove
 * which write produced it.
 *
 * One concrete execution performs one real read, and the engine sees the value
 * it returned.  It does not see which store that value came from, and when
 * several tracked writers stored the same value there is nothing in the
 * observation that separates them.  Choosing one anyway -- by concrete value,
 * by event id, by thread -- would manufacture a read-from edge the run never
 * showed.  This node keeps the recorded candidates as an explicit choice:
 *
 *     exactlyOne(rf1, ..., rfk)
 *     value = ite(rf1, E1, ite(rf2, E2, ... Ek))
 *
 * The choice contains recorded writers only.  Whether that set is complete is
 * separate coverage metadata (`writerSetComplete`).  An incomplete set blocks
 * a closed/final conclusion; it never becomes a fresh value the solver may use.
 * If no recorded candidate remains, no ReadFromExpression is created.
 *
 * Each candidate also carries the writer's local identity and path guard.  The
 * solver couples the arm selector to that writer case and its path condition.
 * Runtime ordering never chooses an arm: every retained bounded writer remains
 * available, including when there is only one.
 */
class ReadFromExpression : public Expression {
public:
  struct Candidate {
    std::string selector;
    jlong field_version_id;
    std::string version_kind;
    Expression *value;
    // NULL denotes the empty conjunction, i.e. an unguarded write.
    Expression *path_guard;
    Candidate() : field_version_id(0), value(NULL), path_guard(NULL) {}
  };

  ReadFromExpression(const std::vector<Candidate> &candidates,
                     const std::string &java_type, jlong read_event_id,
                     sym_rid_t owner, int slot, const char *location_kind,
                     bool writer_set_complete);

  virtual bool is_boolean_expression();
  virtual bool is_guarded_reference_read();
  virtual std::string get_name();

protected:
  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);

private:
  std::vector<Candidate> _candidates;
  std::string _java_type;
  std::string _location_kind;
  jlong _read_event_id;
  sym_rid_t _owner;
  int _slot;
  bool _writer_set_complete;

  void serialize_candidate(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      const Candidate &candidate);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
