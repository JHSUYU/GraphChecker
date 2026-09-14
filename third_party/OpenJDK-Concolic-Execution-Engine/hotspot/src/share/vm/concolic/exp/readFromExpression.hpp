#ifndef SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"

#include <string>

/**
 * The write an ordinary concurrent read observed.
 *
 * One concrete execution performs one real read, and at the instant it ran the
 * location held exactly one version: the newest one retained for it.  This node
 * names that version and carries its value.
 *
 * It used to name every retained version instead, as an `exactlyOne(rf1..rfk)`
 * choice with a selector, a value and a writer path guard per arm, so that an
 * offline composer could pick an arm.  That vocabulary is gone: the run already
 * determined the answer, the arms the run did not take were never evidence, and
 * publishing them cost one full writer DAG per unobserved version.
 *
 * Whether the recorded writer set was complete is separate coverage metadata
 * (`writerSetComplete`) and is unchanged: it still blocks a closed/final
 * conclusion, and it never alters which version this node names.
 */
class ReadFromExpression : public Expression {
public:
  ReadFromExpression(jlong observed_version_id,
                     const std::string &observed_version_kind,
                     Expression *observed_value,
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
  jlong _observed_version_id;
  std::string _observed_version_kind;
  Expression *_observed_value;
  std::string _java_type;
  std::string _location_kind;
  jlong _read_event_id;
  sym_rid_t _owner;
  int _slot;
  bool _writer_set_complete;
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
