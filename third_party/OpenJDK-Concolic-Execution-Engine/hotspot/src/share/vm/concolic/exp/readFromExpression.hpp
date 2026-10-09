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
 * (`writerSetComplete`), and `unnamedWriter` says a writer the log never
 * named reached the location, which removes the read's alternative writers;
 * neither alters which version this node names.  Whether this one read is
 * verified is its own member (`observedExact`): the word it loaded equals the
 * word its observed version stored and no unhooked write came between.  An
 * exact read joins its version even at an incomplete location; a reference or
 * container read states no word and is never exact.
 */
class ReadFromExpression : public Expression {
public:
  ReadFromExpression(jlong observed_version_id,
                     const std::string &observed_version_kind,
                     Expression *observed_value,
                     const std::string &java_type, jlong read_event_id,
                     sym_rid_t owner, int slot, const char *location_kind,
                     bool writer_set_complete, bool unnamed_writer,
                     bool observed_exact,
                     const ReturnedValue &returned,
                     const std::string &site_class = std::string(),
                     const std::string &site_method = std::string(),
                     const std::string &site_descriptor = std::string(),
                     int site_bci = -1);

  virtual bool is_boolean_expression();
  virtual bool is_guarded_reference_read();
  // Only a container query's read is the view it returned; a read of a
  // reference cell is a choice among the objects its writers stored, and a
  // call through it keeps the read itself as its owner, whatever it holds.
  virtual bool derived_container_value(Expression **owner) {
    return _location_kind == "MAP_STATE"
        && _observed_value->derived_container_value(owner);
  }
  // A reference cell whose observed writer stored a constant Enum.valueOf
  // named: the read is of the names its writers stored.
  virtual const char *enum_constant_class() {
    return _observed_value->enum_constant_class();
  }
  virtual std::string get_name();

protected:
  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);

private:
  // The bytecode site this read stood at, in the JVM's own components, or
  // empty when the read named none.  Written by
  // SharedFieldVersions::write_site so the node and the read log cannot
  // disagree about what a site is; held as components here only to keep this
  // header independent of that one.
  std::string _site_class;
  std::string _site_method;
  std::string _site_descriptor;
  int _site_bci;
  jlong _observed_version_id;
  std::string _observed_version_kind;
  Expression *_observed_value;
  std::string _java_type;
  std::string _location_kind;
  jlong _read_event_id;
  sym_rid_t _owner;
  int _slot;
  bool _writer_set_complete;
  bool _unnamed_writer;
  bool _observed_exact;
  // What the read returned.  A read joins to the expression of the write it
  // observed, and pins to this when it cannot: the write does not lower, or
  // the writer set is incomplete (an UNOBSERVED version).  SOLR-18406's read
  // of a String field of ReplicationHandler$DirectoryFileStream
  // (initWrite#288), whose observed write did not lower, stated nothing to
  // pin to, and the composition refused all four paths to the anchor.
  ReturnedValue _returned;
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
