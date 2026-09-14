#ifndef SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <string>

/**
 * A field read whose owner is another symbolic expression.
 *
 * <p>The owner is ordinarily a symbol for the receiver object, and the node
 * denotes "that object's field", which the composer lowers as an
 * uninterpreted projection.  A read through a reference-typed shared carrier
 * adds two more facts that the projection alone would throw away:
 *
 *   - `concrete_owner` is the object this execution actually read from, and
 *   - `concrete_value` is what its field held at that read.
 *
 * The pair binds the projection to a value the run observed, so the read is
 * pinned to evidence instead of to whatever the solver prefers.  Both are
 * optional and NULL when the read had no such owner.
 *
 * <p>When the field is a tracked shared carrier the node also names the
 * version of that carrier it is a view of (`observedVersion`), so a reader
 * that has to say which write a projection saw does not have to infer it from
 * event ordering.  `observed_version_id` is 0 for a field that is not
 * tracked.</p>
 */
class FieldAccessExpression : public Expression {
 private:
  Expression *_owner;
  std::string _owner_class;
  int _field_offset;
  std::string _java_type;
  Expression *_concrete_owner;
  Expression *_concrete_value;
  jlong _observed_version_id;
  std::string _observed_version_kind;

 public:
  FieldAccessExpression(Expression *owner, const char *owner_class,
                        int field_offset, BasicType type,
                        const std::string &java_type = std::string(),
                        Expression *concrete_owner = NULL,
                        Expression *concrete_value = NULL,
                        jlong observed_version_id = 0,
                        const std::string &observed_version_kind
                            = std::string());
  virtual ~FieldAccessExpression();

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP
