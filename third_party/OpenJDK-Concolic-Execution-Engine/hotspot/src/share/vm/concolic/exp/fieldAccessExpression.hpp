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
 * The pair binds one arm of the owner's read-from choice to a value the run
 * observed, so the arms the run did not take stay free while the one it did
 * take is pinned to evidence instead of to whatever the solver prefers.
 * Both are optional and NULL when the read had no such owner choice.</p>
 */
class FieldAccessExpression : public Expression {
 private:
  Expression *_owner;
  std::string _owner_class;
  int _field_offset;
  std::string _java_type;
  Expression *_concrete_owner;
  Expression *_concrete_value;

 public:
  FieldAccessExpression(Expression *owner, const char *owner_class,
                        int field_offset, BasicType type,
                        const std::string &java_type = std::string(),
                        Expression *concrete_owner = NULL,
                        Expression *concrete_value = NULL);
  virtual ~FieldAccessExpression();

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP
