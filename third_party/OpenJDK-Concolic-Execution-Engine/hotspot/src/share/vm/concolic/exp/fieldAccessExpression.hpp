#ifndef SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <string>

/** A field read whose owner is another symbolic expression. */
class FieldAccessExpression : public Expression {
 private:
  Expression *_owner;
  std::string _owner_class;
  int _field_offset;
  std::string _java_type;

 public:
  FieldAccessExpression(Expression *owner, const char *owner_class,
                        int field_offset, BasicType type,
                        const std::string &java_type = std::string());
  virtual ~FieldAccessExpression();

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_FIELDACCESSEXPRESSION_HPP
