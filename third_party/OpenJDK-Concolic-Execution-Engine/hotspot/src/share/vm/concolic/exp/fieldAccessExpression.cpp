#ifdef ENABLE_CONCOLIC

#include "concolic/exp/fieldAccessExpression.hpp"
#include "utilities/ostream.hpp"

FieldAccessExpression::FieldAccessExpression(
    Expression *owner, const char *owner_class, int field_offset,
    BasicType type, const std::string &java_type,
    Expression *concrete_owner, Expression *concrete_value)
    : _owner(owner),
      _owner_class(owner_class == NULL ? "" : owner_class),
      _field_offset(field_offset),
      _java_type(java_type.empty()
                     ? std::string(1, type2char(type))
                     : java_type),
      _concrete_owner(concrete_owner),
      _concrete_value(concrete_value) {
}

FieldAccessExpression::~FieldAccessExpression() {}

void FieldAccessExpression::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("FieldAccessExpression");
  writer.Key("_java_type");
  writer.String(_java_type.c_str());
  writer.Key("ownerClass");
  writer.String(_owner_class.c_str());
  writer.Key("fieldOffset");
  writer.Int(_field_offset);
  writer.Key("owner");
  if (_owner == NULL) {
    writer.Null();
  } else {
    _owner->serialize(writer);
  }
  // Emitted only when the read was through a reference-typed carrier: an
  // absent member is a projection with no observed binding, which is a
  // weaker statement than a binding to nothing.
  if (_concrete_owner != NULL && _concrete_value != NULL) {
    writer.Key("concreteOwner");
    _concrete_owner->serialize(writer);
    writer.Key("concreteValue");
    _concrete_value->serialize(writer);
  }
}

#endif  // ENABLE_CONCOLIC
