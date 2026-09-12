#ifdef ENABLE_CONCOLIC

#include "concolic/exp/fieldAccessExpression.hpp"
#include "utilities/ostream.hpp"

FieldAccessExpression::FieldAccessExpression(
    Expression *owner, const char *owner_class, int field_offset,
    BasicType type, const std::string &java_type)
    : _owner(owner),
      _owner_class(owner_class == NULL ? "" : owner_class),
      _field_offset(field_offset),
      _java_type(java_type.empty()
                     ? std::string(1, type2char(type))
                     : java_type) {
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
}

#endif  // ENABLE_CONCOLIC
