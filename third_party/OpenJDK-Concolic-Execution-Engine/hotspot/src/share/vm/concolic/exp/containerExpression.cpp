#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "utilities/ostream.hpp"

ContainerExpression::ContainerExpression(
    const char *shape, const char *operation, Expression *receiver,
    const exp_list_t &arguments, BasicType result_type,
    const std::string &java_type, Expression *guard)
    : _shape(shape == NULL ? "" : shape),
      _operation(operation == NULL ? "" : operation),
      _receiver(receiver),
      _arguments(arguments),
      _java_type(java_type.empty()
                     ? std::string(1, type2char(result_type))
                     : java_type),
      _guard(guard) {
}

ContainerExpression::~ContainerExpression() {}

ContainerExpression *ContainerExpression::rebuilt_on(
    Expression *receiver) const {
  // _java_type is never empty -- the constructor derives one from the result
  // type when it is -- so passing it back reproduces this node's own type
  // whatever the T_OBJECT placeholder says.
  return new ContainerExpression(_shape.c_str(), _operation.c_str(), receiver,
                                 _arguments, T_OBJECT, _java_type, _guard);
}

void ContainerExpression::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ContainerRelation");
  writer.Key("shape");
  writer.String(_shape.c_str());
  writer.Key("operation");
  writer.String(_operation.c_str());
  writer.Key("_java_type");
  writer.String(_java_type.c_str());
  writer.Key("receiver");
  if (_receiver == NULL) {
    writer.Null();
  } else {
    _receiver->serialize(writer);
  }
  writer.Key("arguments");
  writer.StartArray();
  for (size_t index = 0; index < _arguments.size(); ++index) {
    if (_arguments[index] == NULL) {
      writer.Null();
    } else {
      _arguments[index]->serialize(writer);
    }
  }
  writer.EndArray();
  // Only a conditional mutation carries a guard.  Omitting the key entirely
  // for an unconditional one keeps every existing op's JSON byte-identical.
  if (_guard != NULL) {
    writer.Key("guard");
    _guard->serialize(writer);
  }
}

#endif  // ENABLE_CONCOLIC
