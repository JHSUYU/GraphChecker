#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "utilities/ostream.hpp"

ContainerExpression::ContainerExpression(
    const char *shape, const char *operation, Expression *receiver,
    const exp_list_t &arguments, BasicType result_type,
    const std::string &java_type)
    : _shape(shape == NULL ? "" : shape),
      _operation(operation == NULL ? "" : operation),
      _receiver(receiver),
      _arguments(arguments),
      _java_type(java_type.empty()
                     ? std::string(1, type2char(result_type))
                     : java_type) {
  if (_receiver != NULL) _receiver->inc_ref();
  for (size_t index = 0; index < _arguments.size(); ++index) {
    if (_arguments[index] != NULL) _arguments[index]->inc_ref();
  }
}

ContainerExpression::~ContainerExpression() {
  Expression::gc(_receiver);
  for (size_t index = 0; index < _arguments.size(); ++index) {
    Expression::gc(_arguments[index]);
  }
}

void ContainerExpression::print() {
  tty->print("(container %s %s ", _shape.c_str(), _operation.c_str());
  Expression::print_on_maybe_null(_receiver);
  for (size_t index = 0; index < _arguments.size(); ++index) {
    tty->print(" ");
    Expression::print_on_maybe_null(_arguments[index]);
  }
  tty->print(")");
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
}

#endif  // ENABLE_CONCOLIC
