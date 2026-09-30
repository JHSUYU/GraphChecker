#ifdef ENABLE_CONCOLIC

#include "concolic/exp/consumerBoundaryExpression.hpp"
#include "utilities/debug.hpp"
#include "utilities/ostream.hpp"

ConsumerBoundaryExpression::ConsumerBoundaryExpression(
    Expression *expression, const std::string &java_type,
    BoundaryKind boundary_kind, jlong event_id)
    : _expression(expression),
      _java_type(java_type),
      _boundary_kind(boundary_kind),
      _event_id(event_id) {
  guarantee(_expression != NULL, "a consumer boundary needs its payload");
  guarantee(_event_id > 0, "a consumer boundary needs its boundary id");
  guarantee(_boundary_kind == RPC_ATTACH
                || _boundary_kind == FIELD_READ,
            "unknown consumer boundary kind");
}

ConsumerBoundaryExpression::~ConsumerBoundaryExpression() {}

bool ConsumerBoundaryExpression::is_boolean_expression() {
  return _expression->is_boolean_expression();
}

bool ConsumerBoundaryExpression::is_guarded_reference_read() {
  // The boundary is the identity function, so it answers for its child.
  return _expression->is_guarded_reference_read();
}

ContainerExpression *ConsumerBoundaryExpression::as_container_expression() {
  // Container users inspect the child's structural shape but keep this wrapper
  // as the state expression they pass into the next operation.  The anchor is
  // therefore preserved in the receiver chain rather than becoming a bogus
  // container operation of its own.
  return _expression->as_container_expression();
}

bool ConsumerBoundaryExpression::is_or_wraps_consumer_value(
    Expression *value) {
  return this == value || _expression->is_or_wraps_consumer_value(value);
}

Expression *ConsumerBoundaryExpression::logical_negation() {
  Expression *negated = _expression->logical_negation();
  return negated == NULL ? NULL : new ConsumerBoundaryExpression(
      negated, _java_type, _boundary_kind, _event_id);
}

std::string ConsumerBoundaryExpression::get_name() {
  // get_name() renders expression values polymorphically. An identity marker
  // must not alter the wrapped value.
  return _expression->get_name();
}

void ConsumerBoundaryExpression::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ConsumerBoundaryExpression");
  writer.Key("boundaryKind");
  writer.String(_boundary_kind == RPC_ATTACH
                    ? "RPC_ATTACH" : "FIELD_READ");
  writer.Key("eventId");
  writer.Int64(_event_id);
  writer.Key("_java_type");
  writer.String(_java_type.c_str());
  writer.Key("expression");
  _expression->serialize(writer);
}

#endif  // ENABLE_CONCOLIC
