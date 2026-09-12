#ifndef SHARE_VM_CONCOLIC_EXP_CONSUMERBOUNDARYEXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_CONSUMERBOUNDARYEXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <string>

/**
 * A consumer-side provenance marker around a value the VM already propagated.
 *
 * The node is semantically the identity function.  It neither mints a symbol
 * nor reconnects two values: its child is the exact expression installed at
 * an RPC attach or selected by a shared read.  Keeping the marker in the
 * expression DAG lets later receiver arithmetic retain the precise boundary
 * where that child entered. The application trace records RPC provenance;
 * GuardedRead payloads record their complete bounded writer candidates.
 */
class ConsumerBoundaryExpression : public Expression {
 public:
  enum BoundaryKind {
    RPC_ATTACH = 0,
    FIELD_READ = 1
  };

  ConsumerBoundaryExpression(Expression *expression,
                             const std::string &java_type,
                             BoundaryKind boundary_kind, jlong event_id);
  virtual ~ConsumerBoundaryExpression();

  Expression *get_expression() const { return _expression; }
  BoundaryKind get_boundary_kind() const { return _boundary_kind; }
  jlong get_event_id() const { return _event_id; }

  virtual bool is_boolean_expression();
  virtual bool is_recorded_container_mutation();
  virtual ContainerExpression *as_container_expression();
  virtual bool is_or_wraps_consumer_value(Expression *value);
  virtual Expression *logical_negation();
  virtual std::string get_name();

 protected:
  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);

 private:
  Expression *_expression;
  std::string _java_type;
  BoundaryKind _boundary_kind;
  jlong _event_id;
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_CONSUMERBOUNDARYEXPRESSION_HPP
