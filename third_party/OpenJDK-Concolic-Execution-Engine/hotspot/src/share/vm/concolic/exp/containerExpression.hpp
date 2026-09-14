#ifndef SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <string>

/**
 * One operation in an activation-local shadow container.
 *
 * The VM records Java semantics, not SMT syntax.  Nested expressions form the
 * state transformer consumed by GraphChecker's single ContainerSmtCodec.
 */
class ContainerExpression : public Expression {
 private:
  std::string _shape;
  std::string _operation;
  Expression *_receiver;
  exp_list_t _arguments;
  std::string _java_type;
  // The control-flow predicate a conditionally-recorded mutation fired under,
  // or NULL for an unconditional one.  Today only ASSOCIATIVE/REMOVE_IF carries
  // it: the removeExpiredKeys `if (expiry < now)` branch, recorded so that an
  // external solver may flip the removal (the flippable-removal story).  The
  // guard is oriented as the *removal condition* (true => the key is gone),
  // independent of which way the concrete run branched.
  Expression *_guard;

 public:
  ContainerExpression(const char *shape, const char *operation,
                      Expression *receiver, const exp_list_t &arguments,
                      BasicType result_type = T_OBJECT,
                      const std::string &java_type = std::string(),
                      Expression *guard = NULL);
  virtual ~ContainerExpression();

  // STATE names a container; every other operation is one the recorder
  // watched happen to it.
  virtual bool is_recorded_container_mutation() {
    return _operation != "STATE";
  }

  virtual ContainerExpression *as_container_expression() { return this; }

  const std::string &get_operation() const { return _operation; }
  const std::string &get_shape() const { return _shape; }
  Expression *get_receiver() const { return _receiver; }

  virtual ContainerExpression *as_container_relation() { return this; }
  Expression *get_guard() const { return _guard; }
  const exp_list_t &get_arguments() const { return _arguments; }

  // This same relation, applied to a different receiver.
  //
  // An expression node is immutable once constructed (see expression.hpp), so
  // re-rooting a recorded mutation history onto a stated base rebuilds the
  // chain rather than editing it.  Everything but the receiver is copied,
  // including the guard: a conditionally recorded removal is still
  // conditional when it stands on a different base.
  ContainerExpression *rebuilt_on(Expression *receiver) const;

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
