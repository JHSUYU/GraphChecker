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

 public:
  ContainerExpression(const char *shape, const char *operation,
                      Expression *receiver, const exp_list_t &arguments,
                      BasicType result_type = T_OBJECT,
                      const std::string &java_type = std::string());
  virtual ~ContainerExpression();

  // STATE names a container; every other operation is one the recorder
  // watched happen to it.
  virtual bool is_recorded_container_mutation() {
    return _operation != "STATE";
  }

  virtual void print();
  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
