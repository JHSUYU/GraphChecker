#ifndef SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "oops/oop.inline.hpp"
#include <string>

class MethodSymbolizerHandle;

namespace ContainerSupport {
BasicType result_type(oop result, BasicType declared);
std::string java_type(oop result, BasicType declared);
Expression *concrete_value(oop value);
Expression *concrete_result(MethodSymbolizerHandle &handle);
void constrain_result(MethodSymbolizerHandle &handle,
                      Expression *expression);
void constrain_position(const char *shape, Expression *state,
                        Expression *position, bool allow_end = false);
void attach_result(oop result, Expression *expression);
}

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_REFERENCE_CONTAINERSUPPORT_HPP
