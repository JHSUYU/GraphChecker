//
// Created by gansen on 6/7/22.
//

#include "symbolicNDFunc.hpp"
#include "concolic/exp/placeholderExpression.hpp"

SymbolicNDFunc::SymbolicNDFunc(sym_rid_t sym_rid) : SymInstance(sym_rid) {

}

SymbolicNDFunc::~SymbolicNDFunc() {
}

bool SymbolicNDFunc::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  ResourceMark rm;

  if (callee_name == vmSymbols::currentTimeMillis_name()->as_C_string()) {
    return true;
  }
  return false;
}

Expression *SymbolicNDFunc::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  ResourceMark rm;
  if (callee_name == vmSymbols::currentTimeMillis_name()->as_C_string()) {
    return new PlaceholderExpression(
        PlaceholderExpression::currentTimeMills);
  }
  return NULL;
}

void SymbolicNDFunc::init_register_class(MethodSymbolizer *m_symbolizer) {
  ResourceMark rm;
  m_symbolizer->add_invoke_helper_methods(vmSymbols::java_lang_System()->as_C_string(), invoke_method_helper);
  m_symbolizer->add_finish_helper_methods(vmSymbols::java_lang_System()->as_C_string(), finish_method_helper);
}

void SymbolicNDFunc::print() {
  ShouldNotCallThis();
}
