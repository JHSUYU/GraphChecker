//
// Created by gansen on 5/20/22.
//
#ifdef ENABLE_CONCOLIC

#include "symbolicUnsafe.hpp"

bool SymbolicUnsafe::invoke_method_helper(MethodSymbolizerHandle &handle) {
//  tty->print_cr("Inside unsafe %s", handle.get_callee_name().c_str());
  return true;
}

Expression *SymbolicUnsafe::finish_method_helper(MethodSymbolizerHandle &handle) {
  return NULL;
}

void SymbolicUnsafe::init_register_class(MethodSymbolizer *m_symbolizer) {
  const char *const classes[] = {
    "sun/misc/Unsafe", "sun/instrument/TransformerManager", NULL
  };
  m_symbolizer->register_model(classes, invoke_method_helper,
                               finish_method_helper);
}
#endif