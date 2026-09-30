//
// Created by gansen on 5/20/22.
//
#ifdef ENABLE_CONCOLIC

#include "symbolicUnsafe.hpp"

#include "concolic/unsafeAccess.hpp"

// The whole class is muted: its bodies and natives run concretely.  A write
// it performs is versioned where it happens, in the native
// (UnsafeAccess), and what the written value is a function of is taken here,
// at the call boundary, where the caller's operand shadows still are.
bool SymbolicUnsafe::invoke_method_helper(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_holder_name() == "sun/misc/Unsafe") {
    UnsafeAccess::capture(handle);
  }
  return true;
}

Expression *SymbolicUnsafe::finish_method_helper(MethodSymbolizerHandle &handle) {
  UnsafeAccess::release_capture();
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
