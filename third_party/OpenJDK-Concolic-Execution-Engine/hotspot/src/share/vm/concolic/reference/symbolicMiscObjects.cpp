#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/utils.hpp"

#include "symbolicMiscObjects.h"

void SymbolicMiscObjects::init_register_class(MethodSymbolizer *m_symbolizer) {
  // FIXME: concolic executing into some methods inside these classes triggers
  // JVM crash. Investigate them later.
  const char *const classes[] = {
    "com/fasterxml/jackson/core/json/UTF8JsonGenerator",
    "com/fasterxml/jackson/databind/ser/BeanPropertyWriter",
    NULL
  };
  m_symbolizer->register_model(classes, invoke_method_helper,
                               finish_method_helper);
}

bool SymbolicMiscObjects::invoke_method_helper(MethodSymbolizerHandle &handle) {
    return true;
}

Expression *
SymbolicMiscObjects::finish_method_helper(MethodSymbolizerHandle &handle) {
  return NULL;
}

#endif
