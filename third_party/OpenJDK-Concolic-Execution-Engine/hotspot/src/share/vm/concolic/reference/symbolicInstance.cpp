#ifdef ENABLE_CONCOLIC

#include "classfile/vmSymbols.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "symbolicBigDecimal.hpp"
#include "symbolicString.hpp"

Expression *SymInstance::get_exp_of(oop obj) {
  Expression *exp = NULL;
  Symbol *klass_symbol = obj->klass()->name();
  if (klass_symbol->equals(SymBigDecimal::TYPE_NAME)) {
    exp = SymBigDecimal::get_exp_of(obj);
  } else if (klass_symbol == vmSymbols::java_lang_String()) {
    // A String this session deliberately left unshadowed -- an interned one
    // cannot carry a symbolic id in its shared oop header -- still has the
    // value this execution recorded, and naming that value costs nothing:
    // SymString answers a plain constant when there is no shadow to ask, so
    // no shadow is allocated, no header is written and no identity is
    // minted.  The untracked placeholder named neither the object nor its
    // content, so every comparison against it reached the formula as a root
    // no symbolization event had declared, and was refused.
    exp = SymString::get_exp_of(obj);
  } else {
    exp = new PlaceHolderSymbolExp(obj);
  }
  return exp;
}

#endif // ENABLE_CONCOLIC
