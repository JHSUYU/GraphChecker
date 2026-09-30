#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicArray.hpp"
#include "utilities/ostream.hpp"

SymArr::SymArr(sym_rid_t sym_rid, Expression *length_exp)
    : SymRef(sym_rid), _version(0), _length_exp(length_exp), _ref_exp(NULL),
      _semantic_expression(false), _named(false) {}

SymArr::~SymArr() {}

#endif
