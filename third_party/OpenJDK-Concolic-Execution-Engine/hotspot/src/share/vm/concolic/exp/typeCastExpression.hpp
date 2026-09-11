//
// Created by gansen on 6/28/22.
//

#ifndef JDK8_CDB_TYPECASTEXPRESSION_HPP
#define JDK8_CDB_TYPECASTEXPRESSION_HPP

#include "concolic/exp/expression.hpp"
#include "concolic/SymbolicOp.hpp"
#include "concolic/defs.hpp"
#include "oops/oop.inline.hpp"
#include "utilities/debug.hpp"
#include "utilities/ostream.hpp"
#include "symbolExpression.hpp"

#include <map>
#include <stdio.h>
#include <vector>

class TypeCastExpression : public SymbolExpression {
private:
  Expression *_exp_to_cast;
  std::string _source_type;
  std::string _target_type;
public:
  TypeCastExpression(Expression *exp, const char *source_type,
                     const char *target_type)
      : _exp_to_cast(exp),
        _source_type(source_type == NULL ? "" : source_type),
        _target_type(target_type == NULL ? "" : target_type) {
    // SymbolExpression::_type is the result descriptor serialized for every
    // symbolic expression. Keep it in sync with the explicit cast target.
    set_type(_target_type);
  }

  ~TypeCastExpression() {}

  virtual void serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer);

  virtual std::string get_name();
};

#endif //JDK8_CDB_TYPECASTEXPRESSION_HPP
