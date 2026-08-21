//
// Created by gansen on 6/7/22.
//

#ifndef JDK8_CDB_PLACEHOLDEREXPRESSION_HPP
#define JDK8_CDB_PLACEHOLDEREXPRESSION_HPP
#include "concolic/exp/expression.hpp"

class PlaceholderExpression : public Expression {
public:
  enum Function {
    currentTimeMills,
    uuidToString,
    number_of_placeholder_functions
  };

  PlaceholderExpression(Function type);

protected:
  virtual void serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer);

public:
  virtual void print();

  virtual std::string get_name();

private:
  // One occurrence counter per placeholder function.  It used to be a
  // std::map mutated without synchronization from whichever thread happened
  // to build the node; several attached threads can reach the same
  // non-deterministic call, so the ordinal is now minted atomically.
  static volatile intptr_t occurrence_counters[number_of_placeholder_functions];
  Function _type;
  int _count;
};

#endif //JDK8_CDB_PLACEHOLDEREXPRESSION_HPP
