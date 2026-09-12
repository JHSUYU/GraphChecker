#ifdef ENABLE_CONCOLIC

#include "concolic/exp/stringExpression.hpp"
#include "utilities/ostream.hpp"
#include <concolic/utils.hpp>

OpStrExpression::OpStrExpression(const std::string &method,
                                 exp_list_t &param_list)
    : _name(method), _is_not(false), _is_boolean(false) {
  // all exp must be not null

  _param_list.swap(param_list);
}

OpStrExpression::OpStrExpression(const std::string &method,
                                 exp_list_t &param_list, bool is_not)
    : _name(method), _is_not(is_not), _is_boolean(true) {
  // all exp must be not null

  _param_list.swap(param_list);
}

OpStrExpression::OpStrExpression(const std::string &method, Expression *exp)
    : _name(method), _is_not(false), _is_boolean(false) {
  _param_list.push_back(exp);
}

OpStrExpression *OpStrExpression::to_string(Expression *exp) {
  return new OpStrExpression("toString", exp);
}

void OpStrExpression::serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("OpStrExpression");
  writer.Key("_name");
  writer.String(_name.c_str());
  writer.Key("_is_not");
  writer.Bool(_is_not);

  writer.Key("_param_list");
  writer.StartArray();
  for (size_t index = 0; index < _param_list.size(); ++index) {
    Expression *expr = _param_list[index];
    if (expr) {
      expr->serialize(writer);
    } else {
      writer.Null();
    }
  }
  writer.EndArray();
}

const exp_list_t &OpStrExpression::get_param_list() const {
  return _param_list;
}

std::string OpStrExpression::get_name() {
  std::string name;
  name += _name;
  name += "(";
  for (size_t index = 0; index < _param_list.size(); ++index) {
    Expression *expr = _param_list[index];
    if (expr) {
      name += expr->get_name();
    } else {
      name += "null";
    }
    if (index != _param_list.size() - 1) {
      name += ",";
    }
  }
  name += ")";
  return name;
}

StringSymbolExp::StringSymbolExp(sym_rid_t sym_rid) {
  ResourceMark rm;
  char buf[BUF_SIZE];
  stringStream ss(buf, BUF_SIZE);
  set_head(ss, 'M', T_OBJECT, "'String'");
  ss.print("%lu", sym_rid);
  _type = vmSymbols::java_lang_String()->as_C_string();
  this->finalize(buf, ss.size());
}

StringSymbolExp::StringSymbolExp(sym_rid_t sym_rid, std::string name) {
  ResourceMark rm;
  char buf[BUF_SIZE];
  stringStream ss(buf, BUF_SIZE);
  set_head(ss, 'M', T_OBJECT, "'String'");
  ss.print("%s", name.c_str());
  _type = vmSymbols::java_lang_String()->as_C_string();
  this->finalize(buf, ss.size());
}

ConStringSymbolExp::ConStringSymbolExp(oop obj) {
  ResourceMark rm;
  char buf[BUF_SIZE];
  stringStream ss(buf, BUF_SIZE);
  set_head(ss, 'Y', T_OBJECT, "'String'");
  _type = vmSymbols::java_lang_String()->as_C_string();
  ss.print("%s", OopUtils::java_string_to_c(obj));
  this->finalize(buf, ss.size());
}

ConStringSymbolExp::ConStringSymbolExp(const std::string &str) {
  ResourceMark rm;
  char buf[BUF_SIZE];
  stringStream ss(buf, BUF_SIZE);
  set_head(ss, 'Y', T_OBJECT, "'String'");
  _type = vmSymbols::java_lang_String()->as_C_string();
  ss.print("%s", str.c_str());
  this->finalize(buf, ss.size());
}

void ConStringSymbolExp::serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ConStringSymbolExp");
  writer.Key("_java_type");
  writer.String(_type.c_str());
  writer.Key("_exp");
  writer.String(_str.c_str());
}

#endif
