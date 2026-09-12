#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicBigDecimal.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/utils.hpp"



#include "concolic/reference/symbolicString.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "webridge/utils/rapidjson/document.h"

#include <map>

std::string SymBigDecimal::DECIMAL_WRAPPER = "$BIG_DECIMAL$";
const char *SymBigDecimal::TYPE_NAME = "java/math/BigDecimal";


std::set<std::string> SymBigDecimal::handle_method_names = init_handle_method_names();

std::set<std::string> SymBigDecimal::init_handle_method_names() {
  std::set<std::string> set;
  set.insert("java.math.BigDecimal.<init>(D)V");
  set.insert("java.math.BigDecimal.<init>(I)V");
  set.insert("java.math.BigDecimal.<init>(J)V");
  set.insert("java.math.BigDecimal.<init>(Ljava/lang/String;)V");
  set.insert("java.math.BigDecimal.<init>(Ljava/math/BigInteger;JII)V");
  set.insert("java.math.BigDecimal.setScale(II)Ljava/math/BigDecimal;");
  set.insert("java.math.BigDecimal.valueOf(J)Ljava/math/BigDecimal;");
  set.insert("java.math.BigDecimal.valueOf(JII)Ljava/math/BigDecimal;");
//  set.insert("java.math.BigDecimal.add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;");
//  set.insert("java.math.BigDecimal.add(JIJI)Ljava/math/BigDecimal;");
//  set.insert("java.math.BigDecimal.valueOf(Ljava/math/BigInteger;II)Ljava/math/BigDecimal;");
  return set;
}

std::map<std::string, bool> SymBigDecimal::skip_method_names = init_skip_method_names();

std::map<std::string, bool> SymBigDecimal::init_skip_method_names() {
  std::map<std::string, bool> map;
  return map;
}

void SymBigDecimal::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->add_invoke_helper_methods(SymBigDecimal::TYPE_NAME, invoke_method_helper);
  m_symbolizer->add_finish_helper_methods(SymBigDecimal::TYPE_NAME, finish_method_helper);
}

SymBigDecimal::SymBigDecimal(sym_rid_t sym_rid, oop obj) : SymInstance(sym_rid), _exp(NULL),
                                                           _int_compact_offset(int_compact_offset(obj)),
                                                           _scale_offset(scale_offset(obj)) {}

SymBigDecimal::~SymBigDecimal() {}

bool SymBigDecimal::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  bool need_symbolize = false;
//  tty->print_cr("SymBigDecimal::invoke_method_helper:%s", handle.get_callee_method()->name_and_sig_as_C_string());

  if (handle_method_names.find(handle.get_callee_method()->name_and_sig_as_C_string()) != handle_method_names.end()) {
//    if (std::string(handle.get_callee_method()->name_and_sig_as_C_string()) == "java.math.BigDecimal.add(Ljava/math/BigDecimal;)Ljava/math/BigDecimal;") {
//      tty->print_cr("hit here");
//      return false;
//    }
//    if (std::string(handle.get_callee_method()->name_and_sig_as_C_string()) == "java.math.BigDecimal.add(JIJI)Ljava/math/BigDecimal;") {
//      tty->print_cr("hit here2");
//    }
    if (handle.general_check_param_symbolized()) {
      handle.general_prepare_param();
      if (callee_name == "java.math.BigDecimal.<init>(D)V") {
        oop thisDecimal = handle.get_param<oop>(0);
        assert(thisDecimal != NULL, "should not be null");
        SymBigDecimal *symObj = reinterpret_cast<SymBigDecimal *>(
            ConcolicMngr::ctx->get_or_alloc_sym_inst(thisDecimal)
        );
        assert(symObj, "???");
        return false;
      }
      return true;
    }
  }
  return need_symbolize;
}

// TODO: confirm whether we should take care intValue
Expression *SymBigDecimal::finish_method_helper(MethodSymbolizerHandle &handle) {
  ResourceMark rm;
  std::string signature = handle.get_callee_method()->name_and_sig_as_C_string();
//  tty->print_cr("SymBigDecimal::finish_method_helper %s", signature.c_str());
  if (signature == "java.math.BigDecimal.<init>(Ljava/lang/String;)V") {
    oop paramStr = handle.get_param<oop>(1);
    assert(paramStr->klass()->name()->equals(SymString::TYPE_NAME), "should be string");
    SymString *symStr = reinterpret_cast<SymString *>(
        ConcolicMngr::ctx->find_sym_inst(paramStr));
    if (symStr == NULL) {
      return NULL;
    }
    oop thisDecimal = handle.get_param<oop>(0);
    SymBigDecimal *symObj = reinterpret_cast<SymBigDecimal *>(
        ConcolicMngr::ctx->get_or_alloc_sym_inst(thisDecimal)
    );
    if (symObj == NULL) return NULL;
    Expression *refExp = symStr->get_ref_exp();

    guarantee(refExp != NULL, "Should not be null");
    if (refExp->is_op_str_expression()) {
      OpStrExpression *opExp = reinterpret_cast<OpStrExpression *>(refExp);
      if (opExp->get_op_name() == "valueOf") {
        guarantee(opExp->get_param_list().size() == 1, "Should contain only 1 parameter");
        // inner expression
        refExp = opExp->get_param_list()[0];
      } else {
        tty->print_cr("%s not implemented in sym big decimal conversion", opExp->get_name().c_str());
        ShouldNotCallThis();
      }
    }
    symObj->symbolize_bigDecimal(thisDecimal, refExp);
  } else if (signature == "java.math.BigDecimal.valueOf(J)Ljava/math/BigDecimal;" ||
             signature == "java.math.BigDecimal.valueOf(JII)Ljava/math/BigDecimal;") {
    guarantee(handle.get_callee_method()->is_static(), "should be static method");
    if (handle.get_param_list()[0] == NULL) {
      return NULL;
    }

    oop resultDecimal = handle.get_result<oop>(T_OBJECT);
    SymBigDecimal *symObj = reinterpret_cast<SymBigDecimal *>(
        ConcolicMngr::ctx->get_or_alloc_sym_inst(resultDecimal)
    );
    exp_list_t pam_lst = handle.get_param_list();
    guarantee(pam_lst[0] != NULL, "value symbol should not be null");
    symObj->set_sym_exp(
        symObj->int_compact_offset(resultDecimal), pam_lst[0]
    );

    if (pam_lst.size() > 1) {
      // for java.math.BigDecimal.valueOf(JII)Ljava/math/BigDecimal;
      symObj->set_sym_exp(
          symObj->scale_offset(resultDecimal), pam_lst[1]
      );
    } else {
      symObj->set_sym_exp(
          symObj->scale_offset(resultDecimal), new ConExpression(0)
      );
    }
  } else if (signature == "java.math.BigDecimal.valueOf(Ljava/math/BigInteger;II)Ljava/math/BigDecimal;") {
    ShouldNotCallThis();
  } else if (signature == "java.math.BigDecimal.<init>(I)V" ||
             signature == "java.math.BigDecimal.<init>(J)V") {
    Expression *param = handle.get_param_list()[1];
    guarantee(param != NULL, "Should not be null");
    oop thisDecimal = handle.get_param<oop>(0);
    assert(thisDecimal != NULL, "should not be null");
    SymBigDecimal *symObj = reinterpret_cast<SymBigDecimal *>(
        ConcolicMngr::ctx->get_or_alloc_sym_inst(thisDecimal)
    );
    // directly set int-compact to param expression
    symObj->set_sym_exp(symObj->_int_compact_offset, param);
    symObj->set_sym_exp(symObj->_scale_offset, new ConExpression(0));
  } else if (signature == "java.math.BigDecimal.<init>(D)V") {
    Expression *param = handle.get_param_list()[1];
    guarantee(param != NULL, "Should not be null");
    oop thisDecimal = handle.get_param<oop>(0);
    assert(thisDecimal != NULL, "should not be null");
    SymBigDecimal *symObj = reinterpret_cast<SymBigDecimal *>(
        ConcolicMngr::ctx->get_or_alloc_sym_inst(thisDecimal)
    );
    // TODO: seems there's symbolic lose in this way: param is not correctly related with symBigdecimal
    symObj->symbolize_bigDecimal(thisDecimal, param);
  } else if (signature == "java.math.BigDecimal.<init>(Ljava/math/BigInteger;JII)V") {
    Expression *intValExp = handle.get_param_list()[2];
    Expression *scaleExp = handle.get_param_list()[3];
    guarantee(intValExp != NULL, "Should not be null");
    guarantee(scaleExp != NULL, "Should not be null");
    oop thisDecimal = handle.get_param<oop>(0);
    assert(thisDecimal != NULL, "should not be null");
    SymBigDecimal *symObj = reinterpret_cast<SymBigDecimal *>(
        ConcolicMngr::ctx->get_or_alloc_sym_inst(thisDecimal)
    );
    // directly set int-compact to param expression
    symObj->set_sym_exp(symObj->_int_compact_offset, intValExp);
    symObj->set_sym_exp(symObj->_scale_offset, scaleExp);
  } else if (signature == "java.math.BigDecimal.setScale(II)Ljava/math/BigDecimal;") {
    jint newScale = handle.get_param<jint>(1);
    assert(newScale >= 0, "Scale should >= 0");
    assert(handle.get_param_list().size() == 3, "size should be 3");
    guarantee(handle.get_param_list()[1] == NULL || handle.get_param_list()[2],
              "currently only handle concrete scaling");
    oop thisDecimal = handle.get_param<oop>(0);
    oop resultDecimal = handle.get_result<oop>(T_OBJECT);
    assert(thisDecimal->klass()->name() == vmSymbols::java_math_BigDecimal(), "should be");
    assert(resultDecimal->klass()->name() == vmSymbols::java_math_BigDecimal(), "should be");
    SymBigDecimal *symThisDecimal = reinterpret_cast<SymBigDecimal *>(
        ConcolicMngr::ctx->find_sym_inst(thisDecimal));
    SymBigDecimal *symResDecimal = reinterpret_cast<SymBigDecimal *>(ConcolicMngr::ctx->get_or_alloc_sym_inst(
        resultDecimal));
    guarantee(symThisDecimal != NULL, "Only handle symbolic decimal case[symThisDecimal]");
    guarantee(symResDecimal != NULL, "Only handle symbolic decimal case[symResDecimal]");
    int intCmpFldOffset = symThisDecimal->_int_compact_offset;
    int scaleFldOffset = symThisDecimal->_scale_offset;
    Expression *intCmpExp = symThisDecimal->get(intCmpFldOffset);
    Expression *scaleExp = symThisDecimal->get(scaleFldOffset);
    if (intCmpExp == NULL && scaleExp == NULL) {
      // not a correctly initialized symbolic decimal
      ShouldNotCallThis();
    }

    int curScale = thisDecimal->int_field(scaleFldOffset);
    guarantee(newScale == resultDecimal->int_field(scaleFldOffset), "newScale in parameter should equals to result decimal's scale");
    Expression* newScaleExp = new ConExpression(newScale);
    symResDecimal->set_sym_exp(
        scaleFldOffset,
        newScaleExp
    );
    if (newScale > curScale) {
      long num = std::pow(10, newScale - curScale);
      symResDecimal->set_sym_exp(
          intCmpFldOffset,
          new OpSymExpression(intCmpExp, new ConExpression(num), op_mul)
      );
    } else if (newScale < curScale) {
      long num = std::pow(10, curScale - newScale);
      symResDecimal->set_sym_exp(
          intCmpFldOffset,
          new OpSymExpression(intCmpExp, new ConExpression(num), op_div)
      );
    } else {
      // scale not changed
      symResDecimal->set_sym_exp(
          intCmpFldOffset,
          intCmpExp
      );
    }
  }
  return NULL;
}

Expression *SymBigDecimal::get_exp_of(oop obj) {
  SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(obj);
  return sym_inst == NULL ? get_con_exp(obj) : sym_inst->get_ref_exp();
}

Expression *SymBigDecimal::get_con_exp(oop obj) {
  oop str_obj = OopUtils::bigd_to_java_string(obj);
  ResourceMark rm;
  const char *str = OopUtils::java_string_to_c(str_obj);
  return new ConSymbolExp(str, T_DOUBLE);
}

void SymBigDecimal::print() {
  tty->print_cr("SymBigDecimal: ");
  _exp->print();
  tty->print("\n");
}

// Last-writer-wins under _field_mutex, exactly as for SymObj::_exps; see the
// field-shadow write policy in sessionSymbolicHeap.hpp.
void SymBigDecimal::set_sym_exp(int field_offset, Expression *exp) {
  FieldLock guard(this);
  _internal_fields[field_offset] = exp;
  _exp = NULL;
}


void SymBigDecimal::set_bigDecimal_symbolic(oop decimalOOp, std::string name) {
  std::string intCmpName = DECIMAL_WRAPPER
                           + name
                           + "#intCompact"
                           + DECIMAL_WRAPPER;

  std::string scaleName = DECIMAL_WRAPPER
                          + name
                          + "#scale"
                          + DECIMAL_WRAPPER;

  init_sym_exp(_int_compact_offset, new SymbolExpression(intCmpName.c_str(), intCmpName.length()));
  init_sym_exp(_scale_offset, new SymbolExpression(scaleName.c_str(), scaleName.length()));
}

void SymBigDecimal::init_sym_exp(int field_offset, Expression *exp) {
  guarantee(exp != NULL, "should not be null");
  FieldLock guard(this);
  _internal_fields[field_offset] = exp;
  _exp = NULL;
}

Expression *SymBigDecimal::get(int field_offset) {
  FieldLock guard(this);
  std::map<int, Expression *>::iterator found =
      _internal_fields.find(field_offset);
  return found == _internal_fields.end() ? NULL : found->second;
}

bool SymBigDecimal::has_sym_exp(int field_offset) {
  FieldLock guard(this);
  return _internal_fields.find(field_offset) != _internal_fields.end();
}

void SymBigDecimal::symbolize_bigDecimal(oop decimalOOp, Expression *parentExp) {
  this->set_bigDecimal_symbolic(decimalOOp, parentExp->get_name());
}

int SymBigDecimal::int_compact_offset(oop decimalOOp) {
  assert(decimalOOp != NULL, "Should not be null");
  Klass *bdClz = decimalOOp->klass();
  guarantee(bdClz->name() == vmSymbols::java_math_BigDecimal(), "should equal");

  fieldDescriptor fd_intCmp;
  bdClz->find_field(
      vmSymbols::bd_intCompact(),
      vmSymbols::long_signature(),
      &fd_intCmp
  );
  return fd_intCmp.offset();
}

int SymBigDecimal::scale_offset(oop decimalOOp) {
  assert(decimalOOp != NULL, "Should not be null");
  Klass *bdClz = decimalOOp->klass();
  guarantee(bdClz->name() == vmSymbols::java_math_BigDecimal(), "should equal");

  fieldDescriptor fd_scale;
  bdClz->find_field(
      vmSymbols::bd_scale(),
      vmSymbols::int_signature(),
      &fd_scale
  );
  return fd_scale.offset();
}

Expression *SymBigDecimal::get_ref_exp() {
  if (_exp == NULL) {
    set_ref_exp(
        new BigDecimalExpression(
            get(_scale_offset), get(_int_compact_offset)
        )
    );
  }
  return _exp;
}

BigDecimalExpression::BigDecimalExpression(Expression *scale, Expression *intCompact) : _scale(scale),
                                                                                        _intCompact(intCompact) {
  if (_scale == NULL) {
    _scale = new ConExpression(0);
  }
  if (_intCompact == NULL) {
    _intCompact = new ConExpression(0);
  }
}

BigDecimalExpression::~BigDecimalExpression() {}

void __attribute__((optimize("O0"))) BigDecimalExpression::serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("BigDecimalExpression");

  writer.Key("_scale");
  if (_scale != NULL) {
    _scale->serialize(writer);
  } else {
    Expression* e = new ConExpression(0);
    e->serialize(writer); // TODO: check when this field could be 0
  }

  writer.Key("_intCompact");
  if (_intCompact != NULL) {
    _intCompact->serialize(writer);
  } else {
    Expression* e = new ConExpression(0);
    e->serialize(writer); // TODO: check when this field could be 0
  }
}


#endif
