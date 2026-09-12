#ifdef ENABLE_CONCOLIC

#include <concolic/exp/stringExpression.hpp>
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/methodExpression.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/utils.hpp"

const char *SymStrBuilder::TYPE_NAME = "java/lang/StringBuilder";
method_set_t SymStrBuilder::handle_method_names = init_handle_method_names();
std::map<std::string, bool> SymStrBuilder::skip_method_names =
    init_skip_method_names();

method_set_t SymStrBuilder::init_handle_method_names() {
  method_set_t m_set;
  m_set.insert("append");
  m_set.insert("toString");
  m_set.insert("length");
  return m_set;
}

std::map<std::string, bool> SymStrBuilder::init_skip_method_names() {
  std::map<std::string, bool> map;
  // The concrete bodies of these methods are deliberately not summarized.
  // In particular, an empty StringBuilder constructor has no symbolic input
  // and must not open a symbolic method frame: Hadoop constructs builders for
  // ordinary logging on virtually every service thread.  Treating every
  // constructor as symbolic retains one dead expression per log message and
  // lets unrelated formatting dominate a bounded concolic session.
  map["<init>"] = false;
  map["setLength"] = false;
  return map;
}

void SymStrBuilder::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->add_invoke_helper_methods(SymStrBuilder::TYPE_NAME, invoke_method_helper);
  m_symbolizer->add_finish_helper_methods(SymStrBuilder::TYPE_NAME, finish_method_helper);
}

SymStrBuilder::SymStrBuilder(sym_rid_t sym_rid)
    : SymInstance(sym_rid), _exp(NULL), _ref_exp(NULL) {
}

SymStrBuilder::~SymStrBuilder() {}

void SymStrBuilder::set_sym_exp(int field_offset, Expression *exp) {
  // StringBuilder state is represented by its append/concat reference
  // expression.  Once a builder has that shadow, ordinary append execution
  // still writes AbstractStringBuilder.value/count.  Those implementation
  // fields must stay concrete: recording them would mix the field model with
  // the atomic append model, while rejecting them crashes unrelated code that
  // happens to format a symbolic value.  Keep the existing reference
  // expression; finish_method_helper updates it at the append boundary.
  (void) field_offset;
  (void) exp;
}

bool SymStrBuilder::has_sym_exp(int field_offset) {
  // set_sym_exp above stores nothing per field, so no field ever carries one.
  (void) field_offset;
  return false;
}

bool SymStrBuilder::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  bool need_symbolize = false;
  ResourceMark mr;
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    need_symbolize = handle.general_check_param_symbolized();
    if (need_symbolize) {
      SymStrBuilder::prepare_param(handle);
    }
  } else {
    std::map<std::string, bool>::iterator iter =
        skip_method_names.find(callee_name);
    if (iter != skip_method_names.end()) {
      need_symbolize = iter->second
          && handle.general_check_param_symbolized();
    }
  }
  return need_symbolize;
}

void SymStrBuilder::prepare_param(MethodSymbolizerHandle &handle) {
  Method *callee_method = handle.get_callee_method();

  int offset = handle.get_callee_local_begin_offset();

  if (!callee_method->is_static()) {
    SymStrBuilder::prepare_param_helper(handle, T_OBJECT, offset);
    ++offset;
  }

  ResourceMark rm;
  SignatureStream ss(callee_method->signature());
  while (!ss.at_return_type()) {
    offset = SymStrBuilder::prepare_param_helper(handle, ss.type(), offset);
    ss.next();
    ++offset;
  }
}

int SymStrBuilder::prepare_param_helper(MethodSymbolizerHandle &handle,
                                        BasicType type, int locals_offset) {
  Expression *exp = NULL;

  if (is_java_primitive(type)) {
    exp = OpStrExpression::to_string(handle.get_primitive_exp(locals_offset, type));
    locals_offset += type2size[type] - 1;
  } else if (type == T_OBJECT) {
    oop obj = handle.get_param<oop>(locals_offset);
    if (obj == NULL) {
      if (handle.get_callee_name() == "append") {
        exp = new ConStringSymbolExp(std::string("null"));
      } else {
        ShouldNotCallThis();
      }
    } else {
      exp = SymStrBuilder::get_exp_of(obj);
    }

  } else if (type == T_ARRAY) {
    arrayOop arr_obj = handle.get_param<arrayOop>(locals_offset);
    exp = ConcolicMngr::ctx->container_state(arr_obj, "INDEXED");
    if (exp == NULL) exp = ContainerSupport::concrete_value(arr_obj);
  } else {
    tty->print_cr("unhandled String parameter types!");
    ShouldNotCallThis();
  }

  handle.get_param_list().push_back(exp);
  return locals_offset;
}

void __attribute__((optimize("O0"))) SymStrBuilder::add_to_string_for_param_list(MethodSymbolizerHandle &handle, exp_list_t &ret) {
  exp_list_t &param_list = handle.get_param_list();

  Method *callee_method = handle.get_callee_method();

  int offset = handle.get_callee_local_begin_offset();

  ResourceMark rm;
  SignatureStream ss(callee_method->signature());
//  callee_method->signature()->print();
//  tty->cr();
  // skip `this`
  offset += 1;
  int i = 1;
  ret.push_back(param_list[0]);
  while (!ss.at_return_type()) {
    BasicType type = ss.type();
    Expression *parameter = param_list[i];
    guarantee(parameter != NULL,
              "StringBuilder parameter expression must be materialized");
    bool string_object = false;
    if (type == T_OBJECT) {
      oop obj = handle.get_param<oop>(offset);
      string_object = obj != NULL && obj->is_instance()
          && (obj->klass()->name()->equals(SymString::TYPE_NAME)
              || obj->klass()->name()->equals(SymStrBuilder::TYPE_NAME));
    }
    if (string_object
        || (parameter->is_op_str_expression()
            && strncmp("toString",
                       ((OpStrExpression *)parameter)->get_op_name().c_str(),
                       8) == 0)) {
      ret.push_back(parameter);
    } else {
      ret.push_back(new OpStrExpression("toString", parameter));
    }
    i++;
    ss.next();
    offset += type2size[type];
  }
}

Expression *
SymStrBuilder::finish_method_helper(MethodSymbolizerHandle &handle) {
  BasicType type = handle.get_result_type();
  Expression *exp = NULL;
  oop result = type == T_OBJECT ? handle.get_result<oop>(type) : NULL;

  const std::string &callee_name = handle.get_callee_name();
  if (callee_name == "append") {
    exp_list_t string_exp_list;
    add_to_string_for_param_list(handle, string_exp_list);
    exp = new OpStrExpression("concat", string_exp_list);
    SymStrBuilder *sym_res_strBuilder =
        (SymStrBuilder *)ConcolicMngr::ctx->get_or_alloc_sym_inst(result);
    if (sym_res_strBuilder != NULL) {
      // append mutates the receiver, so updating its object state is
      // intentional; the same expression also travels on the return edge.
      sym_res_strBuilder->set_ref_exp(exp);
    }
  } else if (callee_name == "toString") {
    oop receiver = handle.get_param<oop>(0);
    SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(receiver);
    exp = sym_inst == NULL ? NULL : sym_inst->get_ref_exp();
    if (exp != NULL && result != NULL && result != receiver
        && !ConcolicMngr::ctx->requires_detached_object_shadow(result)) {
      SymString *sym_res_str = (SymString *)
          ConcolicMngr::ctx->get_or_alloc_sym_inst(result);
      if (sym_res_str != NULL) {
        sym_res_str->set_ref_exp(exp);
      }
    }
  } else {
    exp = new OpStrExpression(callee_name, handle.get_param_list());
  }
  return exp;
}

Expression *SymStrBuilder::get_exp_of(oop obj) {
  if (obj == NULL) return SymbolExpression::get(Sym_NULL);
  SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(obj);
  if (sym_inst != NULL && sym_inst->has_semantic_expression()
      && sym_inst->get_ref_exp() != NULL) {
    return sym_inst->get_ref_exp();
  }

  // The first symbolic append can follow any number of concrete appends.  At
  // that point the receiver is a concrete string prefix, not a symbolic Java
  // object identity.  Snapshot the prefix so the resulting concat is a
  // string-valued expression (and so a later equals/contains keeps the exact
  // Java value).  Once an append has installed semantic state, the branch
  // above reuses it and no later snapshot can overwrite symbolic history.
  ResourceMark rm;
  return new ConStringSymbolExp(
      std::string(OopUtils::java_string_to_c(obj)));
}

#endif
