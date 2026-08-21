#ifdef ENABLE_CONCOLIC

#include "concolic/reference/symbolicString.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/utils.hpp"
#include "oops/objArrayOop.hpp"
#include <concolic/exp/methodExpression.hpp>
#include <concolic/exp/stringExpression.hpp>

const char *SymString::ARRAY_TYPE_NAME = "[Ljava/lang/String;";
const char *SymString::TYPE_NAME = "java/lang/String";
method_set_t SymString::handle_method_names = init_handle_method_names();
std::map<std::string, bool> SymString::skip_method_names =
    init_skip_method_names();

namespace {

bool result_aliases_reference_input(MethodSymbolizerHandle &handle,
                                    oop result) {
  if (result == NULL) return false;
  Method *method = handle.get_callee_method();
  int offset = handle.get_callee_local_begin_offset();
  if (!method->is_static()) {
    if (handle.get_param<oop>(offset) == result) return true;
    ++offset;
  }
  ResourceMark rm;
  SignatureStream signature(method->signature());
  while (!signature.at_return_type()) {
    BasicType type = signature.type();
    if ((type == T_OBJECT || type == T_ARRAY)
        && handle.get_param<oop>(offset) == result) {
      return true;
    }
    offset += type2size[type];
    signature.next();
  }
  return false;
}

}  // namespace

method_set_t SymString::init_handle_method_names() {
  method_set_t m_set;
  m_set.insert("charAt");
  m_set.insert("compareTo");
  m_set.insert("concat");
  m_set.insert("copyValueOf");
  m_set.insert("compareToIgnoreCase");
  m_set.insert("contains");
  m_set.insert("endsWith");
  m_set.insert("equals");
  m_set.insert("equalsIgnoreCase");
  m_set.insert("getChars");
  m_set.insert("hashCode");
  m_set.insert("isEmpty");
  m_set.insert("indexOf");
  m_set.insert("intern");
  m_set.insert("lastIndexOf");
  m_set.insert("length");
  m_set.insert("matches");
  m_set.insert("regionMatches");
  m_set.insert("replace");
  m_set.insert("replaceAll");
  m_set.insert("replaceFirst");
  m_set.insert("split");
  m_set.insert("startsWith");
  m_set.insert("subSequence");
  m_set.insert("substring");
  m_set.insert("toCharArray");
  m_set.insert("toLowerCase");
  m_set.insert("toUpperCase");
  m_set.insert("trim");
  m_set.insert("valueOf");
  m_set.insert("<init>");
  m_set.insert("getBytes");
  m_set.insert("toString");
  return m_set;
}

std::map<std::string, bool> SymString::init_skip_method_names() {
  std::map<std::string, bool> map;
  map["contentEquals"] = false;
  return map;
}

void SymString::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->add_invoke_helper_methods(SymString::TYPE_NAME, invoke_method_helper);
  m_symbolizer->add_finish_helper_methods(SymString::TYPE_NAME, finish_method_helper);
}

SymString::SymString(sym_rid_t sym_rid)
    : SymInstance(sym_rid), _exp(NULL), _ref_exp(NULL) {
  this->set_ref_exp(new StringSymbolExp(_sym_rid));
  this->clear_semantic_expression();
}

SymString::~SymString() {}

void SymString::print() {
  tty->print_cr("SymString: ");
  _ref_exp->print_cr();
}

bool SymString::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  bool need_symbolize = false;
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    need_symbolize = handle.general_check_param_symbolized();
    if (need_symbolize) {
      SymString::prepare_param(handle);
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

void SymString::prepare_param(MethodSymbolizerHandle &handle) {
  Method *callee_method = handle.get_callee_method();
  const std::string callee_name = handle.get_callee_name();

  int offset = handle.get_callee_local_begin_offset();

  if (!callee_method->is_static()) {
    SymString::prepare_param_helper(handle, T_OBJECT, offset);
    ++offset;
  }

  if (callee_name == "toLowerCase" || callee_name == "toUpperCase" ) {
    return;
  }

  ResourceMark rm;
  SignatureStream ss(callee_method->signature());
  while (!ss.at_return_type()) {
    offset = SymString::prepare_param_helper(handle, ss.type(), offset);
    ss.next();
    ++offset;
  }
}

int SymString::prepare_param_helper(MethodSymbolizerHandle &handle,
                                    BasicType type, int locals_offset) {
  Expression *exp = NULL;

  if (is_java_primitive(type)) {
    exp = handle.get_primitive_exp(locals_offset, type);
    locals_offset += type2size[type] - 1;
  } else if (type == T_OBJECT) {
    oop obj = handle.get_param<oop>(locals_offset);
//    guarantee(obj != NULL, "should be");
    if (obj == NULL) {
      exp = SymbolExpression::get(Sym_NULL);
    } else {
      exp = handle.get_reference_exp(locals_offset, obj);
      if (exp != NULL) {
        // Preserve an owner-field alias shadow even when obj is an interned
        // literal with an intentionally concrete oop header.
      } else if (obj->klass()->name()->equals("sun/nio/cs/UTF_8")) {
        // no need to symbolize parameter of {public byte[] getBytes(Charset charset)}
        exp = NULL;
      } else {
        exp = SymString::get_exp_of(obj);
      }
    }
  } else if (type == T_ARRAY) {
    arrayOop arr_obj = handle.get_param<arrayOop>(locals_offset);
    exp = ConcolicMngr::ctx->container_state(arr_obj, "INDEXED");
  } else {
    tty->print_cr("unhandled String parameter types!");
    ShouldNotCallThis();
  }

  handle.get_param_list().push_back(exp);
  return locals_offset;
}

Expression *SymString::finish_method_helper(MethodSymbolizerHandle &handle) {
  // A prepared parameter list is local to this thread's MethodSymbolizerHandle.
  // Do not use class-global recording state here: another Java thread can enter
  // a String method while this call is executing.
  if (!handle.get_param_list().empty()) {
    const std::string &callee_name = handle.get_callee_name();
    BasicType type = handle.get_result_type();
    Expression *exp = NULL;
    oop obj = NULL;
//    tty->print_cr("SymString finish_method_helper %s", callee_name.c_str());
    switch (type) {
    case T_VOID:
//      if (callee_name == "getChars") {
//        ShouldNotReachHere();
//      }
      exp = SymbolExpression::get(Sym_VOID);
      break;
    case T_OBJECT:
      if (handle.get_callee_method()->is_native()) {
        obj = handle.get_callee_istate()->oop_temp();
      } else {
        obj = handle.get_result<oop>(type);
      }
      if (obj != NULL) {
        guarantee(obj->klass()->name()->equals(SymString::TYPE_NAME), "should be");
        // Always return the derived value through the caller's operand edge.
        // Object-wide state is safe only for a fresh, non-detached result:
        // several String APIs legally return their receiver, another input,
        // or a VM-global interned object for this concrete execution.
        // In particular, String.intern keeps the exact oop chosen by the JVM.
        // Its symbolic content follows only the returned operand edge; this
        // engine does not attempt to model or rewrite intern-table identity.
        bool identity_result = callee_name == "toString"
            || callee_name == "intern";
        exp = identity_result
            ? handle.get_param_list()[0]
            : static_cast<Expression *>(new OpStrExpression(
                  callee_name, handle.get_param_list()));
        bool aliases_input = result_aliases_reference_input(handle, obj);
        bool may_return_shared_alias = callee_name == "intern";
        if (!aliases_input && !may_return_shared_alias
            && !ConcolicMngr::ctx->requires_detached_object_shadow(obj)) {
          SymInstance *sym_inst =
              ConcolicMngr::ctx->get_or_alloc_sym_inst(obj);
          if (sym_inst != NULL) {
            sym_inst->set_ref_exp(exp);
          }
        }
      } else {
        exp = SymbolExpression::get(Sym_NULL);
      }
      break;
    case T_ARRAY:
      if (callee_name == "split") {
        objArrayOop result =
            (objArrayOop) handle.get_result<oop>(T_ARRAY);
        if (result != NULL) {
          symbolize_split_elements(handle, result);
        }
      }
      break;
    case T_BOOLEAN: {
      // Keep the *unpolarized* predicate on the shadow operand stack.  The
      // concrete method result says nothing about the identity of this value:
      // it is only one observation.  istore/iload and Boolean operations must
      // therefore carry contains(receiver, needle), never an expression that
      // has already been rewritten to the observed path.  ifeq/ifne applies
      // the actual branch polarity when the value is finally consumed.
      exp = new OpStrExpression(callee_name, handle.get_param_list(),
                                false);
      break;
    }
    default:
      exp = new OpStrExpression(callee_name, handle.get_param_list());
    }
    return exp;
  } else {
    return NULL;
  }
}

void SymString::symbolize_split_elements(MethodSymbolizerHandle &handle,
                                         objArrayOop result) {
  exp_list_t &split_params = handle.get_param_list();
  for (int index = 0; index < result->length(); ++index) {
    oop element = result->obj_at(index);
    if (element == NULL) continue;
    if (!element->klass()->name()->equals(SymString::TYPE_NAME)) {
      continue;
    }

    exp_list_t element_params;
    for (size_t param_index = 0; param_index < split_params.size();
         ++param_index) {
      element_params.push_back(split_params[param_index]);
    }
    element_params.push_back(new ConExpression((jint) index));

    // A split element may be the receiver, an existing symbolic alias, or an
    // interned String; none of those identities may be overwritten
    // object-wide. The result array is promoted to the shared indexed state.
    SymInstance *existing = ConcolicMngr::ctx->find_sym_inst(element);
    Expression *element_result = existing == NULL
        ? static_cast<Expression *>(new ConStringSymbolExp(element))
        : existing->get_or_create_ref_exp(element);
    Expression *derived = new MethodExpression(
        handle.get_callee_holder_name(), "splitElement", element_params,
        element_result, false);
    ConcolicMngr::ctx->write_array_element(result, index, derived);

    bool aliases_input = result_aliases_reference_input(handle, element);
    if (existing == NULL && !aliases_input
        && !ConcolicMngr::ctx->requires_detached_object_shadow(element)) {
      SymInstance *fresh = ConcolicMngr::ctx->get_or_alloc_sym_inst(element);
      if (fresh != NULL) fresh->set_ref_exp(derived);
    }
  }
}

Expression *SymString::get_exp_of(oop obj) {
  if (obj == NULL) return SymbolExpression::get(Sym_NULL);

  SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(obj);
  return sym_inst == NULL
      ? static_cast<Expression *>(new ConStringSymbolExp(obj))
      : sym_inst->get_ref_exp();
}

void SymString::set_sym_exp(int field_offset, Expression *exp) {
  // String content is represented atomically by the reference expression
  // installed at a handled String call boundary.  Constructor execution can
  // still copy a shadowed char[] into the private value field before such a
  // boundary is selected.  Treat that implementation write like the
  // corresponding StringBuilder value/count writes: the concrete JVM field
  // is authoritative, while a field-level shadow would mix an indexed-array
  // expression into the String model.
  (void) field_offset;
  (void) exp;
}

bool SymString::get_condition_value(oop s1, oop s2, std::string comp) {
  return false;
}

#endif
