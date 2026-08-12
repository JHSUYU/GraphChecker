#ifdef ENABLE_CONCOLIC

#include "concolic/methodSymbolizer.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/methodExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/jdbc/reference/symbolicConnection.hpp"
#include "concolic/jdbc/reference/symbolicPersister.hpp"
#include "concolic/jdbc/reference/symbolicResultSet.hpp"
#include "concolic/jdbc/reference/symbolicStatement.hpp"
#include "concolic/reference/symbolicEmailValidator.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/reference/symbolicStringUtils.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/symbolicSet.hpp"
#include "concolic/reference/symbolicList.hpp"
#include "concolic/reference/symbolicBigDecimal.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicTimestamp.hpp"
#include "concolic/reference/symbolicDate.hpp"
#include "concolic/reference/symbolicMiscObjects.h"
#include "concolic/reference/symbolicAtomic.hpp"
#include "concolic/reference/internal/symbolicUnsafe.hpp"
#include "concolic/jdbc/reference/symbolicHibernateKey.hpp"
#include "concolic/jdbc/reference/symbolicHibernateMethod.hpp"
#include "concolic/reference/symbolicHttpServletRequest.hpp"
#include "concolic/reference/symbolicNDFunc.hpp"
#include "memory/resourceArea.hpp"
#include "runtime/thread.hpp"
#include "runtime/signature.hpp"
#include "utilities/exceptions.hpp"
#include "utilities/ostream.hpp"

MethodSymbolizer::MethodSymbolizer() : _symbolizing_method(false), _has_callbacks(false) {
  init_helper_methods();
  handling_methods.clear();
}

void MethodSymbolizer::init_helper_methods() {
  SymString::init_register_class(this);
  SymStrBuilder::init_register_class(this);
  SymEmailValidator::init_register_class(this);
  SymStrUtils::init_register_class(this);
  SymConn::init_register_class(this);
  SymStmt::init_register_class(this);
  SymResSet::init_register_class(this);
  SymMap::init_register_class(this);
  SymSet::init_register_class(this);
  SymList::init_register_class(this);
  SymBigDecimal::init_register_class(this);
  SymTimestamp::init_register_class(this);
  SymbolicDate::init_register_class(this);
  SymbolicAtomic::init_register_class(this);
//  SymHibernateKey::init_register_class(this);
//  SymHibernateMethod::init_register_class(this);
  SymbolicUnsafe::init_register_class(this);
//  SymbolicHttpServletRequest::init_register_class(this);
  SymbolicNDFunc::init_register_class(this);
  SymbolicMiscObjects::init_register_class(this);
}

void MethodSymbolizer::add_invoke_helper_methods(const std::string class_name,
                                                 bool (*invoke_helper_func)(MethodSymbolizerHandle &)) {
  _invoke_helper_methods[class_name] = invoke_helper_func;
}

void MethodSymbolizer::add_finish_helper_methods(const std::string class_name,
                                                 Expression *(*finish_helper_func)(MethodSymbolizerHandle &)) {
  _finish_helper_methods[class_name] = finish_helper_func;
}

MethodSymbolizer::~MethodSymbolizer() {
  for (SymClassMapIt sym_class_map_it = _symbolicMethods.begin();
       sym_class_map_it != _symbolicMethods.end(); ++sym_class_map_it) {
    if (sym_class_map_it->second) {
      delete sym_class_map_it->second;
    }
  }
}

void MethodSymbolizer::add_method(const char *class_name,
                                  const char *method_name) {
  SymClassMapIt sym_class_map_it =
      _symbolicMethods
          .insert(std::make_pair(std::string(class_name), (SymMethodSet *) NULL))
          .first;
  if (sym_class_map_it->second == NULL) {
    sym_class_map_it->second = new SymMethodSet();
  }
  sym_class_map_it->second->insert(std::string(method_name));
}


static bool names(Symbol *symbol, const std::string &registered) {
  return symbol != NULL
      && symbol->equals(registered.c_str(), (int)registered.size());
}

static bool boxes_a_primitive(Symbol *holder) {
  return holder->equals(SymPrimitive<jchar>::TYPE_NAME)
      || holder->equals(SymPrimitive<jboolean>::TYPE_NAME)
      || holder->equals(SymPrimitive<jbyte>::TYPE_NAME)
      || holder->equals(SymPrimitive<jint>::TYPE_NAME)
      || holder->equals(SymPrimitive<jshort>::TYPE_NAME)
      || holder->equals(SymPrimitive<jlong>::TYPE_NAME)
      || holder->equals(SymPrimitive<jfloat>::TYPE_NAME)
      || holder->equals(SymPrimitive<jdouble>::TYPE_NAME);
}

/**
 * Whether this callee's value is decided by a registered handler.
 *
 * This mirrors the dispatch invoke_method performs, and exists for the
 * interpreter entry points that answer a call without building a Java frame.
 * Such an entry point never reaches invoke_method, so a handled callee would
 * silently fall back to whatever its bytecode happens to look like -- for a
 * container accessor, an untracked field read where a container relation was
 * owed.
 *
 * The holder name is compared against the registration keys as a Symbol, so
 * this asks its question on the interpreter's hot path without allocating
 * and without caching anything whose lifetime it would then have to reason
 * about.  Almost every candidate fails on length alone.
 */
bool MethodSymbolizer::intercepts(Method *callee_method) {
  if (callee_method == NULL || callee_method->method_holder() == NULL) {
    return false;
  }
  Symbol *holder = callee_method->method_holder()->name();
  if (holder == NULL) return false;

  for (invoke_helper_method_map_t::const_iterator helper =
           _invoke_helper_methods.begin();
       helper != _invoke_helper_methods.end(); ++helper) {
    if (names(holder, helper->first)) return true;
  }
  for (SymClassMap::const_iterator holder_methods = _symbolicMethods.begin();
       holder_methods != _symbolicMethods.end(); ++holder_methods) {
    if (!names(holder, holder_methods->first)
        || holder_methods->second == NULL) {
      continue;
    }
    Symbol *name = callee_method->name();
    for (SymMethodSet::const_iterator method = holder_methods->second->begin();
         method != holder_methods->second->end(); ++method) {
      if (names(name, *method)) return true;
    }
  }
  if (boxes_a_primitive(holder)) return true;
  const std::set<std::string> &persisted = SymPersister::targets();
  for (std::set<std::string>::const_iterator persister = persisted.begin();
       persister != persisted.end(); ++persister) {
    if (names(holder, *persister)) return true;
  }
  // Only the prefix registry matches on a substring rather than the whole
  // name, so it is the one test that needs the name as a string.  It is
  // empty unless something registered a prefix, and then the conversion is
  // that registration's own cost.
  if (_classes_prefix_to_symbolize.empty()) return false;
  ResourceMark rm;
  std::string holder_name(holder->as_C_string());
  for (size_t index = 0; index < _classes_prefix_to_symbolize.size();
       ++index) {
    if (holder_name.find(_classes_prefix_to_symbolize[index])
        != std::string::npos) {
      return true;
    }
  }
  return false;
}

void MethodSymbolizer::invoke_method(ZeroFrame *caller_frame,
                                     ZeroFrame *callee_frame) {
  if (!callee_frame->is_interpreter_frame()) {
    return;
  }

  _handle.set_caller_frame(caller_frame);
  _handle.set_callee_frame(callee_frame);
  Method *callee_method = _handle.get_callee_method();
  if (callee_method == NULL)
    return;

  ResourceMark rm;

  _handle.set_callee_holder_name(
      callee_method->method_holder()->name()->as_C_string());
  _handle.set_callee_name(callee_method->name()->as_C_string());
//  if (_handle.get_callee_name() == "executeQuery") {
//    tty->print_cr("intercepting execute query... of %s, can do concolic:%d",
//                  _handle.get_callee_holder_name().c_str(),
//                  ConcolicMngr::can_do_concolic());
//  }

  /**
   * Whether we need to symbolize the process of this function
   */
  bool need_symbolize = false;
  SymMethodSet *sym_methods =
      this->get_sym_methods(_handle.get_callee_holder_name());
  BasicType basicType = primitive_target(_handle.get_callee_holder_name());
  const std::string& callee_holder_name = _handle.get_callee_holder_name();

  if (basicType != T_ILLEGAL) {
    need_symbolize = primitive_invoke_method_helper(_handle, basicType);
  } else if (_invoke_helper_methods.find(callee_holder_name) != _invoke_helper_methods.end()) {
    need_symbolize = _invoke_helper_methods[callee_holder_name](_handle);
//    if (need_symbolize) {
//      tty->print_cr("symbolizing method: %s.%s", callee_holder_name.c_str(), _handle.get_callee_name().c_str());
//    }
  } else if (SymPersister::target(_handle.get_callee_holder_name())) {
    need_symbolize = false;
    bool need_handling = SymPersister::invoke_method_helper(_handle);
    if (need_handling) {
      handling_methods.push_back(_handle);
    }
  } else if (sym_methods != NULL &&
             sym_methods->find(_handle.get_callee_name()) !=
             sym_methods->end()) {
//    tty->print_cr("Calling function name: %s",
//                  callee_method->name_and_sig_as_C_string());
    invoke_method_helper(_handle);
    need_symbolize = true;
  } else {
    for (size_t klz_index = 0;
         klz_index < _classes_prefix_to_symbolize.size();
         ++klz_index) {
      if (callee_holder_name.find(_classes_prefix_to_symbolize[klz_index]) != std::string::npos) {
        need_symbolize = true;
//        tty->print_cr("symbolizing method: %s.%s", callee_holder_name.c_str(), _handle.get_callee_name().c_str());
      }
    }
  }

  if (need_symbolize) {
    // MethodSymbolizer captures arguments directly at the call boundary and
    // then pauses ordinary bytecode propagation for the callee.  Its
    // structural shadow frame cannot perform normal caller cleanup, so
    // consume the complete JVM-word argument footprint here.
    ConcolicMngr::ctx->clear_stack_words(
        _handle.get_caller_stack_begin_offset(),
        callee_method->size_of_parameters());
    this->set_symbolizing_method(true);
  } else {
    _handle.reset();
  }
}

void __attribute__((optimize("O0"))) MethodSymbolizer::finish_method(ZeroFrame *caller_frame) {
  if (caller_frame == _handle.get_caller_frame()) {
    if (ConcolicMngr::ctx->get_thread()->has_pending_exception()) {
      // Exceptional unwind has no Java result.  Reset symbolizer state only;
      // the real handler will establish the new operand-stack contents.
      this->_handle.reset();
      this->set_symbolizing_method(false);
      return;
    }
    Expression *exp = NULL;
    BasicType basicType = primitive_target(_handle.get_callee_holder_name());
    const std::string& callee_holder_name = _handle.get_callee_holder_name();

    if (basicType != T_ILLEGAL) {
      exp = primitive_finish_method_helper(_handle, basicType);
    } else if (_finish_helper_methods.find(callee_holder_name) != _finish_helper_methods.end()) {
      exp = _finish_helper_methods[callee_holder_name](_handle);
    } else {
      exp = finish_method_helper(_handle);
    }

    BasicType type = _handle.get_result_type();
    int result_slots = type2size[type];
    if (result_slots > 0) {
      assert(result_slots == 1 || result_slots == 2,
             "a JVM result occupies one or two stack words");
      // A category-2 result is anchored in its second word.  Clear the whole
      // result footprint even when a helper returns no symbolic expression;
      // otherwise a prior category-1 value can survive in the companion word.
      ConcolicMngr::ctx->set_stack_value_if_possible(
          _handle.get_caller_stack_begin_offset() + result_slots - 1,
          result_slots, exp);
    }
    this->_handle.reset();
    this->set_symbolizing_method(false);
  }
}

// only for those are not symbolized method
bool MethodSymbolizer::has_handling_methods() {
  return !handling_methods.empty();
}

void MethodSymbolizer::finish_handling_method(ZeroFrame *caller_frame) {
  guarantee(has_handling_methods(), "should be");
  MethodSymbolizerHandle &handle = handling_methods.back();
  if (caller_frame == handle.get_caller_frame()) {
    Expression *exp;
    if (SymPersister::target(handle.get_callee_holder_name())) {
      exp = SymPersister::finish_method_helper(_handle);
    } else {
//      ShouldNotReachHere();
    }
    handling_methods.pop_back();
  }
}

MethodSymbolizer::SymMethodSet *
MethodSymbolizer::get_sym_methods(const std::string &class_name) {
  SymClassMapIt sym_class_map_it = _symbolicMethods.find(class_name);
  return sym_class_map_it != _symbolicMethods.end() ? sym_class_map_it->second
                                                    : NULL;
}

void MethodSymbolizer::invoke_method_helper(MethodSymbolizerHandle &handle) {
  int offset = handle.get_callee_local_begin_offset();
  register intptr_t *locals = handle.get_locals_ptr();

  // Currently, we do not consider "this" object
  MethodSymbolizer::prepare_param(handle, T_OBJECT, locals, offset);
  ++offset;

  ResourceMark rm;
  SignatureStream ss(handle.get_callee_method()->signature());
  while (!ss.at_return_type()) {
    offset = MethodSymbolizer::prepare_param(handle, ss.type(), locals, offset);

    ss.next();
    ++offset;
  }
  // assert(offset == handle.get_end_offset(), "equal");
}

Expression *
MethodSymbolizer::finish_method_helper(MethodSymbolizerHandle &handle) {
  BasicType type = handle.get_result_type();
  Expression *exp = NULL;
  oop obj = NULL;

  switch (type) {
    case T_VOID:
      exp = SymbolExpression::get(Sym_VOID);
      break;
    case T_OBJECT:
      obj = handle.get_result<oop>(type);
      if (obj != NULL) {
        if (!obj->is_symbolic()) {
          ConcolicMngr::ctx->symbolize(obj);
        }
        /*
          We hope only symbolize the method whose return value
          is the object we support like SymString and SymInterger.
        */
        SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(obj);
        exp = sym_inst == NULL ? NULL : sym_inst->get_ref_exp();
      } else {
        exp = SymbolExpression::get(Sym_NULL);
      }
      break;
    case T_ARRAY:
      ShouldNotCallThis();
      break;
    default:
      exp = new MethodReturnSymbolExp(type);
  }

  ConcolicMngr::record_path_condition(new MethodExpression(
      handle.get_callee_holder_name(), handle.get_callee_name(),
      handle.get_param_list(), exp, true));
  return exp;
}

int MethodSymbolizer::prepare_param(MethodSymbolizerHandle &handle,
                                    BasicType type, intptr_t *locals,
                                    int offset) {
  Expression *exp = NULL;

  if (type == T_OBJECT) {
    oop obj = *(oop *) (locals - offset);
    if (obj != NULL) {
      exp = handle.get_reference_exp(offset, obj);
      if (exp == NULL) {
        SymInstance *sym_inst =
            ConcolicMngr::ctx->get_or_alloc_sym_inst(obj);
        if (sym_inst != NULL) {
          exp = sym_inst->get_or_create_ref_exp(obj);
        }
      }
    }
  } else if (type == T_ARRAY) {
    arrayOop arrObj = *(arrayOop *) (locals - offset);
    SymArr *sym_arr = ConcolicMngr::ctx->get_or_alloc_sym_array(arrObj);
    /**
     *  TODO: May be this symbol expression can be reused
     */
    exp =
        new ArraySymbolExp(arrObj->get_sym_rid(), sym_arr->get_version(), type);
  } else {
    offset += type2size[type] - 1;

    exp = ConcolicMngr::ctx->get_stack_slot(offset);
    if (!exp) {
      switch (type) {
        case T_BYTE:
          exp = new ConExpression(*(jbyte *) (locals - offset));
          break;
        case T_CHAR:
          exp = new ConExpression(*(jchar *) (locals - offset));
          break;
        case T_DOUBLE:
          exp = new ConExpression(((VMJavaVal64 *) (locals - offset))->d);
          break;
        case T_FLOAT:
          exp = new ConExpression(*(jfloat *) (locals - offset));
          break;
        case T_INT:
          exp = new ConExpression(*(jint *) (locals - offset));
          break;
        case T_LONG:
          exp = new ConExpression(((VMJavaVal64 *) (locals - offset))->l);
          break;
        case T_SHORT:
          exp = new ConExpression(*(jshort *) (locals - offset));
          break;
        case T_BOOLEAN:
          exp = new ConExpression(*(jboolean *) (locals - offset));
          break;
        default:
          ShouldNotReachHere();
          break;
      }
    }
  }

  handle.get_param_list().push_back(exp);
  return offset;
}

void MethodSymbolizer::print() {
  tty->print_cr("symbolic methods:");
  for (SymClassMapIt sym_class_map_it = _symbolicMethods.begin();
       sym_class_map_it != _symbolicMethods.end(); ++sym_class_map_it) {
    tty->print_cr("%s", sym_class_map_it->first.c_str());
    if (sym_class_map_it->second) {
      SymMethodSet *sym_method_set = sym_class_map_it->second;
      for (SymMethodSetIt sym_method_set_it = sym_method_set->begin();
           sym_method_set_it != sym_method_set->end(); ++sym_method_set_it) {
        tty->print_cr("  %s", sym_method_set_it->c_str());
      }
    }
  }
}

void MethodSymbolizer::add_prefix_symbolic_class(const std::string class_name) {
  _classes_prefix_to_symbolize.push_back(class_name);
}

bool MethodSymbolizer::has_callback() const {
  return _has_callbacks;
}

void MethodSymbolizer::set_has_callback(bool has_callback) {
  _has_callbacks = has_callback;
}

void MethodSymbolizer::method_exit(ZeroFrame *caller_frame) {
  if (caller_frame != _handle.get_caller_frame()) {
    return;
  }

  const std::string &callee_holder_name = _handle.get_callee_holder_name();
  if (_method_exit_callback_methods.find(callee_holder_name) ==
      _method_exit_callback_methods.end()) {
    return;
  }

  _method_exit_callback_methods[callee_holder_name](_handle);
  _handle.reset();
}

void MethodSymbolizer::add_method_exit_callback(const std::string class_name,
                                                void (*method_exit_callback)(MethodSymbolizerHandle &)) {
  _method_exit_callback_methods[class_name] = method_exit_callback;
}

sym_rid_t MethodReturnSymbolExp::sym_method_count = 0;

MethodReturnSymbolExp::MethodReturnSymbolExp(BasicType type) {
  stringStream ss(str_buf, BUF_SIZE);
  _type = type2char(type);
  set_head(ss, 'M', type);
  ss.print("return%lu", sym_method_count++);
  this->finalize(ss.size());
}

#endif
