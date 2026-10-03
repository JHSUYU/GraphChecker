#ifdef ENABLE_CONCOLIC

#include "concolic/methodSymbolizer.hpp"
#include "concolic/unsafeAccess.hpp"
#include "concolic/concolicMngr.hpp"
#include "runtime/atomic.inline.hpp"
#include "concolic/exp/methodExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/reference/symbolicStringUtils.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/symbolicStream.hpp"
#include "concolic/reference/symbolicSet.hpp"
#include "concolic/reference/symbolicList.hpp"
#include "concolic/reference/symbolicBigDecimal.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicMiscObjects.h"
#include "concolic/reference/symbolicAtomic.hpp"
#include "concolic/reference/internal/symbolicUnsafe.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "memory/resourceArea.hpp"
#include "runtime/thread.hpp"
#include "runtime/signature.hpp"
#include "utilities/exceptions.hpp"
#include "utilities/ostream.hpp"

MethodSymbolizer::MethodSymbolizer() : _symbolizing_method(false) {
  init_helper_methods();
}

void MethodSymbolizer::init_helper_methods() {
  SymString::init_register_class(this);
  SymStrBuilder::init_register_class(this);
  SymStrUtils::init_register_class(this);
  SymMap::init_register_class(this);
  SymStream::init_register_class(this);
  SymSet::init_register_class(this);
  SymList::init_register_class(this);
  SymBigDecimal::init_register_class(this);
  SymbolicAtomic::init_register_class(this);
  SymbolicUnsafe::init_register_class(this);
  SymbolicMiscObjects::init_register_class(this);

  // A log statement may inspect a symbolic application value, but its
  // formatting, encoding and output are observational side effects.  Letting
  // those implementation bodies execute concolically caused one symbolic
  // keyId to generate thousands of MessageFormatter/UTF-8 array constraints
  // and eventually truncate the bounded auxiliary-PC envelope.  Suppress the
  // logging implementation as one concrete subtree; business code before and
  // after the call remains fully concolic.
  add_prefix_disabled_class("org/slf4j/");
  add_prefix_disabled_class("org/apache/log4j/");
  add_prefix_disabled_class("org/apache/commons/logging/");
  add_prefix_disabled_class("java/util/logging/");

  // A one-way function -- digest, MAC, cipher -- is a concrete subtree for
  // the same reason: no solver inverts it, so a symbolic output only grows
  // the graph.  hdfs-11741's Balancer handed a symbolic keyId to DIGEST-MD5
  // and the session cipher made every transferred block CBC constraints
  // (41 MB of expressions in one seed session).  A decision on such an
  // output (a MAC check) stays a concrete decision of the recording.  Only
  // provider packages: the mute holds for the call's whole extent, and they
  // call back into no application code (a SASL mechanism would: its
  // callback handler is the workload's).
  add_prefix_disabled_class("com/sun/crypto/provider/");
  add_prefix_disabled_class("sun/security/provider/");
}

void MethodSymbolizer::add_invoke_helper_methods(const std::string class_name,
                                                 bool (*invoke_helper_func)(MethodSymbolizerHandle &)) {
  _invoke_helper_methods[class_name] = invoke_helper_func;
}

void MethodSymbolizer::add_finish_helper_methods(const std::string class_name,
                                                 Expression *(*finish_helper_func)(MethodSymbolizerHandle &)) {
  _finish_helper_methods[class_name] = finish_helper_func;
}

void MethodSymbolizer::register_model(
    const char *const *class_names,
    bool (*invoke_helper)(MethodSymbolizerHandle &),
    Expression *(*finish_helper)(MethodSymbolizerHandle &)) {
  for (; *class_names != NULL; ++class_names) {
    const std::string class_name(*class_names);
    add_invoke_helper_methods(class_name, invoke_helper);
    add_finish_helper_methods(class_name, finish_helper);
  }
}

void MethodSymbolizer::register_model(
    const std::set<std::string> &class_names,
    bool (*invoke_helper)(MethodSymbolizerHandle &),
    Expression *(*finish_helper)(MethodSymbolizerHandle &)) {
  for (std::set<std::string>::const_iterator name = class_names.begin();
       name != class_names.end(); ++name) {
    add_invoke_helper_methods(*name, invoke_helper);
    add_finish_helper_methods(*name, finish_helper);
  }
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
  if (boxes_a_primitive(holder)) return true;
  if (_classes_prefix_to_disable.empty()) return false;
  ResourceMark rm;
  std::string holder_name(holder->as_C_string());
  return disabled_class(holder_name);
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
  BasicType basicType = primitive_target(_handle.get_callee_holder_name());
  const std::string& callee_holder_name = _handle.get_callee_holder_name();
  const bool disabled = disabled_class(callee_holder_name);

  if (disabled) {
    // Do not prepare symbolic parameters.  Merely entering the method with
    // its body muted and clearing its eventual result severs this
    // observation-only subtree from the workload expression graph.
    need_symbolize = true;
  } else if (basicType != T_ILLEGAL) {
    need_symbolize = primitive_invoke_method_helper(_handle, basicType);
  } else if (_invoke_helper_methods.find(callee_holder_name) != _invoke_helper_methods.end()) {
    need_symbolize = _invoke_helper_methods[callee_holder_name](_handle);
  }

  if (need_symbolize) {
    if (!disabled) register_functional_arguments();
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

void MethodSymbolizer::register_functional_arguments() {
  Method *callee = _handle.get_callee_method();
  ResourceMark rm;
  int offset = callee->is_static() ? 0 : 1;
  for (SignatureStream stream(callee->signature()); !stream.at_return_type();
       stream.next()) {
    const BasicType type = stream.type();
    if (type == T_OBJECT) {
      // A probe: a parameter's class is loaded, and nothing is interned.
      Symbol *name = stream.as_symbol_or_null();
      const bool functional = name != NULL
          && (name->starts_with("java/util/function/")
              || name->equals("java/util/Comparator"));
      oop argument = functional ? _handle.get_param<oop>(offset) : (oop) NULL;
      if (argument != NULL) {
        _handle.add_functional(
            ConcolicMngr::ctx->name_reference(argument));
      }
    }
    offset += type2size[type];
  }
}

// A callback frame's arguments, as its locals hold them, and the local each
// one's shadow anchors at (a two-word value at its second word).
static void callback_arguments(interpreterState istate,
                               std::vector<oop> *arguments,
                               std::vector<int> *anchors) {
  ResourceMark rm;
  int local = 1;
  for (SignatureStream stream(istate->method()->signature());
       !stream.at_return_type(); stream.next()) {
    const BasicType type = stream.type();
    arguments->push_back(type == T_OBJECT || type == T_ARRAY
        ? *(oop *)(istate->locals() - local) : (oop) NULL);
    if (anchors != NULL) anchors->push_back(local + type2size[type] - 1);
    local += type2size[type];
  }
}

bool MethodSymbolizer::enter_callback(ZeroFrame *caller_frame,
                                      ZeroFrame *callee_frame) {
  if (!_symbolizing_method || !_handle.has_functional()
      || !callee_frame->is_interpreter_frame()) {
    return false;
  }
  interpreterState istate =
      callee_frame->as_interpreter_frame()->interpreter_state();
  Method *method = istate->method();
  if (method->is_static() || method->is_native()) return false;
  oop receiver = *(oop *) istate->locals();
  if (receiver == NULL || !_handle.is_functional(receiver->get_sym_rid())) {
    return false;
  }
  if (_windows.size() >= MAX_CALLBACK_DEPTH) {
    // Declined: the callback runs muted and unlogged, so its call cannot say
    // whether it ran, nor what it answered.
    _handle.refuse_callbacks("CALLBACK_DEPTH_EXCEEDED");
    return false;
  }
  std::vector<oop> arguments;
  std::vector<int> anchors;
  callback_arguments(istate, &arguments, &anchors);
  exp_list_t seeds;
  CallbackWindow window;
  window.frame = callee_frame;
  window.key = NULL;
  window.path_start = ConcolicMngr::ctx->get_path_condition().size();
  if (_handle.seeder() != NULL) {
    _handle.seeder()(_handle, receiver->get_sym_rid(), arguments, &seeds,
                     &window.key);
  }
  _windows.push_back(window);
  _suspended.push_back(_handle);
  _handle.reset();
  _symbolizing_method = false;
  ConcolicMngr::ctx->get_shadow_stack().push_callback(callee_frame, anchors,
                                                      seeds);
  return true;
}

bool MethodSymbolizer::exit_callback(ZeroFrame *callee_frame) {
  if (_windows.empty() || _windows.back().frame != callee_frame) return false;
  CallbackResult result;
  result.key = _windows.back().key;
  const int path_start = _windows.back().path_start;
  _windows.pop_back();
  // The conditions the callback's path recorded, and their complement.
  PathCondition &path = ConcolicMngr::ctx->get_path_condition();
  bool negatable = true;
  for (int index = path_start; index < path.size(); ++index) {
    Expression *condition = path.getConds()[index]->getExp();
    if (condition == NULL) continue;
    Expression *negation = condition->logical_negation();
    negatable = negatable && negation != NULL;
    result.path = result.path == NULL ? condition
        : new OpSymExpression(result.path, condition, op_land);
    if (negatable) {
      result.path_negation = result.path_negation == NULL ? negation
          : new OpSymExpression(result.path_negation, negation, op_lor);
    }
  }
  if (!negatable) result.path_negation = NULL;
  interpreterState istate =
      callee_frame->as_interpreter_frame()->interpreter_state();
  const BasicType type = istate->method()->result_type();
  result.threw = ConcolicMngr::ctx->get_thread()->has_pending_exception();
  Expression *returned = ConcolicMngr::ctx->get_shadow_stack().pop_callback(
      callee_frame, result.threw ? T_VOID : type);
  _handle = _suspended.back();
  _suspended.pop_back();
  // A listening model names what it needs of a concrete result itself.
  const bool listened = _handle.listener() != NULL;
  oop returned_object = NULL;
  if (!result.threw && type != T_VOID) {
    // Where a returning frame leaves its result, as get_result reads it.
    intptr_t *slot = istate->stack() + 1;
    result.symbolic = returned != NULL;
    if (type == T_OBJECT || type == T_ARRAY) {
      returned_object = *(oop *) slot;
      result.returned_null = returned_object == NULL;
      result.result = returned != NULL || listened
          ? returned : ContainerSupport::concrete_value(returned_object);
    } else if (type == T_BOOLEAN || type == T_BYTE || type == T_CHAR
               || type == T_SHORT || type == T_INT) {
      result.returned_int = *(jint *) slot;
      result.result = returned != NULL || listened ? returned
          : type == T_BOOLEAN
              ? static_cast<Expression *>(
                    new ConExpression((jboolean)(result.returned_int & 1)))
              : static_cast<Expression *>(
                    new ConExpression(result.returned_int));
    } else {
      result.result = returned;
    }
  }
  _symbolizing_method = true;
  if (listened) {
    // Read as it returns: no log is kept for the call's finish.
    std::vector<oop> arguments;
    callback_arguments(istate, &arguments, NULL);
    _handle.listener()(_handle, result, returned_object, arguments);
  } else {
    _handle.callbacks().push_back(result);
  }
  return true;
}

bool MethodSymbolizer::reenters(oop container) {
  if (container == NULL) return false;
  // A suspended call's frame is still on the stack, under its callback.
  for (size_t index = 0; index < _suspended.size(); ++index) {
    if (ContainerSupport::backing_container(
            _suspended[index].get_param<oop>(0)) == container) {
      _suspended[index].mark_reentered();
      return true;
    }
  }
  return false;
}

void __attribute__((optimize("O0"))) MethodSymbolizer::finish_method(ZeroFrame *caller_frame) {
  if (caller_frame == _handle.get_caller_frame()) {
    if (ConcolicMngr::ctx->get_thread()->has_pending_exception()) {
      // Exceptional unwind has no Java result.  Reset symbolizer state only;
      // the real handler will establish the new operand-stack contents.  An
      // Unsafe write the call stated it would make (UnsafeAccess::Intent)
      // did not complete; a later write must not take it for its own.
      UnsafeAccess::clear_intent();
      // A call that mutates as its callbacks answer (removeIf, replaceAll)
      // and unwound once one had run changed its container part way: named,
      // not stated.
      if (_handle.mutates_per_callback() && !_handle.callbacks().empty()) {
        ContainerSupport::abandon_state(
            ContainerSupport::backing_container(_handle.get_param<oop>(0)),
            "CALLBACK_THREW_AFTER_MUTATION");
      }
      this->_handle.reset();
      this->set_symbolizing_method(false);
      return;
    }
    Expression *exp = NULL;
    BasicType basicType = primitive_target(_handle.get_callee_holder_name());
    const std::string& callee_holder_name = _handle.get_callee_holder_name();

    if (disabled_class(callee_holder_name) || !_handle.result_readable()) {
      // An observation sink returns a concrete value.  In particular, never
      // manufacture a MethodExpression that would reconnect a formatted log
      // string to its symbolic application argument.  A native's primitive
      // result cannot be read here (MethodSymbolizerHandle::result_readable),
      // so it is concrete too: no model mints a symbol for a word it did not
      // see.
      exp = NULL;
    } else if (basicType != T_ILLEGAL) {
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
      exp = new MethodReturnSymbolExp(handle);
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

void MethodSymbolizer::add_prefix_disabled_class(
    const std::string class_name) {
  _classes_prefix_to_disable.push_back(class_name);
}

bool MethodSymbolizer::disabled_class(const std::string &class_name) const {
  for (size_t index = 0; index < _classes_prefix_to_disable.size(); ++index) {
    const std::string &prefix = _classes_prefix_to_disable[index];
    if (class_name.size() >= prefix.size()
        && class_name.compare(0, prefix.size(), prefix) == 0) {
      return true;
    }
  }
  return false;
}

volatile intptr_t MethodReturnSymbolExp::sym_method_count = 0;

template <class T>
static SharedFieldVersions::ConcreteBits result_as(
    MethodSymbolizerHandle &handle, BasicType type) {
  return SharedFieldVersions::ConcreteBits(
      type, SharedFieldVersions::raw_bits(handle.get_result<T>(type)));
}

// The word a primitive result left, in the encoding a field's word has, so
// that a call and a read state one constant one way.
static SharedFieldVersions::ConcreteBits result_word(
    MethodSymbolizerHandle &handle, BasicType type) {
  switch (type) {
    case T_BOOLEAN: return result_as<jboolean>(handle, type);
    case T_BYTE:    return result_as<jbyte>(handle, type);
    case T_CHAR:    return result_as<jchar>(handle, type);
    case T_SHORT:   return result_as<jshort>(handle, type);
    case T_INT:     return result_as<jint>(handle, type);
    case T_LONG:    return result_as<jlong>(handle, type);
    case T_FLOAT:   return result_as<jfloat>(handle, type);
    case T_DOUBLE:  return result_as<jdouble>(handle, type);
    default:
      ShouldNotReachHere();
      return SharedFieldVersions::ConcreteBits();
  }
}

MethodReturnSymbolExp::MethodReturnSymbolExp(MethodSymbolizerHandle &handle) {
  const BasicType type = handle.get_result_type();
  char buf[BUF_SIZE];
  stringStream ss(buf, BUF_SIZE);
  _type = type2char(type);
  set_head(ss, 'M', type);
  ss.print("return%lu", (ulong) Atomic::add_ptr(
      (intptr_t) 1, &sym_method_count) - 1);
  this->finalize(buf, ss.size());
  _returned = SharedFieldVersions::returned_value(result_word(handle, type),
                                                  NULL);
  // Taken before the MethodExpression beside it consumes the list.
  ResourceMark rm;
  Method *callee = handle.get_callee_method();
  _holder = handle.get_callee_holder_name();
  _name = handle.get_callee_name();
  _descriptor = callee == NULL ? std::string()
      : std::string(callee->signature()->as_C_string());
  _arguments = handle.get_param_list();
}

void MethodReturnSymbolExp::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  SymbolExpression::serialize_internal(writer);
  _returned.serialize(writer);
  writer.Key("call");
  writer.StartObject();
  writer.Key("holder");
  writer.String(_holder.c_str());
  writer.Key("name");
  writer.String(_name.c_str());
  writer.Key("descriptor");
  writer.String(_descriptor.c_str());
  writer.Key("arguments");
  writer.StartArray();
  for (size_t index = 0; index < _arguments.size(); ++index) {
    if (_arguments[index] == NULL) {
      writer.Null();
    } else {
      // A child like any other node's: a reference into the expression
      // table under an artifact scope, the node itself otherwise.
      _arguments[index]->serialize(writer);
    }
  }
  writer.EndArray();
  writer.EndObject();
}

#endif
