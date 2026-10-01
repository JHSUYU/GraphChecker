#ifdef ENABLE_CONCOLIC

#include <concolic/exp/stringExpression.hpp>
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/methodExpression.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/utils.hpp"
#include "utilities/utf8.hpp"

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
  return map;
}

// The builder's mutators other than append.  Their bodies write the
// builder's value/count, which this model does not follow (set_sym_exp
// keeps nothing), so the builder's expression used to go stale: a setLength(0)
// left the old content's concat standing for an empty builder.  Each is now
// summarized over the builder's content -- a concat of substrings of it --
// or, where no summary is exact, the expression is dropped and the next use
// states the builder's concrete content (get_exp_of).
static bool is_mutator(const std::string &name) {
  return name == "insert" || name == "delete" || name == "deleteCharAt"
      || name == "replace" || name == "setCharAt" || name == "setLength"
      || name == "reverse" || name == "appendCodePoint";
}

// The concrete length of a builder: AbstractStringBuilder.count.
static jint builder_length(oop builder) {
  typeArrayOop value = OopUtils::java_string_to_char_array(builder);
  if (value == NULL) return -1;
  fieldDescriptor count;
  if (OopUtils::get_fd_by_name(builder, "count", "I", count) == NULL) {
    return -1;
  }
  return builder->int_field(count.offset());
}

static const char *ABSTRACT_BUILDER = "java/lang/AbstractStringBuilder";

// append(CharSequence, int, int) and append(char[], int, int): a range of
// the operand, not the operand and two renderings of its bounds.
static bool is_ranged_append(MethodSymbolizerHandle &handle) {
  if (handle.get_callee_name() != "append") return false;
  ResourceMark rm;
  SignatureStream ss(handle.get_callee_method()->signature());
  BasicType types[3];
  int count = 0;
  for (; !ss.at_return_type(); ss.next()) {
    if (count == 3) return false;
    types[count++] = ss.type();
  }
  return count == 3 && (types[0] == T_OBJECT || types[0] == T_ARRAY)
      && types[1] == T_INT && types[2] == T_INT;
}

void SymStrBuilder::init_register_class(MethodSymbolizer *m_symbolizer) {
  // AbstractStringBuilder too: setLength and setCharAt are declared only
  // there, so a call on a StringBuilder names that holder.
  const char *const classes[] = { SymStrBuilder::TYPE_NAME, ABSTRACT_BUILDER,
                                  NULL };
  m_symbolizer->register_model(classes, invoke_method_helper,
                               finish_method_helper);
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
  Method *callee = handle.get_callee_method();
  if (handle.get_callee_holder_name() == ABSTRACT_BUILDER) {
    // Only a StringBuilder's: a StringBuffer is not modeled.
    oop receiver = callee->is_static() ? (oop) NULL
        : handle.get_param<oop>(0);
    if (receiver == NULL
        || !receiver->klass()->name()->equals(SymStrBuilder::TYPE_NAME)) {
      return false;
    }
  }
  if (is_mutator(callee_name) && !callee->is_static()) {
    need_symbolize = handle.general_check_param_symbolized();
    if (need_symbolize) prepare_mutation(handle);
    return need_symbolize;
  }
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
  if (is_ranged_append(handle)) {
    // [content, what the range appends (NULL: a sequence with no
    // expression, whose text finish reads back off the builder), the
    // builder's length before]: the bounds as the int expressions they are.
    exp_list_t &params = handle.get_param_list();
    params.push_back(range_of(handle, offset,
                              handle.get_primitive_exp(offset + 1, T_INT),
                              handle.get_primitive_exp(offset + 2, T_INT)));
    params.push_back(new ConExpression(
        builder_length(handle.get_param<oop>(offset - 1))));
    return;
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
      exp = operand_exp(handle, locals_offset, obj);
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

namespace {

Expression *substring(Expression *content, Expression *begin,
                      Expression *end) {
  exp_list_t arguments;
  arguments.push_back(content);
  arguments.push_back(begin);
  if (end != NULL) arguments.push_back(end);
  return new OpStrExpression("substring", arguments);
}

Expression *concat(Expression *first, Expression *second,
                   Expression *third = NULL) {
  exp_list_t arguments;
  arguments.push_back(first);
  arguments.push_back(second);
  if (third != NULL) arguments.push_back(third);
  return new OpStrExpression("concat", arguments);
}

Expression *plus_one(Expression *index) {
  return new OpSymExpression(index, new ConExpression((jint) 1), op_add);
}

// `end` clamped to the length as Java clamps it, when both are concrete.
Expression *clamped(Expression *end, Expression *length) {
  jint at = 0;
  jint bound = 0;
  if (end->concrete_int_value(&at) && length->concrete_int_value(&bound)
      && at > bound) {
    return length;
  }
  return end;
}

}  // namespace

Expression *
SymStrBuilder::finish_method_helper(MethodSymbolizerHandle &handle) {
  BasicType type = handle.get_result_type();
  Expression *exp = NULL;
  oop result = type == T_OBJECT ? handle.get_result<oop>(type) : NULL;

  const std::string &callee_name = handle.get_callee_name();
  if (is_mutator(callee_name)) {
    exp = mutated(handle);
    oop receiver = handle.get_param<oop>(0);
    SymStrBuilder *builder = static_cast<SymStrBuilder *>(
        ConcolicMngr::ctx->get_or_alloc_sym_inst(receiver));
    if (builder != NULL) {
      builder->set_ref_exp(exp);
      if (exp == NULL) builder->clear_semantic_expression();
    }
    return type == T_VOID ? NULL : exp;
  }
  if (callee_name == "append") {
    if (is_ranged_append(handle)) {
      const exp_list_t &params = handle.get_param_list();
      exp = concat(params[0], params[1] != NULL ? params[1]
                   : appended_text(handle.get_param<oop>(0), params[2]));
    } else {
      exp_list_t string_exp_list;
      add_to_string_for_param_list(handle, string_exp_list);
      exp = new OpStrExpression("concat", string_exp_list);
    }
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

void SymStrBuilder::prepare_mutation(MethodSymbolizerHandle &handle) {
  // [content, argument..., length before the call]: indices as the int
  // expressions they are, a value as the String append would make of it.
  exp_list_t &params = handle.get_param_list();
  oop receiver = handle.get_param<oop>(0);
  params.push_back(get_exp_of(receiver));
  Method *callee = handle.get_callee_method();
  ResourceMark rm;
  SignatureStream ss(callee->signature());
  int offset = 1;
  bool summarizable = true;
  // Leading positions: delete and replace take two, the others one.
  const std::string &name = handle.get_callee_name();
  const int positions = name == "delete" || name == "replace" ? 2 : 1;
  for (int index = 0; !ss.at_return_type(); ss.next(), ++index) {
    const BasicType type = ss.type();
    Expression *exp = NULL;
    if (type == T_INT && index < positions) {
      exp = handle.get_primitive_exp(offset, T_INT);
    } else if (is_java_primitive(type)) {
      exp = OpStrExpression::to_string(handle.get_primitive_exp(offset, type));
    } else if (type == T_OBJECT) {
      oop value = handle.get_param<oop>(offset);
      if (value == NULL) {
        exp = new ConStringSymbolExp(std::string("null"));
      } else if (value->klass()->name()->equals(SymString::TYPE_NAME)
                 || value->klass()->name()->equals(SymStrBuilder::TYPE_NAME)) {
        exp = operand_exp(handle, offset, value);
      }
    }
    if (exp == NULL) summarizable = false;
    params.push_back(exp);
    offset += type2size[type];
  }
  const jint length = builder_length(receiver);
  params.push_back(summarizable && length >= 0
                       ? new ConExpression(length) : (Expression *) NULL);
}


Expression *SymStrBuilder::range_of(MethodSymbolizerHandle &handle,
                                    int offset, Expression *start,
                                    Expression *end) {
  oop sequence = handle.get_param<oop>(offset);
  if (sequence == NULL) {
    return substring(new ConStringSymbolExp(std::string("null")), start, end);
  }
  if (sequence->is_instance()
      && (sequence->klass()->name()->equals(SymString::TYPE_NAME)
          || sequence->klass()->name()->equals(SymStrBuilder::TYPE_NAME))) {
    return substring(operand_exp(handle, offset, sequence), start, end);
  }
  // A char[] or another CharSequence: no String operation states its range.
  // With an expression of its own the range is a named operation over it;
  // without one it is the text it appended (NULL here: finish reads it).
  Expression *shadow = NULL;
  if (sequence->is_array()) {
    // Only an array that already has a state or an expression: asking for
    // its state would make one for any array.
    SymArr *array = ConcolicMngr::ctx->find_sym_array(arrayOop(sequence));
    shadow = ConcolicMngr::ctx->find_container_state(sequence);
    if (shadow == NULL && array != NULL && array->has_semantic_expression()) {
      shadow = ConcolicMngr::ctx->container_state(sequence, "INDEXED");
    }
  } else {
    SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(sequence);
    if (instance != NULL && instance->has_semantic_expression()) {
      shadow = instance->get_ref_exp();
    }
  }
  if (shadow == NULL) return NULL;
  exp_list_t arguments;
  arguments.push_back(shadow);
  arguments.push_back(start);
  arguments.push_back(end);
  return new OpStrExpression(sequence->is_array()
                                 ? "unsupportedCharArrayRange"
                                 : "unsupportedCharSequenceRange",
                             arguments);
}

Expression *SymStrBuilder::appended_text(oop builder, Expression *before) {
  jint from = 0;
  typeArrayOop value = OopUtils::java_string_to_char_array(builder);
  const jint to = builder_length(builder);
  if (value == NULL || to < 0 || !before->concrete_int_value(&from)
      || from < 0 || from > to) {
    return new OpStrExpression("unsupportedCharSequenceRange",
                               (Expression *) new ConExpression(to));
  }
  ResourceMark rm;
  const std::string text(UNICODE::as_utf8(value->char_at_addr(from),
                                          to - from));
  if (!ConStringSymbolExp::fits(text)) {
    // A constant past the symbol-name bound would be cut: named instead.
    return new OpStrExpression("unsupportedCharSequenceRange",
                               (Expression *) new ConExpression(to - from));
  }
  return new ConStringSymbolExp(text);
}

Expression *SymStrBuilder::mutated(MethodSymbolizerHandle &handle) {
  const exp_list_t &params = handle.get_param_list();
  const std::string &name = handle.get_callee_name();
  if (params.size() < 2 || params.back() == NULL) return NULL;
  Expression *content = params[0];
  Expression *length = params.back();
  const size_t arguments = params.size() - 2;
  if (name == "setLength" && arguments == 1) {
    jint to = 0;
    jint from = 0;
    // Shorter: a prefix.  Longer pads with '\0', which no summary states.
    if (params[1]->concrete_int_value(&to) && to == 0) {
      return new ConStringSymbolExp(std::string());
    }
    if (params[1]->concrete_int_value(&to)
        && length->concrete_int_value(&from) && to <= from) {
      return substring(content, new ConExpression((jint) 0), params[1]);
    }
    return NULL;
  }
  if (name == "delete" && arguments == 2) {
    return concat(substring(content, new ConExpression((jint) 0), params[1]),
                  substring(content, clamped(params[2], length), NULL));
  }
  if (name == "deleteCharAt" && arguments == 1) {
    return concat(substring(content, new ConExpression((jint) 0), params[1]),
                  substring(content, plus_one(params[1]), NULL));
  }
  if (name == "insert" && arguments == 2) {
    return concat(substring(content, new ConExpression((jint) 0), params[1]),
                  params[2], substring(content, params[1], NULL));
  }
  if (name == "replace" && arguments == 3) {
    return concat(substring(content, new ConExpression((jint) 0), params[1]),
                  params[3],
                  substring(content, clamped(params[2], length), NULL));
  }
  if (name == "setCharAt" && arguments == 2) {
    return concat(substring(content, new ConExpression((jint) 0), params[1]),
                  params[2], substring(content, plus_one(params[1]), NULL));
  }
  return NULL;
}

Expression *SymStrBuilder::operand_exp(MethodSymbolizerHandle &handle,
                                       int locals_offset, oop obj) {
  // The operand slot's own shadow first: an interned String carries its
  // value on the slot only, never on the JVM-wide object, so asking the
  // object alone read a symbolic literal as its concrete content.
  Expression *slot = ConcolicMngr::ctx->find_stack_slot(
      handle.get_caller_stack_begin_offset() + locals_offset);
  return slot != NULL ? slot : get_exp_of(obj);
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
