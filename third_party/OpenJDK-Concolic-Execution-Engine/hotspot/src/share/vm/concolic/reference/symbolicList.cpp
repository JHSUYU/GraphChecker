#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicList.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/utils.hpp"

std::set<std::string> SymList::target_class_names = init_target_class_names();

std::set<std::string> SymList::init_target_class_names() {
  std::set<std::string> set;
  set.insert("java/util/List");
  set.insert("java/util/Queue");
  set.insert("java/util/Deque");
  set.insert("java/util/ArrayList");
  set.insert("java/util/AbstractList");
  set.insert("java/util/ArrayList$Itr");
  set.insert("java/util/ArrayList$ListItr");
  set.insert("java/util/ArrayDeque");
  set.insert("java/util/ArrayDeque$DeqIterator");
  return set;
}

std::set<std::string> SymList::handle_method_names = init_handle_method_names();

std::set<std::string> SymList::init_handle_method_names() {
  std::set<std::string> set;
  set.insert("add");
  set.insert("set");
  set.insert("get");
  set.insert("remove");
  set.insert("contains");
  set.insert("isEmpty");
  set.insert("clear");
  set.insert("size");
  set.insert("iterator");
  set.insert("hasNext");
  set.insert("next");
  set.insert("offer");
  set.insert("poll");
  set.insert("peek");
  set.insert("element");
  return set;
}

void SymList::init_register_class(MethodSymbolizer *m_symbolizer) {
  for(std::set<std::string>::iterator it = target_class_names.begin(); it != target_class_names.end(); it++) {
    m_symbolizer->add_invoke_helper_methods(*it, invoke_method_helper);
    m_symbolizer->add_finish_helper_methods(*it, finish_method_helper);
  }
}

bool SymList::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    bool recording = handle.general_check_param_symbolized();
    if (recording) {
      handle.general_prepare_param();
    }
    return recording;
  }
  if (handle.general_check_param_symbolized()) {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "INDEXED_OPERATION_UNSUPPORTED");
  }
  return false;
}


Expression *SymList::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  exp_list_t &parameters = handle.get_param_list();
  if (parameters.empty()) return NULL;
  oop receiver_object = handle.get_param<oop>(0);
  Expression *receiver = parameters[0];
  bool root_container = ContainerSupport::indexed(receiver_object);
  bool list_operation = root_container && (method == "add"
      || method == "offer"
      || method == "poll" || method == "peek" || method == "element"
      || method == "set"
      || method == "get" || method == "remove"
      || method == "contains" || method == "isEmpty"
      || method == "clear" || method == "size"
      || method == "iterator");
  if (list_operation) {
    receiver = ConcolicMngr::ctx->container_state(
        receiver_object, "INDEXED");
  }
  if (receiver == NULL) return NULL;

  exp_list_t arguments;
  for (size_t index = 1; index < parameters.size(); ++index) {
    arguments.push_back(parameters[index]);
  }
  if ((method == "add" || method == "offer") && root_container) {
    const char *operation = arguments.size() == 1 ? "APPEND" : "INSERT";
    if (arguments.size() == 2) {
      ContainerSupport::constrain_position(
          "INDEXED", receiver, arguments[0], true);
    }
    Expression *next = new ContainerExpression(
        "INDEXED", operation, receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    return handle.get_result_type() == T_BOOLEAN
        ? (Expression *)new ConExpression((jboolean)true) : NULL;
  }
  if (method == "set" && root_container && arguments.size() == 2) {
    ContainerSupport::constrain_position(
        "INDEXED", receiver, arguments[0]);
    exp_list_t index;
    index.push_back(arguments[0]);
    oop result_object = handle.get_result_type() == T_OBJECT
        ? handle.get_result<oop>(T_OBJECT) : NULL;
    Expression *old = new ContainerExpression(
        "INDEXED", "READ", receiver, index,
        ContainerSupport::result_type(
            result_object, handle.get_result_type()),
        ContainerSupport::java_type(
            result_object, handle.get_result_type()));
    ContainerSupport::constrain_result(handle, old);
    ContainerSupport::attach_result(result_object, old);
    Expression *next = new ContainerExpression(
        "INDEXED", "WRITE", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    return old;
  }
  if (method == "remove" && root_container && arguments.size() == 1) {
    ResourceMark rm;
    const char *signature =
        handle.get_callee_method()->signature()->as_C_string();
    if (signature != NULL && signature[0] == '(' && signature[1] == 'I') {
      ContainerSupport::constrain_position(
          "INDEXED", receiver, arguments[0]);
      oop result_object = handle.get_result_type() == T_OBJECT
          ? handle.get_result<oop>(T_OBJECT) : NULL;
      Expression *old = new ContainerExpression(
          "INDEXED", "READ", receiver, arguments,
          ContainerSupport::result_type(
              result_object, handle.get_result_type()),
          ContainerSupport::java_type(
              result_object, handle.get_result_type()));
      ContainerSupport::constrain_result(handle, old);
      ContainerSupport::attach_result(result_object, old);
      Expression *next = new ContainerExpression(
          "INDEXED", "REMOVE", receiver, arguments);
      ConcolicMngr::ctx->set_container_state(receiver_object, next);
      return old;
    }
    ConcolicMngr::ctx->abort_symbolic_execution(
        "INDEXED_REMOVE_OBJECT_UNSUPPORTED");
    return NULL;
  }
  if (root_container && (method == "poll"
      || (method == "remove" && arguments.empty()))) {
    oop result_object = handle.get_result_type() == T_OBJECT
        ? handle.get_result<oop>(T_OBJECT) : NULL;
    if (method == "poll" && result_object == NULL) {
      exp_list_t no_arguments;
      ConcolicMngr::record_path_condition(new ContainerExpression(
          "INDEXED", "IS_EMPTY", receiver, no_arguments, T_BOOLEAN));
      return SymbolExpression::get(Sym_NULL);
    }
    exp_list_t first;
    first.push_back(new ConExpression((jint)0));
    ContainerSupport::constrain_position(
        "INDEXED", receiver, first[0]);
    Expression *old = new ContainerExpression(
        "INDEXED", "READ", receiver, first,
        ContainerSupport::result_type(
            result_object, handle.get_result_type()),
        ContainerSupport::java_type(
            result_object, handle.get_result_type()));
    ContainerSupport::constrain_result(handle, old);
    ContainerSupport::attach_result(result_object, old);
    Expression *next = new ContainerExpression(
        "INDEXED", "REMOVE", receiver, first);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    return old;
  }
  if (method == "clear" && root_container) {
    Expression *next = new ContainerExpression(
        "INDEXED", "CLEAR", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    return NULL;
  }
  if (method == "remove" && !root_container && arguments.empty()) {
    int position =
        ConcolicMngr::ctx->current_container_position(receiver_object) - 1;
    Expression *root = ConcolicMngr::ctx->container_state(
        receiver_object, "INDEXED");
    if (root == NULL || position < 0) {
      ConcolicMngr::ctx->abort_symbolic_execution(
          "INDEXED_ITERATOR_REMOVE_WITHOUT_NEXT");
      return NULL;
    }
    exp_list_t remove_arguments;
    remove_arguments.push_back(new ConExpression((jint)position));
    Expression *next = new ContainerExpression(
        "INDEXED", "REMOVE", root, remove_arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ConcolicMngr::ctx->rewind_container_position(receiver_object);
    return NULL;
  }

  if ((method == "peek" || method == "element")
      && arguments.empty()) {
    if (method == "peek" && handle.get_result_type() == T_OBJECT
        && handle.get_result<oop>(T_OBJECT) == NULL) {
      exp_list_t no_arguments;
      ConcolicMngr::record_path_condition(new ContainerExpression(
          "INDEXED", "IS_EMPTY", receiver, no_arguments, T_BOOLEAN));
      return SymbolExpression::get(Sym_NULL);
    }
    arguments.push_back(new ConExpression((jint)0));
    ContainerSupport::constrain_position(
        "INDEXED", receiver, arguments[0]);
  }
  if (method == "remove" && !root_container) {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "ITERATOR_REMOVE_UNSUPPORTED");
    return NULL;
  }
  if (method == "hasNext" && arguments.empty()) {
    arguments.push_back(new ConExpression((jint)
        ConcolicMngr::ctx->current_container_position(receiver_object)));
    Expression *result = new ContainerExpression(
        "INDEXED", "HAS_NEXT", receiver, arguments, T_BOOLEAN);
    ContainerSupport::constrain_result(handle, result);
    return result;
  }
  const char *operation = method == "get"
          || method == "peek" || method == "element" ? "READ"
      : method == "contains" ? "CONTAINS"
      : method == "size" ? "SIZE"
      : method == "isEmpty" ? "IS_EMPTY"
      : method == "iterator" ? "ITERATOR"
      : method == "next" ? "NEXT" : NULL;
  if (operation == NULL) return NULL;
  if (method == "next") {
    arguments.clear();
    arguments.push_back(new ConExpression(
        ConcolicMngr::ctx->next_container_position(receiver_object)));
    ContainerSupport::constrain_position(
        "INDEXED", receiver, arguments[0]);
  } else if (method == "get" && arguments.size() == 1) {
    ContainerSupport::constrain_position(
        "INDEXED", receiver, arguments[0]);
  }
  oop result_object = handle.get_result_type() == T_OBJECT
      ? handle.get_result<oop>(T_OBJECT) : NULL;
  BasicType result_type = ContainerSupport::result_type(
      result_object, handle.get_result_type());
  Expression *result = new ContainerExpression(
      "INDEXED", operation, receiver, arguments, result_type,
      ContainerSupport::java_type(result_object,
                                  handle.get_result_type()));
  if (method != "iterator") {
    ContainerSupport::constrain_result(handle, result);
  }
  if (result_object != NULL) {
    ContainerSupport::attach_result(result_object, result,
        method == "iterator" ? receiver_object : NULL);
  }
  return result;
}

#endif // ENABLE_CONCOLIC
