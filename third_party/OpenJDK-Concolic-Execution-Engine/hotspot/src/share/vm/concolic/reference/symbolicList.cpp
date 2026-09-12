#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicArray.hpp"
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
  set.insert("java/util/AbstractList$Itr");
  set.insert("java/util/AbstractList$ListItr");
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
  set.insert("toArray");
  set.insert("iterator");
  set.insert("listIterator");
  set.insert("hasNext");
  set.insert("next");
  set.insert("nextIndex");
  set.insert("offer");
  set.insert("poll");
  set.insert("peek");
  set.insert("element");
  return set;
}

void SymList::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->register_model(target_class_names, invoke_method_helper,
                               finish_method_helper);
}

bool SymList::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  if (ContainerSupport::claims_state(handle)) {
    // Reject cursor contracts before their bodies can throw and bypass the
    // finish hook that maintains the modeled container state.
    Method *callee = handle.get_callee_method();
    oop receiver = handle.get_param<oop>(0);
    if (callee_name == "listIterator"
        && callee->size_of_parameters() != 1) {
      ConcolicMngr::ctx->abort_symbolic_execution(
          "INDEXED_LIST_ITERATOR_OFFSET_UNSUPPORTED");
      return false;
    }
    if ((callee_name == "add" || callee_name == "set")
        && !ContainerSupport::indexed(receiver)) {
      ConcolicMngr::ctx->abort_symbolic_execution(
          "INDEXED_LIST_ITERATOR_MUTATOR_UNSUPPORTED");
      return false;
    }
  }
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    bool recording = handle.general_check_param_symbolized();
    if (recording) {
      handle.general_prepare_param();
    }
    return recording;
  }
  if (ContainerSupport::claims_state(handle)
      && !ContainerSupport::follows_callee_body(callee_name)) {
    ConcolicMngr::ctx->abort_symbolic_execution(ContainerSupport::unsupported(
        "INDEXED_OPERATION_UNSUPPORTED", handle).c_str());
  }
  return false;
}


/**
 * The array a Collection.toArray published, related to the collection it was
 * taken from.
 *
 * Both overloads promise the same elements in the same order and differ only
 * in the array they are put in.  toArray() allocates one of exactly size(),
 * and so does toArray(T[]) when the destination it was handed is too short.
 * Every slot of such an array is an element, so the array *is* the
 * collection's indexed value: it is bound to that state, and later reads of
 * the array read the collection.
 *
 * toArray(T[]) that fills the destination it was handed is the case an
 * IndexedState cannot state.  The elements stop at size(), a null is written
 * at size(), and the destination's own contents survive above that, so the
 * array agrees with the collection only up to size() -- "these elements, but
 * that many slots" is not expressible, since a state carries one size.  It
 * *is* exact when the destination has no room to spare, which is precisely
 * what `new T[c.size()]` declares and what `measures` recognises.  Any other
 * destination is named rather than approximated: falling back to the array's
 * concrete contents would discard the dependence on the collection that put
 * this call in the closure to begin with, which is the one thing the call is
 * here for.
 */
Expression *SymList::published_array(MethodSymbolizerHandle &handle,
                                     Expression *receiver,
                                     const exp_list_t &arguments) {
  if (receiver == NULL) {
    ConcolicMngr::ctx->abort_symbolic_execution(ContainerSupport::unsupported(
        "INDEXED_TO_ARRAY_RECEIVER_UNSUPPORTED", handle).c_str());
    return NULL;
  }
  if (arguments.size() > 1) {
    ConcolicMngr::ctx->abort_symbolic_execution(ContainerSupport::unsupported(
        "INDEXED_TO_ARRAY_OVERLOAD_UNSUPPORTED", handle).c_str());
    return NULL;
  }
  BasicType result_type = handle.get_result_type();
  oop published = result_type == T_ARRAY || result_type == T_OBJECT
      ? handle.get_result<oop>(result_type) : NULL;
  if (published == NULL || !published->is_array()) {
    ConcolicMngr::ctx->abort_symbolic_execution(ContainerSupport::unsupported(
        "INDEXED_TO_ARRAY_RESULT_NOT_AN_ARRAY", handle).c_str());
    return NULL;
  }
  // A destination the call did not return was too short to fill, so what
  // came back was allocated at exactly size() instead.
  oop destination = arguments.empty() ? (oop)NULL
      : handle.get_param<oop>(1);
  if (published == destination
      && ((arrayOop)destination)->length() != 0) {
    SymArr *filled =
        ConcolicMngr::ctx->find_sym_array((arrayOop)destination);
    Expression *declared = filled == NULL ? NULL : filled->get_length_exp();
    if (!ContainerSupport::measures(declared, receiver)) {
      std::string gap("INDEXED_TO_ARRAY_DESTINATION_MAY_HAVE_ROOM_TO_SPARE:");
      gap += ContainerSupport::measurement(declared, receiver);
      ConcolicMngr::ctx->abort_symbolic_execution(
          ContainerSupport::unsupported(gap.c_str(), handle).c_str());
      return NULL;
    }
  }
  ConcolicMngr::ctx->set_container_state(published, receiver);
  return ContainerSupport::concrete_value(published);
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
      || method == "toArray"
      || method == "iterator" || method == "listIterator");
  if (list_operation) {
    receiver = ConcolicMngr::ctx->container_state(
        receiver_object, "INDEXED");
  }
  if (receiver == NULL) return NULL;

  exp_list_t arguments;
  for (size_t index = 1; index < parameters.size(); ++index) {
    arguments.push_back(parameters[index]);
  }
  if (!root_container && (method == "add" || method == "set")) {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "INDEXED_LIST_ITERATOR_MUTATOR_UNSUPPORTED");
    return NULL;
  }
  if (method == "toArray") {
    return published_array(handle, root_container ? receiver : NULL,
                           arguments);
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
    int position = ConcolicMngr::ctx->next_container_removal_position(
        receiver_object);
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
  if (method == "nextIndex" && arguments.empty()) {
    Expression *result = new ConExpression((jint)
        ConcolicMngr::ctx->current_container_index(receiver_object));
    ContainerSupport::constrain_result(handle, result);
    return result;
  }
  if (method == "listIterator" && !arguments.empty()) {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "INDEXED_LIST_ITERATOR_OFFSET_UNSUPPORTED");
    return NULL;
  }
  const char *operation = method == "get"
          || method == "peek" || method == "element" ? "READ"
      : method == "contains" ? "CONTAINS"
      : method == "size" ? "SIZE"
      : method == "isEmpty" ? "IS_EMPTY"
      : method == "iterator" || method == "listIterator" ? "ITERATOR"
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
  if (method != "iterator" && method != "listIterator") {
    ContainerSupport::constrain_result(handle, result);
  }
  if (result_object != NULL) {
    ContainerSupport::attach_result(result_object, result,
        method == "iterator" || method == "listIterator"
            ? receiver_object : NULL);
  }
  return result;
}

#endif // ENABLE_CONCOLIC
