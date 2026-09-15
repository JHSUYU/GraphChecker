#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicSet.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/utils.hpp"

std::set<std::string> SymSet::target_class_names = init_target_class_names();

std::set<std::string> SymSet::init_target_class_names() {
  std::set<std::string> set;
  set.insert("java/util/Set");
  set.insert("java/util/HashSet");
  set.insert("java/util/LinkedHashSet");
  return set;
}

std::set<std::string> SymSet::handle_method_names = init_handle_method_names();

std::set<std::string> SymSet::init_handle_method_names() {
  std::set<std::string> set;
  set.insert("add");
  set.insert("remove");
  set.insert("contains");
  set.insert("isEmpty");
  set.insert("clear");
  set.insert("size");
  set.insert("iterator");
  return set;
}

void SymSet::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->register_model(target_class_names, invoke_method_helper,
                               finish_method_helper);
}

bool SymSet::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    bool recording = handle.general_check_param_symbolized();
    if (recording) {
      handle.general_prepare_param();
      // Before the body runs: state what the container already holds, while
      // the receiver is still untouched by this operation.
      ContainerSupport::state_base_before_operation(handle.get_param<oop>(0));
    }
    return recording;
  }
  if (ContainerSupport::claims_state(handle)
      && !ContainerSupport::follows_callee_body(callee_name)) {
    // See the same line in symbolicMap.cpp: the abort ends this thread, the
    // mark keeps every other reader of a selected container honest.
    ContainerSupport::mark_state_gap(
        handle.get_param<oop>(0), "ASSOCIATIVE_OPERATION_UNSUPPORTED");
    ConcolicMngr::ctx->abort_symbolic_execution(ContainerSupport::unsupported(
        "ASSOCIATIVE_OPERATION_UNSUPPORTED", handle).c_str());
  }
  return false;
}

Expression *SymSet::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  exp_list_t &parameters = handle.get_param_list();
  if (parameters.empty()) return NULL;
  oop receiver_object = handle.get_param<oop>(0);
  Expression *state = ConcolicMngr::ctx->container_state(
      receiver_object, "ASSOCIATIVE");
  if (state == NULL) return NULL;
  exp_list_t arguments;
  for (size_t index = 1; index < parameters.size(); ++index) {
    arguments.push_back(parameters[index]);
  }
  if (method == "add" && arguments.size() == 1) {
    exp_list_t key;
    key.push_back(arguments[0]);
    Expression *present = new ContainerExpression(
        "ASSOCIATIVE", "CONTAINS", state, key, T_BOOLEAN);
    arguments.push_back(new ConExpression((jboolean)true));
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "PUT", state, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "ADD");
    Expression *result = new OpSymExpression(
        present, new ConExpression((jboolean)false), op_eq);
    ContainerSupport::constrain_result(handle, result);
    return result;
  }
  if (method == "remove" && arguments.size() == 1) {
    Expression *present = new ContainerExpression(
        "ASSOCIATIVE", "CONTAINS", state, arguments, T_BOOLEAN);
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "REMOVE", state, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "REMOVE");
    ContainerSupport::constrain_result(handle, present);
    return present;
  }
  if (method == "clear") {
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "CLEAR", state, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "CLEAR");
    return NULL;
  }
  const char *operation = method == "contains" ? "CONTAINS"
      : method == "size" ? "SIZE"
      : method == "isEmpty" ? "IS_EMPTY"
      : method == "iterator" ? "KEY_VIEW" : NULL;
  if (operation == NULL) return NULL;
  Expression *result = new ContainerExpression(
      "ASSOCIATIVE", operation, state, arguments,
      handle.get_result_type());
  if (method != "iterator") {
    ContainerSupport::constrain_result(handle, result);
  }
  if (handle.get_result_type() == T_OBJECT) {
    ContainerSupport::attach_result(
        handle.get_result<oop>(T_OBJECT), result,
        method == "iterator" ? receiver_object : NULL);
  }
  return result;
}

#endif // ENABLE_CONCOLIC
