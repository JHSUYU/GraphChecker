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
  set.insert("java/util/concurrent/ConcurrentHashMap$KeySetView");
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
    // A symbolic value admits the model, and so does a mutation this thread
    // is performing because of a symbolic decision: see
    // ContainerSupport::guarded_mutation.
    bool recording = handle.general_check_param_symbolized()
        || ContainerSupport::guarded_mutation(callee_name);
    if (recording && ContainerSupport::reenters_from_callback(
            ContainerSupport::backing_container(handle.get_param<oop>(0)),
            callee_name)) {
      return false;
    }
    if (recording) {
      handle.general_prepare_param();
      // Before the body runs: state what the container already holds, while
      // the receiver is still untouched by this operation.  A KeySetView is
      // its map (canonicalize), so the base is the map's.
      ContainerSupport::state_base_before_operation(
          ContainerSupport::canonicalize(handle.get_param<oop>(0)));
    }
    return recording;
  }
  if (ContainerSupport::claims_state(handle)
      && !ContainerSupport::follows_callee_body(callee_name)) {
    // See the same line in symbolicMap.cpp: the set leaves the model, and the
    // mark keeps every other reader of a selected container honest.
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
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
    // add answers whether the member was absent, and puts it only there: a
    // hash set's member maps to true, a KeySetView's to its map value, and
    // putIfAbsent keeps the value a member already maps to.  So the PUT is
    // guarded by that absence, which a flip of the state flips; one that
    // did not fire is the thread's state, no version.
    exp_list_t key;
    key.push_back(arguments[0]);
    Expression *present = new ContainerExpression(
        "ASSOCIATIVE", "CONTAINS", state, key, T_BOOLEAN);
    const bool added = (handle.get_result<jint>(T_BOOLEAN) & 1) != 0;
    ContainerSupport::state_answer(present, !added);
    Expression *absent = ContainerSupport::negation(present);
    oop mapped = ContainerSupport::capability(receiver_object)
        == ContainerSupport::CAPABILITY_HASH_SET ? (oop) NULL
        : OopUtils::obj_field_by_name(receiver_object, "value",
                                      "Ljava/lang/Object;");
    arguments.push_back(mapped == NULL
        ? static_cast<Expression *>(new ConExpression((jboolean)true))
        : ContainerSupport::concrete_value(mapped));
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "PUT_IF", state, arguments, T_OBJECT, std::string(),
        absent);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    if (added) ContainerSupport::publish_state(receiver_object, next, "ADD");
    return absent;
  }
  if (method == "remove" && arguments.size() == 1) {
    Expression *present = new ContainerExpression(
        "ASSOCIATIVE", "CONTAINS", state, arguments, T_BOOLEAN);
    ContainerSupport::state_result(handle, present);
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "REMOVE", state, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "REMOVE");
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
  // A KeySetView's query is its map's, bound to the map's version as every
  // map query is.
  Expression *result = NULL;
  if (method != "iterator" && ContainerSupport::capability(receiver_object)
                                  != ContainerSupport::CAPABILITY_HASH_SET) {
    result = ContainerSupport::query_state(
        receiver_object, "ASSOCIATIVE", operation, arguments,
        handle.get_result_type(),
        std::string(1, type2char(handle.get_result_type())),
        ContainerSupport::receiver_owner(parameters[0])).expression;
  }
  if (result == NULL) {
    result = new ContainerExpression(
        "ASSOCIATIVE", operation, state, arguments,
        handle.get_result_type());
    if (method != "iterator") {
      ContainerSupport::state_result(handle, result);
    }
  }
  if (handle.get_result_type() == T_OBJECT) {
    ContainerSupport::attach_result(
        handle.get_result<oop>(T_OBJECT), result,
        method == "iterator" ? receiver_object : NULL);
  }
  return result;
}

#endif // ENABLE_CONCOLIC
