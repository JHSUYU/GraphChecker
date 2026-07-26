#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/utils.hpp"

static bool is_root_map(oop receiver) {
  if (receiver == NULL || receiver->klass() == NULL
      || receiver->klass()->name() == NULL) return false;
  Symbol *name = receiver->klass()->name();
  return name->equals("java/util/HashMap")
      || name->equals("java/util/LinkedHashMap")
      || name->equals("java/util/Hashtable")
      || name->equals("java/util/concurrent/ConcurrentHashMap")
      || name->equals(
          "org/hibernate/internal/util/collections/"
          "ConcurrentReferenceHashMap");
}

static bool is_scalar_map_iterator(oop receiver) {
  if (receiver == NULL || receiver->klass() == NULL
      || receiver->klass()->name() == NULL) return false;
  Symbol *name = receiver->klass()->name();
  return name->equals("java/util/HashMap$KeyIterator")
      || name->equals("java/util/HashMap$ValueIterator")
      || name->equals("java/util/LinkedHashMap$LinkedKeyIterator")
      || name->equals("java/util/LinkedHashMap$LinkedValueIterator");
}

std::set<std::string> SymMap::target_class_names = init_target_class_names();

std::set<std::string> SymMap::init_target_class_names() {
  std::set<std::string> set;
  set.insert("java/util/HashMap");
  set.insert("java/util/LinkedHashMap");
  set.insert("org/hibernate/internal/util/collections/ConcurrentReferenceHashMap");
  set.insert("java/util/Hashtable");
  set.insert("java/util/concurrent/ConcurrentHashMap");
  set.insert("java/util/HashMap$EntrySet");
  set.insert("java/util/HashMap$KeySet");
  set.insert("java/util/HashMap$Values");
  set.insert("java/util/HashMap$EntryIterator");
  set.insert("java/util/HashMap$KeyIterator");
  set.insert("java/util/HashMap$ValueIterator");
  set.insert("java/util/HashMap$Node");
  set.insert("java/util/LinkedHashMap$LinkedEntrySet");
  set.insert("java/util/LinkedHashMap$LinkedKeySet");
  set.insert("java/util/LinkedHashMap$LinkedValues");
  set.insert("java/util/LinkedHashMap$LinkedEntryIterator");
  set.insert("java/util/LinkedHashMap$LinkedKeyIterator");
  set.insert("java/util/LinkedHashMap$LinkedValueIterator");
  set.insert("java/util/LinkedHashMap$Entry");
  return set;
}

std::set<std::string> SymMap::handle_method_names = init_handle_method_names();

std::set<std::string> SymMap::init_handle_method_names() {
  std::set<std::string> set;
  set.insert("put");
  set.insert("get");
  set.insert("remove");
  set.insert("containsKey");
  set.insert("isEmpty");
  set.insert("clear");
  set.insert("size");
  set.insert("entrySet");
  set.insert("keySet");
  set.insert("values");
  set.insert("iterator");
  set.insert("next");
  set.insert("getKey");
  set.insert("getValue");
  set.insert("putAll");
  set.insert("putIfAbsent");
  set.insert("replace");
  set.insert("replaceAll");
  set.insert("compute");
  set.insert("computeIfAbsent");
  set.insert("computeIfPresent");
  set.insert("merge");
  return set;
}

std::map<std::string, bool> SymMap::skip_method_names = init_skip_method_names();

std::map<std::string, bool> SymMap::init_skip_method_names() {
  std::map<std::string, bool> map;
  map["<init>"] = true; //really??
  map["hash"] = true;
  map["forEach"] = false; // really?
  return map;
}

void SymMap::init_register_class(MethodSymbolizer *m_symbolizer) {
  for(std::set<std::string>::iterator it = target_class_names.begin(); it != target_class_names.end(); it++) {
    m_symbolizer->add_invoke_helper_methods(*it, invoke_method_helper);
    m_symbolizer->add_finish_helper_methods(*it, finish_method_helper);
  }
}

bool SymMap::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  bool need_symbolize = true;
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    // Treat public Map operations as semantic boundaries.  Besides lookups,
    // mutators must be recorded so producer regions can export relational
    // heap summaries such as M' = put(M, key, value).
    bool recording = handle.general_check_param_symbolized();
    if (recording) {
      handle.general_prepare_param();
    }
  } else {
    std::map<std::string, bool>::iterator iter = skip_method_names.find(callee_name);
    if (iter != skip_method_names.end()) {
      need_symbolize = iter->second;
    }
  }

  return need_symbolize;
}

Expression *SymMap::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  exp_list_t &parameters = handle.get_param_list();
  if (parameters.empty()) return NULL;
  if (method == "putAll" || method == "putIfAbsent"
      || method == "replace" || method == "replaceAll"
      || method == "compute" || method == "computeIfAbsent"
      || method == "computeIfPresent" || method == "merge") {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "ASSOCIATIVE_MUTATOR_UNSUPPORTED");
    return NULL;
  }

  oop receiver_object = handle.get_param<oop>(0);
  Expression *receiver = parameters[0];
  bool root_map = is_root_map(receiver_object);
  bool map_operation = root_map && (method == "get"
      || method == "containsKey"
      || method == "size" || method == "isEmpty"
      || method == "put"
      || method == "remove" || method == "clear"
      || method == "entrySet" || method == "keySet"
      || method == "values");
  if (map_operation) {
    receiver = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
  }
  if (receiver == NULL) return NULL;

  exp_list_t arguments;
  for (size_t index = 1; index < parameters.size(); ++index) {
    arguments.push_back(parameters[index]);
  }

  const char *operation = NULL;
  if (method == "get") operation = "READ";
  else if (method == "containsKey") operation = "CONTAINS";
  else if (method == "size") operation = "SIZE";
  else if (method == "isEmpty") operation = "IS_EMPTY";
  else if (method == "entrySet") operation = "ENTRY_VIEW";
  else if (method == "keySet") operation = "KEY_VIEW";
  else if (method == "values") operation = "VALUE_VIEW";
  else if (method == "iterator") operation = "ITERATOR";
  else if (method == "next") {
    operation = "NEXT";
    arguments.clear();
    arguments.push_back(new ConExpression(
        ConcolicMngr::ctx->next_container_position(receiver_object)));
    ContainerSupport::constrain_position(
        "ASSOCIATIVE", receiver, arguments[0]);
  } else if (method == "getKey") operation = "KEY";
  else if (method == "getValue") operation = "VALUE";

  if (method == "put" && root_map && arguments.size() == 2) {
    Expression *old_state = receiver;
    Expression *new_state = new ContainerExpression(
        "ASSOCIATIVE", "PUT", old_state, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, new_state);
    if (!arguments.empty()) {
      exp_list_t key;
      key.push_back(arguments[0]);
      oop result = handle.get_result_type() == T_OBJECT
          ? handle.get_result<oop>(T_OBJECT) : NULL;
      Expression *old = new ContainerExpression(
          "ASSOCIATIVE", "READ", old_state, key,
          ContainerSupport::result_type(result,
                                        handle.get_result_type()),
          ContainerSupport::java_type(result,
                                      handle.get_result_type()));
      ContainerSupport::constrain_result(handle, old);
      return old;
    }
    return NULL;
  }
  if (method == "remove" && root_map && arguments.size() == 1) {
    Expression *old = new ContainerExpression(
        "ASSOCIATIVE", "READ", receiver, arguments,
        ContainerSupport::result_type(
            handle.get_result_type() == T_OBJECT
                ? handle.get_result<oop>(T_OBJECT) : NULL,
            handle.get_result_type()),
        ContainerSupport::java_type(
            handle.get_result_type() == T_OBJECT
                ? handle.get_result<oop>(T_OBJECT) : NULL,
            handle.get_result_type()));
    ContainerSupport::constrain_result(handle, old);
    Expression *new_state = new ContainerExpression(
        "ASSOCIATIVE", "REMOVE", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, new_state);
    return old;
  }
  if (method == "clear" && root_map && arguments.empty()) {
    Expression *new_state = new ContainerExpression(
        "ASSOCIATIVE", "CLEAR", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, new_state);
    return NULL;
  }
  if (method == "remove" && (!root_map || arguments.size() != 1)) {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "ASSOCIATIVE_REMOVE_OVERLOAD_UNSUPPORTED");
    return NULL;
  }
  if (method == "clear" && !root_map) {
    ConcolicMngr::ctx->abort_symbolic_execution(
        "ASSOCIATIVE_VIEW_CLEAR_UNSUPPORTED");
    return NULL;
  }
  if (operation == NULL) return NULL;

  BasicType expression_type = handle.get_result_type();
  oop result_object = NULL;
  if (expression_type == T_OBJECT) {
    result_object = handle.get_result<oop>(T_OBJECT);
    expression_type = ContainerSupport::result_type(
        result_object, expression_type);
  }
  Expression *result = new ContainerExpression(
      "ASSOCIATIVE", operation, receiver, arguments,
      expression_type,
      ContainerSupport::java_type(result_object,
                                  handle.get_result_type()));
  if (method == "get" || method == "containsKey"
      || method == "size" || method == "isEmpty"
      || method == "next" && is_scalar_map_iterator(receiver_object)) {
    ContainerSupport::constrain_result(handle, result);
  }
  if ((method == "getKey" || method == "getValue")
      && result_object != NULL) {
    exp_list_t observation_arguments;
    observation_arguments.push_back(
        ContainerSupport::concrete_value(result_object));
    ConcolicMngr::record_path_condition(new ContainerExpression(
        "ASSOCIATIVE",
        method == "getKey" ? "OBSERVE_KEY" : "OBSERVE_VALUE",
        receiver, observation_arguments, T_BOOLEAN));
  }
  if (handle.get_result_type() == T_OBJECT) {
    if (result_object != NULL) {
      ContainerSupport::attach_result(result_object, result);
    }
  }
  return result;
}

#endif // ENABLE_CONCOLIC
