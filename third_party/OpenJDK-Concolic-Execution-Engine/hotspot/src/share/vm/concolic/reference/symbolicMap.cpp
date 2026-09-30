#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/utils.hpp"

#include <string.h>

namespace {

bool klass_is_one_of(oop receiver, const char *const *names) {
  if (receiver == NULL || receiver->klass() == NULL
      || receiver->klass()->name() == NULL) {
    return false;
  }
  Symbol *name = receiver->klass()->name();
  for (; *names != NULL; ++names) {
    if (name->equals(*names, (int) strlen(*names))) return true;
  }
  return false;
}

// Iterators whose next() yields a key or a value.
const char *const SCALAR_ITERATORS[] = {
  "java/util/HashMap$KeyIterator", "java/util/HashMap$ValueIterator",
  "java/util/LinkedHashMap$LinkedKeyIterator",
  "java/util/LinkedHashMap$LinkedValueIterator",
  "java/util/concurrent/ConcurrentHashMap$KeyIterator",
  "java/util/concurrent/ConcurrentHashMap$ValueIterator", NULL
};
// Iterators whose next() yields the map *key*, so the element it returns is
// exactly the removed key a conditional removal must name.  A value iterator
// is deliberately excluded: it never surfaces the key.
const char *const KEY_ITERATORS[] = {
  "java/util/HashMap$KeyIterator", "java/util/LinkedHashMap$LinkedKeyIterator",
  "java/util/concurrent/ConcurrentHashMap$KeyIterator", NULL
};
// Iterators whose next() yields a Map.Entry.  A loop may read the value but
// never the key, so the removed key is recovered from the returned entry.
const char *const ENTRY_ITERATORS[] = {
  "java/util/HashMap$EntryIterator",
  "java/util/LinkedHashMap$LinkedEntryIterator",
  "java/util/concurrent/ConcurrentHashMap$EntryIterator", NULL
};
// The views whose elements are keys, entries or values.
const char *const KEY_VIEWS[] = {
  "java/util/HashMap$KeySet", "java/util/LinkedHashMap$LinkedKeySet",
  "java/util/concurrent/ConcurrentHashMap$KeySetView",
  "java/util/Hashtable$KeySet", NULL
};
const char *const ENTRY_VIEWS[] = {
  "java/util/HashMap$EntrySet", "java/util/LinkedHashMap$LinkedEntrySet",
  "java/util/concurrent/ConcurrentHashMap$EntrySetView",
  "java/util/Hashtable$EntrySet", NULL
};
const char *const VALUE_VIEWS[] = {
  "java/util/HashMap$Values", "java/util/LinkedHashMap$LinkedValues",
  "java/util/concurrent/ConcurrentHashMap$ValuesView",
  "java/util/Hashtable$ValueCollection", NULL
};

bool map_capability(ContainerSupport::Capability capability) {
  return capability == ContainerSupport::CAPABILITY_HASH_MAP
      || capability == ContainerSupport::CAPABILITY_CONCURRENT_MAP
      || capability == ContainerSupport::CAPABILITY_HASHTABLE;
}

// The calls whose functional argument the muted body calls back
// (MethodSymbolizer::enter_callback).
bool takes_callback(const std::string &method) {
  return method == "computeIfAbsent" || method == "computeIfPresent"
      || method == "compute" || method == "merge" || method == "forEach"
      || method == "replaceAll" || method == "removeIf";
}

// Calls on a map itself, as opposed to its entries and iterators: a
// receiver that is no modeled map runs them as bytecode.
bool map_level(const std::string &method) {
  return method != "getKey" && method != "getValue" && method != "hasNext"
      && method != "next" && method != "iterator"
      && !(method == "remove" || method == "clear" || method == "size"
           || method == "isEmpty");
}

// What names one key: the expression the key object carries, else its
// concrete identity or value.  Wrapping NEXT in KEY instead would repeat the
// iterator's whole input map in every REMOVE_IF and make successive passes
// grow the state exponentially.
Expression *key_expression(oop key_object) {
  Expression *carried = ContainerSupport::semantic_value(key_object);
  return carried != NULL ? carried
                         : ContainerSupport::concrete_value(key_object);
}

Expression *iterated_entry_key(oop cursor, oop result_object,
                               Expression *next) {
  if (next == NULL) return NULL;
  oop key_object = NULL;
  if (klass_is_one_of(cursor, KEY_ITERATORS)) {
    key_object = result_object;
  } else if (klass_is_one_of(cursor, ENTRY_ITERATORS)
             && result_object != NULL) {
    key_object = OopUtils::key_of_map_node(result_object);
  } else {
    return NULL;
  }
  return key_expression(key_object);
}

// A container relation of one map state.
Expression *relation(const char *operation, Expression *state,
                     const exp_list_t &arguments, Expression *owner,
                     BasicType type = T_OBJECT,
                     const std::string &java_type = std::string(),
                     Expression *guard = NULL) {
  return new ContainerExpression("ASSOCIATIVE", operation, state, arguments,
                                 type, java_type, guard, owner);
}

Expression *read_of(Expression *state, Expression *key, Expression *owner,
                    oop value = NULL) {
  exp_list_t arguments;
  arguments.push_back(key);
  return relation("READ", state, arguments, owner,
                  ContainerSupport::result_type(value, T_OBJECT),
                  ContainerSupport::java_type(value, T_OBJECT));
}

// Records `READ(state, key) != null` (present) or `== null`, the presence
// the muted body decided, in the polarity the run took.  A present key of a
// null-free map is exactly a non-null READ; a HashMap's compute family and
// putIfAbsent treat a null value as absent, which is the same test.
Expression *record_presence(Expression *state, Expression *key,
                            Expression *owner, bool present) {
  Expression *old = read_of(state, key, owner);
  ConcolicMngr::record_path_condition(new OpSymExpression(
      old, SymbolExpression::get(Sym_NULL), present ? op_ne : op_eq, true));
  return old;
}

// Records `READ(state, key) == expected` or `!=`, as the body decided it,
// and answers the equality.
Expression *record_match(Expression *state, Expression *key,
                         Expression *expected, Expression *owner,
                         bool matched) {
  Expression *read = read_of(state, key, owner);
  Expression *equal = new OpSymExpression(read, expected, op_eq, true);
  ConcolicMngr::record_path_condition(
      matched ? equal : new OpSymExpression(read, expected, op_ne, true));
  return equal;
}

Expression *publish(oop container, const char *operation, Expression *state,
                    const exp_list_t &arguments, Expression *owner,
                    Expression *guard = NULL) {
  Expression *next = relation(operation, state, arguments, owner, T_OBJECT,
                              std::string(), guard);
  ConcolicMngr::ctx->set_container_state(container, next);
  ContainerSupport::publish_state(container, next, operation);
  return next;
}

Expression *put(oop container, Expression *state, Expression *key,
                Expression *value, Expression *owner) {
  exp_list_t arguments;
  arguments.push_back(key);
  arguments.push_back(value);
  return publish(container, "PUT", state, arguments, owner);
}

Expression *remove(oop container, Expression *state, Expression *key,
                   Expression *owner) {
  exp_list_t arguments;
  arguments.push_back(key);
  return publish(container, "REMOVE", state, arguments, owner);
}

// Records `REMOVE_IF(prev_state, key) under guard` as a new version of the
// map the cursor walks.  The guard is oriented as the removal condition
// (true => the key is gone), so a concrete replay that folds it reproduces
// this run and a solver that flips it removes (or restores) exactly this key.
void install_conditional_removal(oop cursor, Expression *prev_state,
                                 Expression *key, Expression *guard,
                                 Expression *owner) {
  if (prev_state == NULL || key == NULL || guard == NULL) return;
  exp_list_t arguments;
  arguments.push_back(key);
  publish(cursor, "REMOVE_IF", prev_state, arguments, owner, guard);
}

// Closes out the element an iterator returned last when the loop moved past
// it without removing it.  If a marked symbolic branch guarded it, the
// removal that did NOT fire is still recorded -- as the branch's other arm,
// which is concretely false -- so the key is present on this run and
// flippable off it.
void dispose_conditional_removal(oop cursor, Expression *owner) {
  ThreadContext *ctx = ConcolicMngr::ctx;
  if (ctx == NULL || !ctx->conditional_removal_active()) return;
  if (ctx->conditional_removal_is_guarded()) {
    Expression *guard = ctx->conditional_removal_guard()->logical_negation();
    Expression *key = ctx->conditional_removal_key();
    Expression *prev = ctx->container_state(cursor, "ASSOCIATIVE");
    ctx->clear_conditional_removal();
    // A guard with no relational complement yields NULL here; drop it rather
    // than record a backwards removal -- install_conditional_removal no-ops.
    install_conditional_removal(cursor, prev, key, guard, owner);
    return;
  }
  ctx->clear_conditional_removal();
}

// A callback's boolean result as a removal guard.
Expression *as_guard(Expression *result) {
  return result->is_boolean_expression() ? result
      : static_cast<Expression *>(new OpSymExpression(
            result, new ConExpression((jint) 0), op_ne, true));
}

// The removal condition of one removeIf visit: the predicate's own boolean
// expression, else what its path decided in the direction it answered;
// NULL when nothing symbolic decided it.
Expression *removal_guard(const CallbackResult &visit) {
  if (visit.symbolic) return as_guard(visit.result);
  return (visit.returned_int & 1) != 0 ? visit.path : visit.path_negation;
}

// The value a visiting callback's element stands for: the state's READ of
// its key when the map has a state, else the value's own expression.
Expression *element_value(Expression *state, Expression *key,
                          Expression *owner, oop value) {
  if (state == NULL) return ContainerSupport::semantic_value(value);
  return read_of(state, key, owner, value);
}

// The calls whose callback visits one element per call (forEach,
// replaceAll, removeIf): each visit is seeded with a READ of the state, so
// a decision on it is a path condition per element per call.  Past the
// snapshot bound the visits are not seeded, and the call refuses its map by
// name (CALLBACK_VISITS_OVER_BOUND) rather than state the rest concretely.
bool visiting(const std::string &method) {
  return method == "forEach" || method == "replaceAll"
      || method == "removeIf";
}

}  // namespace

std::set<std::string> SymMap::target_class_names = init_target_class_names();

std::set<std::string> SymMap::init_target_class_names() {
  static const char *const NAMES[] = {
    "java/util/Map", "java/util/Map$Entry",
    // A map view's removeIf is Collection's default; any other receiver of
    // it declines here.
    "java/util/Collection",
    "java/util/HashMap", "java/util/LinkedHashMap",
    "java/util/HashMap$EntrySet", "java/util/HashMap$KeySet",
    "java/util/HashMap$Values", "java/util/HashMap$EntryIterator",
    "java/util/HashMap$KeyIterator", "java/util/HashMap$ValueIterator",
    "java/util/HashMap$HashIterator", "java/util/HashMap$Node",
    "java/util/LinkedHashMap$LinkedEntrySet",
    "java/util/LinkedHashMap$LinkedKeySet",
    "java/util/LinkedHashMap$LinkedValues",
    "java/util/LinkedHashMap$LinkedEntryIterator",
    "java/util/LinkedHashMap$LinkedKeyIterator",
    "java/util/LinkedHashMap$LinkedValueIterator",
    "java/util/LinkedHashMap$LinkedHashIterator",
    "java/util/LinkedHashMap$Entry",
    "java/util/concurrent/ConcurrentHashMap",
    "java/util/concurrent/ConcurrentHashMap$CollectionView",
    "java/util/concurrent/ConcurrentHashMap$EntrySetView",
    "java/util/concurrent/ConcurrentHashMap$ValuesView",
    "java/util/concurrent/ConcurrentHashMap$BaseIterator",
    "java/util/concurrent/ConcurrentHashMap$KeyIterator",
    "java/util/concurrent/ConcurrentHashMap$ValueIterator",
    "java/util/concurrent/ConcurrentHashMap$EntryIterator",
    "java/util/concurrent/ConcurrentHashMap$MapEntry",
    "java/util/Hashtable", "java/util/Hashtable$KeySet",
    "java/util/Hashtable$EntrySet", "java/util/Hashtable$ValueCollection",
    "java/util/Hashtable$Entry",
    NULL
  };
  std::set<std::string> set;
  for (const char *const *name = NAMES; *name != NULL; ++name) {
    set.insert(*name);
  }
  return set;
}

std::set<std::string> SymMap::handle_method_names = init_handle_method_names();

std::set<std::string> SymMap::init_handle_method_names() {
  static const char *const NAMES[] = {
    "put", "get", "getOrDefault", "remove", "containsKey", "isEmpty",
    "clear", "size", "mappingCount", "entrySet", "keySet", "values",
    "iterator", "hasNext", "next", "getKey", "getValue", "putAll",
    "putIfAbsent", "replace", "replaceAll", "compute", "computeIfAbsent",
    "computeIfPresent", "merge", "forEach", "removeIf", NULL
  };
  std::set<std::string> set;
  for (const char *const *name = NAMES; *name != NULL; ++name) {
    set.insert(*name);
  }
  return set;
}

void SymMap::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->register_model(target_class_names, invoke_method_helper,
                               finish_method_helper);
}

bool SymMap::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  Method *callee = handle.get_callee_method();
  oop target = callee == NULL || callee->is_static()
      ? (oop) NULL : handle.get_param<oop>(0);
  // Collection's default removeIf is this model's only on a map's key or
  // entry view.  A values view cannot name what it removes.
  if (handle.get_callee_holder_name() == "java/util/Collection") {
    if (callee_name != "removeIf") return false;
    if (klass_is_one_of(target, VALUE_VIEWS)) {
      ContainerSupport::abandon_state(
          ContainerSupport::backing_container(target),
          "ASSOCIATIVE_VALUES_REMOVE_IF_UNMODELED");
      return false;
    }
    if (!klass_is_one_of(target, KEY_VIEWS)
        && !klass_is_one_of(target, ENTRY_VIEWS)) {
      return false;
    }
  }
  oop container = ContainerSupport::backing_container(target);
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    // A symbolic value admits the model, and so does a mutation this thread
    // is performing because of a symbolic decision (see
    // ContainerSupport::guarded_mutation), and a call with a callback on a
    // map whose state is tracked: its body runs muted and the callback with
    // propagation, so what the callback computes is kept.  Anything else
    // runs as bytecode.
    const bool callback = takes_callback(callee_name) && container != NULL;
    const bool recording = handle.general_check_param_symbolized()
        || ContainerSupport::guarded_mutation(callee_name)
        || (callback && SharedFieldVersions::is_tracked(
                            ContainerSupport::state_location(container)));
    if (!recording) return false;
    if (container == NULL && map_level(callee_name)) {
      // A subclass of a modeled class, or an access-ordered LinkedHashMap,
      // is refused by name; anything else is no map this model knows, and
      // runs as bytecode.
      const std::string reason = ContainerSupport::unmodeled_reason(target);
      if (!reason.empty()) ContainerSupport::abandon_state(target, reason);
      return false;
    }
    // An entry or an iterator a callback reads is no reentry; a call on the
    // map itself is.
    if (container != NULL
        && (map_level(callee_name) || callee_name == "remove"
            || callee_name == "clear")
        && ConcolicMngr::ctx->get_method_symbolizer().in_callback()
        && ConcolicMngr::ctx->get_method_symbolizer().reenters(container)) {
      // A callback called back into the container its call is changing:
      // no chain can say in which order the two happened.
      ContainerSupport::abandon_state(container,
                                      "CALLBACK_REENTERS_CONTAINER");
      return false;
    }
    handle.general_prepare_param();
    // Before the body runs: state what the container already holds, while
    // the receiver is still untouched by this operation.  A view is not a
    // location, so the container whose base this is is the one the view
    // belongs to.
    ContainerSupport::state_base_before_operation(
        container != NULL ? container : target);
    // A removal through a view names the entry the iterator last returned,
    // and the iterator forgets it inside remove(); read it here, while the
    // body has not run, and let the publisher consume it.
    if (container != NULL && container != target
        && callee_name == "remove") {
      oop key_object = OopUtils::key_of_map_node(
          OopUtils::current_node_of_iterator(target));
      if (key_object != NULL) {
        ConcolicMngr::ctx->note_view_removal_argument(
            ContainerSupport::concrete_value(key_object));
      }
    }
    if (callback) {
      handle.set_pre_state(
          ConcolicMngr::ctx->find_container_state(container));
      handle.set_seeder(seed_callback);
      handle.set_mutates_per_callback(callee_name == "removeIf"
                                      || callee_name == "replaceAll");
    }
    return true;
  }
  if (ContainerSupport::claims_state(handle)
      && !ContainerSupport::follows_callee_body(callee_name)) {
    // An operation nobody modeled may have changed a state that other threads
    // still read.  The location is marked and the map leaves the model
    // (abandon_state), so later queries cannot treat the retained writer set as
    // complete, and this thread goes on concretely for this map alone.
    ContainerSupport::abandon_state(target,
        ContainerSupport::unsupported(
        "ASSOCIATIVE_OPERATION_UNSUPPORTED", handle).c_str());
  }
  return false;
}

// The contract of a callback: what its parameters are, in terms of the call.
void SymMap::seed_callback(MethodSymbolizerHandle &call,
                           const std::vector<oop> &arguments,
                           exp_list_t *seeds, Expression **key) {
  const std::string &method = call.get_callee_name();
  exp_list_t &parameters = call.get_param_list();
  Expression *state = call.pre_state();
  Expression *owner = ContainerSupport::receiver_owner(parameters[0]);
  if (visiting(method) && call.callbacks().size()
          >= (size_t) ConcolicMngr::initialSnapshotMaxEntries()) {
    call.refuse_callbacks("CALLBACK_VISITS_OVER_BOUND");
    return;
  }
  if (method == "computeIfAbsent") {
    seeds->push_back(parameters[1]);
  } else if (method == "computeIfPresent" || method == "compute") {
    seeds->push_back(parameters[1]);
    seeds->push_back(state == NULL ? NULL
        : read_of(state, parameters[1], owner));
  } else if (method == "merge") {
    seeds->push_back(state == NULL ? NULL
        : read_of(state, parameters[1], owner));
    seeds->push_back(parameters[2]);
  } else if (arguments.size() == 2) {
    // A map's forEach/replaceAll: (key, value) at the visited position.
    *key = key_expression(arguments[0]);
    seeds->push_back(*key);
    seeds->push_back(element_value(state, *key, owner, arguments[1]));
  } else if (arguments.size() == 1 && arguments[0] != NULL) {
    // A view's forEach/removeIf: its element.  An entry is the state's entry
    // of its key, so getKey/getValue are that key and its READ.
    oop view = call.get_param<oop>(0);
    if (klass_is_one_of(view, ENTRY_VIEWS)) {
      *key = key_expression(OopUtils::key_of_map_node(arguments[0]));
      exp_list_t entry;
      entry.push_back(*key);
      seeds->push_back(state == NULL ? NULL
          : relation("ENTRY", state, entry, owner));
    } else if (klass_is_one_of(view, KEY_VIEWS)) {
      *key = key_expression(arguments[0]);
      seeds->push_back(*key);
    } else {
      seeds->push_back(ContainerSupport::semantic_value(arguments[0]));
    }
  }
}

Expression *SymMap::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  exp_list_t &parameters = handle.get_param_list();
  if (parameters.empty() || handle.reentered()) return NULL;

  oop receiver_object = handle.get_param<oop>(0);
  // Which object the receiver's own read chose, kept on every relation this
  // call builds, while the relation's receiver stays this object's state.
  Expression *owner = ContainerSupport::receiver_owner(parameters[0]);
  oop container = ContainerSupport::backing_container(receiver_object);
  Expression *receiver = parameters[0];
  bool root_map = map_capability(
      ContainerSupport::capability(receiver_object));

  exp_list_t arguments;
  for (size_t index = 1; index < parameters.size(); ++index) {
    arguments.push_back(parameters[index]);
  }

  // ---- calls with a callback: the log of what each callback returned ----
  if (takes_callback(method)) {
    std::vector<CallbackResult> &callbacks = handle.callbacks();
    // A callback that ran unlogged (a declined window) or unseeded (past
    // the visit bound) leaves the call unstated: the map leaves the model.
    if (handle.callback_refusal() != NULL) {
      ContainerSupport::abandon_state(container, handle.callback_refusal());
      return NULL;
    }
    Expression *state = ConcolicMngr::ctx->container_state(
        container, "ASSOCIATIVE");
    if (state == NULL) return NULL;
    if (method == "forEach") return NULL;
    if (method == "replaceAll" || method == "removeIf") {
      for (size_t index = 0; index < callbacks.size(); ++index) {
        const CallbackResult &visit = callbacks[index];
        if (visit.key == NULL) continue;
        if (method == "replaceAll") {
          state = put(container, state, visit.key, visit.result, owner);
          continue;
        }
        Expression *guard = removal_guard(visit);
        if (guard != NULL) {
          exp_list_t key;
          key.push_back(visit.key);
          state = publish(container, "REMOVE_IF", state, key, owner, guard);
        } else if ((visit.returned_int & 1) != 0) {
          state = remove(container, state, visit.key, owner);
        }
      }
      return NULL;
    }
    Expression *key = arguments[0];
    const bool called = !callbacks.empty();
    const CallbackResult result = called ? callbacks[0] : CallbackResult();
    if (method == "computeIfAbsent") {
      // Called exactly when the key was absent; a null result maps nothing.
      Expression *old = record_presence(state, key, owner, !called);
      if (!called) return old;
      if (result.returned_null) return result.result;
      put(container, state, key, result.result, owner);
      return result.result;
    }
    if (method == "computeIfPresent") {
      record_presence(state, key, owner, called);
      if (!called) return SymbolExpression::get(Sym_NULL);
      if (result.returned_null) {
        remove(container, state, key, owner);
      } else {
        put(container, state, key, result.result, owner);
      }
      return result.result;
    }
    if (method == "compute") {
      if (!called) return NULL;
      if (result.returned_null) {
        remove(container, state, key, owner);
      } else {
        put(container, state, key, result.result, owner);
      }
      return result.result;
    }
    // merge: the callback runs exactly when an old value was there.
    record_presence(state, key, owner, called);
    if (!called) {
      put(container, state, key, arguments[1], owner);
      return arguments[1];
    }
    if (result.returned_null) {
      remove(container, state, key, owner);
    } else {
      put(container, state, key, result.result, owner);
    }
    return result.result;
  }

  // ---- mutators the body decides by presence or by a value match ----
  if (root_map && (method == "putIfAbsent" || method == "replace"
                   || (method == "remove" && arguments.size() == 2)
                   || method == "putAll")) {
    Expression *state = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
    if (state == NULL) return NULL;
    if (method == "putAll") {
      oop source = handle.get_param<oop>(1);
      Expression *source_state = ContainerSupport::observed_state(source);
      if (source_state != NULL) {
        exp_list_t copied;
        copied.push_back(source_state);
        publish(receiver_object, "PUT_ALL", state, copied, owner);
        return NULL;
      }
      std::vector<oop> keys;
      std::vector<oop> values;
      const char *unreadable = NULL;
      bool over_bound = false;
      if (!ContainerSupport::read_concrete_members(source, &keys, &values,
                                                   &unreadable, &over_bound)
          || over_bound || keys.size() != values.size()) {
        ContainerSupport::abandon_state(receiver_object,
            "ASSOCIATIVE_PUT_ALL_SOURCE_UNSTATED");
        return NULL;
      }
      for (size_t index = 0; index < keys.size(); ++index) {
        state = put(receiver_object, state,
                    ContainerSupport::concrete_value(keys[index]),
                    ContainerSupport::concrete_value(values[index]), owner);
      }
      return NULL;
    }
    if (method == "putIfAbsent") {
      oop old_value = handle.get_result<oop>(T_OBJECT);
      Expression *old = record_presence(state, arguments[0], owner,
                                        old_value != NULL);
      if (old_value == NULL) {
        put(receiver_object, state, arguments[0], arguments[1], owner);
      }
      return old;
    }
    if (arguments.size() == 3 || method == "remove") {
      // replace(k, expected, update) and remove(k, expected) answer whether
      // the value matched.
      const bool matched = (handle.get_result<jint>(T_BOOLEAN) & 1) != 0;
      Expression *equal = record_match(state, arguments[0], arguments[1],
                                       owner, matched);
      if (matched && method == "remove") {
        remove(receiver_object, state, arguments[0], owner);
      } else if (matched) {
        put(receiver_object, state, arguments[0], arguments[2], owner);
      }
      return equal;
    }
    // replace(k, v): replaced exactly when a mapping was there.  A HashMap
    // that answered null may have replaced a null value.
    oop old_value = handle.get_result<oop>(T_OBJECT);
    if (old_value == NULL && ContainerSupport::capability(receiver_object)
                                 == ContainerSupport::CAPABILITY_HASH_MAP) {
      ContainerSupport::abandon_state(receiver_object,
                                      "ASSOCIATIVE_REPLACE_UNDECIDED");
      return NULL;
    }
    Expression *old = record_presence(state, arguments[0], owner,
                                      old_value != NULL);
    if (old_value != NULL) {
      put(receiver_object, state, arguments[0], arguments[1], owner);
    }
    return old;
  }

  bool map_operation = root_map && (method == "get"
      || method == "getOrDefault" || method == "containsKey"
      || method == "size" || method == "mappingCount" || method == "isEmpty"
      || method == "put"
      || method == "remove" || method == "clear"
      || method == "entrySet" || method == "keySet"
      || method == "values");
  if (map_operation) {
    receiver = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
  }
  if (receiver == NULL) return NULL;

  // A view the program built rather than a modeled call (a KeySetView of
  // newKeySet) is its map: its size, emptiness and clearing are the map's.
  Expression *view_of = NULL;
  if (!root_map && container != NULL && container != receiver_object
      && (method == "size" || method == "isEmpty" || method == "clear")
      && (parameters[0] == NULL
          || !parameters[0]->derived_container_value(&view_of))) {
    root_map = true;
    receiver_object = container;
    receiver = ConcolicMngr::ctx->container_state(container, "ASSOCIATIVE");
    if (receiver == NULL) return NULL;
  }

  // An entry a callback visits (ENTRY): its key, and the state's READ of it.
  ContainerExpression *entry = parameters[0] == NULL
      ? NULL : parameters[0]->as_container_expression();
  if ((method == "getKey" || method == "getValue") && entry != NULL
      && entry->get_operation() == "ENTRY") {
    Expression *key = entry->get_arguments()[0];
    return method == "getKey" ? key
        : read_of(entry->get_receiver(), key, owner,
                  handle.get_result<oop>(T_OBJECT));
  }

  const char *operation = NULL;
  if (method == "get") operation = "READ";
  else if (method == "getOrDefault") operation = "READ_OR_DEFAULT";
  else if (method == "containsKey") operation = "CONTAINS";
  else if (method == "size" || method == "mappingCount") operation = "SIZE";
  else if (method == "isEmpty") operation = "IS_EMPTY";
  else if (method == "entrySet") operation = "ENTRY_VIEW";
  else if (method == "keySet") operation = "KEY_VIEW";
  else if (method == "values") operation = "VALUE_VIEW";
  else if (method == "iterator") operation = "ITERATOR";
  else if (method == "next") {
    // Advancing past the previous element disposes it: if it was visited under
    // a marked symbolic branch and not removed, its (un-fired) conditional
    // removal is recorded now.
    dispose_conditional_removal(receiver_object, owner);
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
    put(receiver_object, old_state, arguments[0], arguments[1], owner);
    oop result = handle.get_result_type() == T_OBJECT
        ? handle.get_result<oop>(T_OBJECT) : NULL;
    Expression *old = read_of(old_state, arguments[0], owner, result);
    ContainerSupport::constrain_result(handle, old);
    return old;
  }
  if (method == "remove" && root_map && arguments.size() == 1) {
    Expression *old = read_of(receiver, arguments[0], owner,
        handle.get_result_type() == T_OBJECT
            ? handle.get_result<oop>(T_OBJECT) : NULL);
    ContainerSupport::constrain_result(handle, old);
    remove(receiver_object, receiver, arguments[0], owner);
    return old;
  }
  if (method == "clear" && root_map && arguments.empty()) {
    publish(receiver_object, "CLEAR", receiver, arguments, owner);
    return NULL;
  }
  if (method == "remove" && !root_map && arguments.empty()) {
    // A view is never a location of its own, so this is a mutation of the
    // backing map.  When the walk was never modelled -- every read concrete,
    // so entrySet()/iterator()/next() were not admitted and the cursor has no
    // chain at all -- the removal still has everything it needs, and both
    // halves are concrete in the iterator's own fields: the map it walks, and
    // the entry it last returned.  That is HDFS-11741's removeExpiredKeys(),
    // whose loop is entirely concrete and whose only symbolic thing is the
    // `expiryDate < now` decision that guards the remove.
    if (ConcolicMngr::ctx->find_container_state(receiver_object) == NULL) {
      Expression *base = container == NULL ? NULL
          : ConcolicMngr::ctx->container_state(container, "ASSOCIATIVE");
      Expression *removed_key =
          ConcolicMngr::ctx->take_view_removal_argument();
      // One named reason per cause: which half of the removal could not be
      // stated is the whole difference between a view this engine does not
      // know how to follow and an entry it could not name.
      if (container == NULL) {
        ContainerSupport::abandon_state(receiver_object,
            "ASSOCIATIVE_VIEW_OWNER_MISSING");
        return NULL;
      }
      if (base == NULL) {
        ContainerSupport::abandon_state(receiver_object,
            "ASSOCIATIVE_VIEW_OWNER_STATE_MISSING");
        return NULL;
      }
      if (removed_key == NULL) {
        ContainerSupport::abandon_state(receiver_object,
            "ASSOCIATIVE_VIEW_REMOVED_KEY_MISSING");
        return NULL;
      }
      remove(container, base, removed_key, owner);
      ConcolicMngr::ctx->clear_conditional_removal();
      return NULL;
    }
    int position = ConcolicMngr::ctx->next_container_removal_position(
        receiver_object);
    Expression *root = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
    if (root == NULL || position < 0) {
      ContainerSupport::abandon_state(receiver_object,
          "ASSOCIATIVE_ITERATOR_REMOVE_WITHOUT_NEXT");
      return NULL;
    }
    // This element WAS removed.  If a marked symbolic branch controlled the
    // removal, record it as REMOVE_IF keyed by the entry with that branch's
    // predicate as the guard -- concretely true here, so a replay removes the
    // key exactly as this run did while a solver may flip it back.  The
    // ordinal bookkeeping above still advances, so any position-keyed views of
    // this cursor stay consistent.
    if (ConcolicMngr::ctx->conditional_removal_is_guarded()) {
      Expression *guard = ConcolicMngr::ctx->conditional_removal_guard();
      Expression *key = ConcolicMngr::ctx->conditional_removal_key();
      ConcolicMngr::ctx->clear_conditional_removal();
      install_conditional_removal(receiver_object, root, key, guard, owner);
      return NULL;
    }
    // An unconditional iterator remove (no controlling symbolic branch) keeps
    // the position-keyed REMOVE_AT exactly as before.  The receiver is the
    // cursor, not the map; state_location canonicalizes it to the map it
    // walks, so this is a version of that one location.
    ConcolicMngr::ctx->clear_conditional_removal();
    exp_list_t remove_arguments;
    remove_arguments.push_back(new ConExpression((jint)position));
    publish(receiver_object, "REMOVE_AT", root, remove_arguments, owner);
    return NULL;
  }
  if (method == "clear" && !root_map && arguments.empty()) {
    Expression *root = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
    if (root == NULL) {
      ContainerSupport::abandon_state(receiver_object,
          "ASSOCIATIVE_VIEW_OWNER_MISSING");
      return NULL;
    }
    Expression *next = relation("CLEAR", root, arguments, owner);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "CLEAR_VIEW");
    return NULL;
  }
  if (method == "remove" && (!root_map || arguments.size() != 1)) {
    // A symbolic argument can make an unrelated map invocation enter this
    // helper even though the receiver itself is not one of the selected
    // shared carriers.  Its concrete body remains the only semantics claimed
    // for that map: it leaves the model, and a selected location is marked
    // incomplete, since the unsupported mutation left its versions so.
    ContainerSupport::abandon_state(receiver_object,
        ContainerSupport::unsupported(
        "ASSOCIATIVE_REMOVE_OVERLOAD_UNSUPPORTED", handle).c_str());
    return NULL;
  }
  if (method == "clear" && !root_map) {
    ContainerSupport::abandon_state(receiver_object,
        "ASSOCIATIVE_VIEW_CLEAR_UNSUPPORTED");
    return NULL;
  }
  if (method == "hasNext" && arguments.empty()) {
    // The final hasNext() of a while(it.hasNext()) loop disposes the last
    // visited element, which no following next() would.
    dispose_conditional_removal(receiver_object, owner);
    arguments.push_back(new ConExpression((jint)
        ConcolicMngr::ctx->current_container_position(receiver_object)));
    Expression *result = relation("HAS_NEXT", receiver, arguments, owner,
                                  T_BOOLEAN);
    ContainerSupport::constrain_result(handle, result);
    return result;
  }
  if (operation == NULL) return NULL;

  BasicType expression_type = handle.get_result_type();
  oop result_object = NULL;
  if (expression_type == T_OBJECT) {
    result_object = handle.get_result<oop>(T_OBJECT);
    expression_type = ContainerSupport::result_type(
        result_object, expression_type);
  }
  const std::string result_java_type = ContainerSupport::java_type(
      result_object, handle.get_result_type());

  Expression *result = NULL;
  // Every observation of a selected root map binds to the state it may have
  // observed rather than to whichever state happens to be installed when the
  // helper finishes.  Views are observations too: values().iterator().next()
  // and values().toArray() inherit the guarded writer choice made here
  // instead of silently walking an unversioned last-state receiver.
  bool observation_admitted = true;
  bool selected_without_value = false;
  bool root_observation = root_map
      && (method == "get" || method == "getOrDefault"
          || method == "containsKey" || method == "size"
          || method == "mappingCount" || method == "isEmpty"
          || method == "entrySet" || method == "keySet"
          || method == "values");
  if (root_observation) {
    ContainerSupport::StateQuery bound = ContainerSupport::query_state(
        receiver_object, "ASSOCIATIVE", operation, arguments,
        expression_type, result_java_type, owner);
    if (bound.expression != NULL) {
      result = bound.expression;
      // A guarded writer choice must not be constrained to the concrete value
      // this replay happened to return; that would pin the read to one writer.
      observation_admitted = false;
    } else if (bound.selected) {
      selected_without_value = true;
    }
  }
  if (result == NULL && !selected_without_value) {
    result = relation(operation, receiver, arguments, owner,
                      expression_type, result_java_type);
  }
  if (result == NULL) return NULL;
  if (method == "next") {
    Expression *key = iterated_entry_key(
        receiver_object, result_object, result);
    if (key != NULL) ConcolicMngr::ctx->begin_conditional_removal(key);
  }
  if (observation_admitted
      && (method == "get" || method == "getOrDefault"
          || method == "containsKey" || method == "size"
          || method == "mappingCount" || method == "isEmpty"
          || (method == "next"
              && klass_is_one_of(receiver_object, SCALAR_ITERATORS)))) {
    ContainerSupport::constrain_result(handle, result);
  }
  if ((method == "getKey" || method == "getValue")
      && result_object != NULL) {
    exp_list_t observation_arguments;
    observation_arguments.push_back(
        ContainerSupport::concrete_value(result_object));
    ConcolicMngr::record_path_condition(relation(
        method == "getKey" ? "OBSERVE_KEY" : "OBSERVE_VALUE",
        receiver, observation_arguments, owner, T_BOOLEAN));
  }
  if (handle.get_result_type() == T_OBJECT) {
    if (result_object != NULL) {
      bool derived_container = method == "entrySet"
          || method == "keySet" || method == "values"
          || method == "iterator";
      ContainerSupport::attach_result(result_object, result,
          derived_container ? receiver_object : NULL);
    }
  }
  return result;
}

#endif // ENABLE_CONCOLIC
