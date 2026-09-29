#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/utils.hpp"

static bool is_scalar_map_iterator(oop receiver) {
  if (receiver == NULL || receiver->klass() == NULL
      || receiver->klass()->name() == NULL) return false;
  Symbol *name = receiver->klass()->name();
  return name->equals("java/util/HashMap$KeyIterator")
      || name->equals("java/util/HashMap$ValueIterator")
      || name->equals("java/util/LinkedHashMap$LinkedKeyIterator")
      || name->equals("java/util/LinkedHashMap$LinkedValueIterator");
}

// An iterator whose next() yields the map *key*, so the element it returns is
// exactly the removed key a conditional removal must name.  A value iterator
// is deliberately excluded: it never surfaces the key.
static bool is_key_map_iterator(oop receiver) {
  if (receiver == NULL || receiver->klass() == NULL
      || receiver->klass()->name() == NULL) return false;
  Symbol *name = receiver->klass()->name();
  return name->equals("java/util/HashMap$KeyIterator")
      || name->equals("java/util/LinkedHashMap$LinkedKeyIterator");
}

// An iterator whose next() yields a Map.Entry. A loop may read the value but
// never the key, so recover the removed key from the returned entry node.
static bool is_entry_map_iterator(oop receiver) {
  if (receiver == NULL || receiver->klass() == NULL
      || receiver->klass()->name() == NULL) return false;
  Symbol *name = receiver->klass()->name();
  return name->equals("java/util/HashMap$EntryIterator")
      || name->equals("java/util/LinkedHashMap$LinkedEntryIterator");
}

// Prefer the expression carried by the actual key object.  In particular, an
// Integer produced from a symbolic int already carries that int expression;
// wrapping NEXT in KEY would repeat the iterator's whole input map in every
// REMOVE_IF and make successive passes grow the state exponentially.
//
// A key with no semantic expression cannot contribute symbolic lineage.  Its
// concrete/identity leaf is therefore the bounded fallback: it records which
// entry this replay visited without copying the map state into its own update.
static Expression *iterated_entry_key(oop cursor, oop result_object,
                                      Expression *next) {
  if (next == NULL) return NULL;
  oop key_object = NULL;
  if (is_key_map_iterator(cursor)) {
    key_object = result_object;
  } else if (is_entry_map_iterator(cursor) && result_object != NULL) {
    key_object = OopUtils::key_of_map_node(result_object);
  } else {
    return NULL;
  }
  Expression *carried = ContainerSupport::semantic_value(key_object);
  return carried != NULL ? carried
                         : ContainerSupport::concrete_value(key_object);
}

// Records `REMOVE_IF(prev_state, key) under guard` as a new version of the map
// the cursor walks.  The guard is oriented as the removal condition (true =>
// the key is gone), so a concrete replay that folds it reproduces this run and
// a solver that flips it removes (or restores) exactly this key.
static void install_conditional_removal(oop cursor, Expression *prev_state,
                                        Expression *key, Expression *guard) {
  if (prev_state == NULL || key == NULL || guard == NULL) return;
  exp_list_t arguments;
  arguments.push_back(key);
  Expression *next = new ContainerExpression(
      "ASSOCIATIVE", "REMOVE_IF", prev_state, arguments, T_OBJECT,
      std::string(), guard);
  ConcolicMngr::ctx->set_container_state(cursor, next);
  ContainerSupport::publish_state(cursor, next, "REMOVE_IF");
}

// Closes out the element an iterator returned last when the loop moved past it
// without removing it.  If a marked symbolic branch guarded it, the removal
// that did NOT fire is still recorded -- as the branch's other arm, which is
// concretely false -- so the key is present on this run and flippable off it.
static void dispose_conditional_removal(oop cursor) {
  ThreadContext *ctx = ConcolicMngr::ctx;
  if (ctx == NULL || !ctx->conditional_removal_active()) return;
  if (ctx->conditional_removal_is_guarded()) {
    Expression *guard = ctx->conditional_removal_guard()->logical_negation();
    Expression *key = ctx->conditional_removal_key();
    Expression *prev = ctx->container_state(cursor, "ASSOCIATIVE");
    ctx->clear_conditional_removal();
    // A guard with no relational complement yields NULL here; drop it rather
    // than record a backwards removal -- install_conditional_removal no-ops.
    install_conditional_removal(cursor, prev, key, guard);
    return;
  }
  ctx->clear_conditional_removal();
}

std::set<std::string> SymMap::target_class_names = init_target_class_names();

std::set<std::string> SymMap::init_target_class_names() {
  std::set<std::string> set;
  set.insert("java/util/Map");
  set.insert("java/util/Map$Entry");
  set.insert("java/util/HashMap");
  set.insert("java/util/LinkedHashMap");
  set.insert("java/util/HashMap$EntrySet");
  set.insert("java/util/HashMap$KeySet");
  set.insert("java/util/HashMap$Values");
  set.insert("java/util/HashMap$EntryIterator");
  set.insert("java/util/HashMap$KeyIterator");
  set.insert("java/util/HashMap$ValueIterator");
  set.insert("java/util/HashMap$HashIterator");
  set.insert("java/util/HashMap$Node");
  set.insert("java/util/LinkedHashMap$LinkedEntrySet");
  set.insert("java/util/LinkedHashMap$LinkedKeySet");
  set.insert("java/util/LinkedHashMap$LinkedValues");
  set.insert("java/util/LinkedHashMap$LinkedEntryIterator");
  set.insert("java/util/LinkedHashMap$LinkedKeyIterator");
  set.insert("java/util/LinkedHashMap$LinkedValueIterator");
  set.insert("java/util/LinkedHashMap$LinkedHashIterator");
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
  set.insert("hasNext");
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

void SymMap::init_register_class(MethodSymbolizer *m_symbolizer) {
  m_symbolizer->register_model(target_class_names, invoke_method_helper,
                               finish_method_helper);
}

bool SymMap::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &callee_name = handle.get_callee_name();
  if (handle_method_names.find(callee_name) != handle_method_names.end()) {
    // A symbolic value admits the model, and so does a mutation this thread
    // is performing because of a symbolic decision: see
    // ContainerSupport::guarded_mutation.
    bool recording = handle.general_check_param_symbolized()
        || ContainerSupport::guarded_mutation(callee_name);
    if (recording) {
      handle.general_prepare_param();
      // Before the body runs: state what the container already holds, while
      // the receiver is still untouched by this operation.  A view is not a
      // location, so the container whose base this is is the one the view
      // belongs to.
      oop target = handle.get_param<oop>(0);
      oop backing = OopUtils::map_of_view(target);
      ContainerSupport::state_base_before_operation(
          backing != NULL ? backing : target);
      // A removal through a view names the entry the iterator last returned,
      // and the iterator forgets it inside remove(); read it here, while the
      // body has not run, and let the publisher consume it.
      if (backing != NULL && callee_name == "remove") {
        oop key_object = OopUtils::key_of_map_node(
            OopUtils::current_node_of_iterator(target));
        if (key_object != NULL) {
          ConcolicMngr::ctx->note_view_removal_argument(
              ContainerSupport::concrete_value(key_object));
        }
      }
    }
    return recording;
  }
  if (ContainerSupport::claims_state(handle)
      && !ContainerSupport::follows_callee_body(callee_name)) {
    // An operation nobody modeled may have changed a state that other threads
    // still read.  The location is marked and the map leaves the model
    // (abandon_state), so later queries cannot treat the retained writer set as
    // complete, and this thread goes on concretely for this map alone.
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
        "ASSOCIATIVE_OPERATION_UNSUPPORTED", handle).c_str());
  }
  return false;
}

Expression *SymMap::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  exp_list_t &parameters = handle.get_param_list();
  if (parameters.empty()) return NULL;
  if (method == "putAll" || method == "putIfAbsent"
      || method == "replace" || method == "replaceAll"
      || method == "compute" || method == "computeIfAbsent"
      || method == "computeIfPresent" || method == "merge") {
    // The mutation ran concretely and produced no version.  On a selected map
    // that is a writer no later read can name: abandon_state says so
    // permanently for the location every other thread reads, and drops the
    // map from the model.
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
        "ASSOCIATIVE_MUTATOR_UNSUPPORTED", handle).c_str());
    return NULL;
  }

  oop receiver_object = handle.get_param<oop>(0);
  Expression *receiver = parameters[0];
  bool root_map = ContainerSupport::associative(receiver_object);
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
    // Advancing past the previous element disposes it: if it was visited under
    // a marked symbolic branch and not removed, its (un-fired) conditional
    // removal is recorded now.
    dispose_conditional_removal(receiver_object);
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
    ContainerSupport::publish_state(receiver_object, new_state, "PUT");
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
    ContainerSupport::publish_state(receiver_object, new_state, "REMOVE");
    return old;
  }
  if (method == "clear" && root_map && arguments.empty()) {
    Expression *new_state = new ContainerExpression(
        "ASSOCIATIVE", "CLEAR", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, new_state);
    ContainerSupport::publish_state(receiver_object, new_state, "CLEAR");
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
      oop backing_map = OopUtils::map_of_view(receiver_object);
      Expression *base = backing_map == NULL ? NULL
          : ConcolicMngr::ctx->container_state(backing_map, "ASSOCIATIVE");
      Expression *removed_key =
          ConcolicMngr::ctx->take_view_removal_argument();
      // One named reason per cause: which half of the removal could not be
      // stated is the whole difference between a view this engine does not
      // know how to follow and an entry it could not name.
      if (backing_map == NULL) {
        ContainerSupport::abandon_state(handle.get_param<oop>(0),
            "ASSOCIATIVE_VIEW_OWNER_MISSING");
        return NULL;
      }
      if (base == NULL) {
        ContainerSupport::abandon_state(handle.get_param<oop>(0),
            "ASSOCIATIVE_VIEW_OWNER_STATE_MISSING");
        return NULL;
      }
      if (removed_key == NULL) {
        ContainerSupport::abandon_state(handle.get_param<oop>(0),
            "ASSOCIATIVE_VIEW_REMOVED_KEY_MISSING");
        return NULL;
      }
      exp_list_t removed;
      removed.push_back(removed_key);
      Expression *next = new ContainerExpression(
          "ASSOCIATIVE", "REMOVE", base, removed);
      ConcolicMngr::ctx->set_container_state(backing_map, next);
      ContainerSupport::publish_state(backing_map, next, "REMOVE");
      ConcolicMngr::ctx->clear_conditional_removal();
      return NULL;
    }
    int position = ConcolicMngr::ctx->next_container_removal_position(
        receiver_object);
    Expression *root = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
    if (root == NULL || position < 0) {
      ContainerSupport::abandon_state(handle.get_param<oop>(0),
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
      install_conditional_removal(receiver_object, root, key, guard);
      return NULL;
    }
    // An unconditional iterator remove (no controlling symbolic branch) keeps
    // the position-keyed REMOVE_AT exactly as before.
    ConcolicMngr::ctx->clear_conditional_removal();
    exp_list_t remove_arguments;
    remove_arguments.push_back(new ConExpression((jint)position));
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "REMOVE_AT", root, remove_arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    // The receiver is the cursor, not the map; state_location canonicalizes it
    // to the map it walks, so this is a version of that one location.
    ContainerSupport::publish_state(receiver_object, next, "REMOVE_AT");
    return NULL;
  }
  if (method == "clear" && !root_map && arguments.empty()) {
    Expression *root = ConcolicMngr::ctx->container_state(
        receiver_object, "ASSOCIATIVE");
    if (root == NULL) {
      ContainerSupport::abandon_state(handle.get_param<oop>(0),
          "ASSOCIATIVE_VIEW_OWNER_MISSING");
      return NULL;
    }
    Expression *next = new ContainerExpression(
        "ASSOCIATIVE", "CLEAR", root, arguments);
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
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        "ASSOCIATIVE_VIEW_CLEAR_UNSUPPORTED");
    return NULL;
  }
  if (method == "hasNext" && arguments.empty()) {
    // The final hasNext() of a while(it.hasNext()) loop disposes the last
    // visited element, which no following next() would.
    dispose_conditional_removal(receiver_object);
    arguments.push_back(new ConExpression((jint)
        ConcolicMngr::ctx->current_container_position(receiver_object)));
    Expression *result = new ContainerExpression(
        "ASSOCIATIVE", "HAS_NEXT", receiver, arguments, T_BOOLEAN);
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
      && (method == "get" || method == "containsKey"
          || method == "size" || method == "isEmpty"
          || method == "entrySet" || method == "keySet"
          || method == "values");
  if (root_observation) {
    ContainerSupport::StateQuery bound = ContainerSupport::query_state(
        receiver_object, "ASSOCIATIVE", operation, arguments,
        expression_type, result_java_type);
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
    result = new ContainerExpression(
        "ASSOCIATIVE", operation, receiver, arguments,
        expression_type, result_java_type);
  }
  if (result == NULL) return NULL;
  if (method == "next") {
    Expression *key = iterated_entry_key(
        receiver_object, result_object, result);
    if (key != NULL) ConcolicMngr::ctx->begin_conditional_removal(key);
  }
  if (observation_admitted
      && (method == "get" || method == "containsKey"
          || method == "size" || method == "isEmpty"
          || method == "next" && is_scalar_map_iterator(receiver_object))) {
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
