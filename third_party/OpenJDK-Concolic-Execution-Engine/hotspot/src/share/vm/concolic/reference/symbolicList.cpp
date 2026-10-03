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
      ContainerSupport::abandon_state(handle.get_param<oop>(0),
          "INDEXED_LIST_ITERATOR_OFFSET_UNSUPPORTED");
      return false;
    }
    if ((callee_name == "add" || callee_name == "set")
        && ContainerSupport::capability(receiver)
               != ContainerSupport::CAPABILITY_INDEXED) {
      ContainerSupport::abandon_state(receiver,
          "INDEXED_LIST_ITERATOR_MUTATOR_UNSUPPORTED");
      return false;
    }
  }
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
      // the receiver is still untouched by this operation.  An iterator is
      // not a location, so the container whose base this is is the list it
      // walks.
      oop target = handle.get_param<oop>(0);
      oop backing = OopUtils::list_of_iterator(target);
      ContainerSupport::state_base_before_operation(
          backing != NULL ? backing : target);
      // A removal through an iterator names the index it last returned, and
      // the iterator forgets it inside remove(); read it here, while the body
      // has not run, and let the publisher consume it.
      if (backing != NULL && callee_name == "remove") {
        bool found = false;
        jint index = OopUtils::last_returned_index(target, &found);
        if (found && index >= 0) {
          ConcolicMngr::ctx->note_view_removal_argument(
              new ConExpression(index));
        }
      }
    }
    return recording;
  }
  if (ContainerSupport::claims_state(handle)
      && !ContainerSupport::follows_callee_body(callee_name)) {
    // An operation nobody modeled may have changed a state that other regions
    // still read.  The location is marked and the list leaves the model
    // (abandon_state), so later queries cannot treat the retained writer set as
    // complete, and this thread goes on concretely for this list alone.
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
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
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
        "INDEXED_TO_ARRAY_RECEIVER_UNSUPPORTED", handle).c_str());
    return NULL;
  }
  if (arguments.size() > 1) {
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
        "INDEXED_TO_ARRAY_OVERLOAD_UNSUPPORTED", handle).c_str());
    return NULL;
  }
  BasicType result_type = handle.get_result_type();
  oop published = result_type == T_ARRAY || result_type == T_OBJECT
      ? handle.get_result<oop>(result_type) : NULL;
  if (published == NULL || !published->is_array()) {
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        ContainerSupport::unsupported(
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
      ContainerSupport::abandon_state(handle.get_param<oop>(0),
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
  bool root_container = ContainerSupport::capability(receiver_object)
      == ContainerSupport::CAPABILITY_INDEXED;
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
    ContainerSupport::abandon_state(receiver_object,
        "INDEXED_LIST_ITERATOR_MUTATOR_UNSUPPORTED");
    return NULL;
  }
  if (method == "toArray") {
    return published_array(handle, root_container ? receiver : NULL,
                           arguments);
  }
  if ((method == "add" || method == "offer") && root_container) {
    const char *operation = arguments.size() == 1 ? "APPEND" : "INSERT";
    Expression *next = new ContainerExpression(
        "INDEXED", operation, receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, operation);
    return handle.get_result_type() == T_BOOLEAN
        ? (Expression *)new ConExpression((jboolean)true) : NULL;
  }
  if (method == "set" && root_container && arguments.size() == 2) {
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
    ContainerSupport::state_result(handle, old);
    ContainerSupport::attach_result(result_object, old);
    Expression *next = new ContainerExpression(
        "INDEXED", "WRITE", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "WRITE");
    return old;
  }
  if (method == "remove" && root_container && arguments.size() == 1) {
    ResourceMark rm;
    const char *signature =
        handle.get_callee_method()->signature()->as_C_string();
    if (signature != NULL && signature[0] == '(' && signature[1] == 'I') {
      oop result_object = handle.get_result_type() == T_OBJECT
          ? handle.get_result<oop>(T_OBJECT) : NULL;
      Expression *old = new ContainerExpression(
          "INDEXED", "READ", receiver, arguments,
          ContainerSupport::result_type(
              result_object, handle.get_result_type()),
          ContainerSupport::java_type(
              result_object, handle.get_result_type()));
      ContainerSupport::state_result(handle, old);
      ContainerSupport::attach_result(result_object, old);
      Expression *next = new ContainerExpression(
          "INDEXED", "REMOVE", receiver, arguments);
      ConcolicMngr::ctx->set_container_state(receiver_object, next);
      ContainerSupport::publish_state(receiver_object, next, "REMOVE");
      return old;
    }
    // remove(Object) has no indexed relation: the position it removed is not
    // recoverable from the argument.  It ran concretely, so a selected list
    // has a writer no later read can name: abandon_state says so permanently
    // and drops the list from the model.
    ContainerSupport::abandon_state(receiver_object,
        "INDEXED_REMOVE_OBJECT_UNSUPPORTED");
    return NULL;
  }
  if (root_container && (method == "poll"
      || (method == "remove" && arguments.empty()))) {
    oop result_object = handle.get_result_type() == T_OBJECT
        ? handle.get_result<oop>(T_OBJECT) : NULL;
    // poll() answers the head or null and removes the head where there is
    // one -- PEEK and POLL, whose emptiness test is their own, so another
    // state flips both; remove() throws on an empty queue, so its head is a
    // member: READ and REMOVE at 0.
    const bool poll = method == "poll";
    exp_list_t first;
    if (!poll) first.push_back(new ConExpression((jint)0));
    Expression *old = new ContainerExpression(
        "INDEXED", poll ? "PEEK" : "READ", receiver, first,
        ContainerSupport::result_type(
            result_object, handle.get_result_type()),
        ContainerSupport::java_type(
            result_object, handle.get_result_type()));
    ContainerSupport::state_result(handle, old);
    ContainerSupport::attach_result(result_object, old);
    Expression *next = new ContainerExpression(
        "INDEXED", poll ? "POLL" : "REMOVE", receiver, first);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next,
                                    poll ? "POLL" : "REMOVE");
    return old;
  }
  if (method == "clear" && root_container) {
    Expression *next = new ContainerExpression(
        "INDEXED", "CLEAR", receiver, arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    ContainerSupport::publish_state(receiver_object, next, "CLEAR");
    return NULL;
  }
  if (method == "remove" && !root_container && arguments.empty()) {
    // An iterator is never a location of its own, so this is a mutation of
    // the list it walks.  When the walk itself was never modelled -- every
    // read concrete, so iterator()/next() were not admitted and the cursor
    // has no chain at all -- the removal still has what it needs: the list,
    // and the index the iterator last returned, both read from the
    // iterator's own fields before its body cleared them.
    if (ConcolicMngr::ctx->find_container_state(receiver_object) == NULL) {
      oop backing_list = OopUtils::list_of_iterator(receiver_object);
      Expression *base = backing_list == NULL ? NULL
          : ConcolicMngr::ctx->container_state(backing_list, "INDEXED");
      Expression *removed_index =
          ConcolicMngr::ctx->take_view_removal_argument();
      if (backing_list == NULL) {
        ContainerSupport::abandon_state(receiver_object,
            "INDEXED_VIEW_OWNER_MISSING");
        return NULL;
      }
      if (base == NULL || removed_index == NULL) {
        ContainerSupport::abandon_state(receiver_object,
            "INDEXED_VIEW_REMOVED_INDEX_MISSING");
        return NULL;
      }
      exp_list_t removed;
      removed.push_back(removed_index);
      Expression *next = new ContainerExpression(
          "INDEXED", "REMOVE", base, removed);
      ConcolicMngr::ctx->set_container_state(backing_list, next);
      ContainerSupport::publish_state(backing_list, next, "REMOVE");
      return NULL;
    }
    int position = ConcolicMngr::ctx->next_container_removal_position(
        receiver_object);
    Expression *root = ConcolicMngr::ctx->container_state(
        receiver_object, "INDEXED");
    if (root == NULL || position < 0) {
      ContainerSupport::abandon_state(receiver_object,
          "INDEXED_ITERATOR_REMOVE_WITHOUT_NEXT");
      return NULL;
    }
    exp_list_t remove_arguments;
    remove_arguments.push_back(new ConExpression((jint)position));
    Expression *next = new ContainerExpression(
        "INDEXED", "REMOVE", root, remove_arguments);
    ConcolicMngr::ctx->set_container_state(receiver_object, next);
    // The receiver is the cursor, not the list; state_location canonicalizes
    // it to the list it walks, so this is a version of that one location.
    ContainerSupport::publish_state(receiver_object, next, "REMOVE");
    return NULL;
  }

  // element() throws on an empty queue, so its head is a member: READ at 0.
  // peek() is PEEK, the head or null.
  if (method == "element" && arguments.empty()) {
    arguments.push_back(new ConExpression((jint)0));
  }
  if (method == "remove" && !root_container) {
    ContainerSupport::abandon_state(receiver_object,
        "ITERATOR_REMOVE_UNSUPPORTED");
    return NULL;
  }
  if (method == "hasNext" && arguments.empty()) {
    arguments.push_back(new ConExpression((jint)
        ConcolicMngr::ctx->current_container_position(receiver_object)));
    Expression *result = new ContainerExpression(
        "INDEXED", "HAS_NEXT", receiver, arguments, T_BOOLEAN);
    ContainerSupport::state_result(handle, result);
    return result;
  }
  if (method == "nextIndex" && arguments.empty()) {
    return new ConExpression((jint)
        ConcolicMngr::ctx->current_container_index(receiver_object));
  }
  if (method == "listIterator" && !arguments.empty()) {
    ContainerSupport::abandon_state(handle.get_param<oop>(0),
        "INDEXED_LIST_ITERATOR_OFFSET_UNSUPPORTED");
    return NULL;
  }
  const char *operation = method == "get" || method == "element" ? "READ"
      : method == "peek" ? "PEEK"
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
  }
  oop result_object = handle.get_result_type() == T_OBJECT
      ? handle.get_result<oop>(T_OBJECT) : NULL;
  BasicType result_type = ContainerSupport::result_type(
      result_object, handle.get_result_type());
  const std::string result_java_type = ContainerSupport::java_type(
      result_object, handle.get_result_type());

  Expression *result = NULL;
  // Every observation of a selected root list binds to the state it may have
  // observed rather than to whichever state happens to be installed when the
  // helper finishes.  A cursor is an observation too: iterator() inherits the
  // guarded writer choice made here, so the traversal that follows walks the
  // chosen writer's state instead of an unversioned last state - which is the
  // whole point for a size read that is really a traversal count.
  bool observation_admitted = true;
  bool selected_without_value = false;
  bool root_observation = root_container
      && (method == "get" || method == "contains"
          || method == "size" || method == "isEmpty"
          || method == "peek" || method == "element"
          || method == "iterator" || method == "listIterator");
  if (root_observation) {
    ContainerSupport::StateQuery bound = ContainerSupport::query_state(
        receiver_object, "INDEXED", operation, arguments,
        result_type, result_java_type);
    if (bound.expression != NULL) {
      result = bound.expression;
      // A guarded writer choice states no value this replay happened to
      // return: a pin of it would choose the read's writer.
      observation_admitted = false;
    } else if (bound.selected) {
      selected_without_value = true;
    }
  }
  if (result == NULL && !selected_without_value) {
    result = new ContainerExpression(
        "INDEXED", operation, receiver, arguments, result_type,
        result_java_type);
  }
  if (result == NULL) return NULL;
  if (observation_admitted
      && method != "iterator" && method != "listIterator") {
    ContainerSupport::state_result(handle, result);
  }
  if (result_object != NULL) {
    ContainerSupport::attach_result(result_object, result,
        method == "iterator" || method == "listIterator"
            ? receiver_object : NULL);
  }
  return result;
}

#endif // ENABLE_CONCOLIC
