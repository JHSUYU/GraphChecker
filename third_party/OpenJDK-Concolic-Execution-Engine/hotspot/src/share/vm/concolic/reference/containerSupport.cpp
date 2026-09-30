#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "classfile/vmSymbols.hpp"
#include "oops/typeArrayKlass.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/consumerBoundaryExpression.hpp"
#include "concolic/exp/readFromExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicList.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/symbolicSet.hpp"
#include "concolic/reference/symbolicString.hpp"

#include <algorithm>
#include <map>
#include <stdio.h>
#include <string.h>
#include <vector>

const char *ContainerSupport::shape(oop value) {
  if (value == NULL) return NULL;
  if (value->is_array()) return "INDEXED";
  if (value->klass() == NULL || value->klass()->name() == NULL) return NULL;
  Symbol *name = value->klass()->name();
  bool abstract_list = false;
  for (Klass *current = value->klass(); current != NULL;
       current = current->super()) {
    Symbol *current_name = current->name();
    if (current_name != NULL
        && current_name->equals("java/util/AbstractList")) {
      abstract_list = true;
      break;
    }
  }
  if (abstract_list || name->equals("java/util/ArrayDeque")) {
    return "INDEXED";
  }
  if (name->equals("java/util/HashMap")
      || name->equals("java/util/LinkedHashMap")
      || name->equals("java/util/HashSet")
      || name->equals("java/util/LinkedHashSet")) {
    return "ASSOCIATIVE";
  }
  return NULL;
}

bool ContainerSupport::indexed(oop value) {
  const char *value_shape = shape(value);
  return value_shape != NULL && value_shape[0] == 'I';
}

bool ContainerSupport::associative(oop value) {
  const char *value_shape = shape(value);
  return value_shape != NULL && value_shape[0] == 'A';
}

BasicType ContainerSupport::result_type(oop result, BasicType declared) {
  if (result == NULL || declared != T_OBJECT) return declared;
  Symbol *type = result->klass()->name();
  if (type->equals(SymPrimitive<jboolean>::TYPE_NAME)) return T_BOOLEAN;
  if (type->equals(SymPrimitive<jbyte>::TYPE_NAME)) return T_BYTE;
  if (type->equals(SymPrimitive<jchar>::TYPE_NAME)) return T_CHAR;
  if (type->equals(SymPrimitive<jshort>::TYPE_NAME)) return T_SHORT;
  if (type->equals(SymPrimitive<jint>::TYPE_NAME)) return T_INT;
  if (type->equals(SymPrimitive<jlong>::TYPE_NAME)) return T_LONG;
  if (type->equals(SymPrimitive<jfloat>::TYPE_NAME)) return T_FLOAT;
  if (type->equals(SymPrimitive<jdouble>::TYPE_NAME)) return T_DOUBLE;
  return T_OBJECT;
}

std::string ContainerSupport::java_type(oop result, BasicType declared) {
  if (result != NULL
      && result->klass()->name() == vmSymbols::java_lang_String()) {
    return "Ljava/lang/String;";
  }
  return std::string(1, type2char(result_type(result, declared)));
}

bool ContainerSupport::follows_callee_body(const std::string &callee_name) {
  // Methods that only READ the container they are called on.  Their bodies
  // run as written and what they return is concrete: no container relation
  // is claimed for it, and nothing the state holds changes.  Aborting one
  // ended the thread's whole path condition on a logged toString() or a
  // stream over values() (SOLR-18413: LinkedHashMap.getOrDefault in every
  // cluster-state parse, LinkedValues.spliterator in Slice.getReplicas).
  // getNode is HashMap's own lookup, which getOrDefault's body calls.  A
  // mutation nobody modeled still fails closed: it would leave a versioned
  // state incomplete.
  static const char *const READS[] = {
      "<init>", "toString", "hashCode", "equals", "getOrDefault", "getNode",
      "containsValue", "contains", "containsAll", "toArray", "forEach",
      "forEachRemaining", "spliterator", "stream", "parallelStream",
      "indexOf", "lastIndexOf"};
  for (size_t index = 0; index < sizeof(READS) / sizeof(READS[0]); ++index) {
    if (callee_name == READS[index]) return true;
  }
  return false;
}

bool ContainerSupport::claims_state(MethodSymbolizerHandle &handle) {
  Method *callee = handle.get_callee_method();
  if (callee == NULL || callee->is_static()) return false;
  oop receiver = handle.get_param<oop>(0);
  if (receiver == NULL) return false;
  if (ConcolicMngr::ctx->find_container_state(receiver) != NULL
      || ConcolicMngr::ctx->find_stack_slot(
          handle.get_caller_stack_begin_offset()) != NULL) {
    return true;
  }
  if (receiver->is_array()) {
    SymArr *array = ConcolicMngr::ctx->find_sym_array((arrayOop)receiver);
    return array != NULL && array->has_semantic_expression();
  }
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(receiver);
  return instance != NULL && instance->has_semantic_expression();
}

bool ContainerSupport::measures(Expression *length, Expression *state) {
  if (length == NULL || state == NULL) return false;
  ContainerExpression *size = length->as_container_expression();
  return size != NULL && size->get_operation() == "SIZE"
      && size->get_receiver() == state;
}

std::string ContainerSupport::measurement(Expression *length,
                                          Expression *state) {
  if (measures(length, state)) return "MEASURED";
  if (length == NULL) return "LENGTH_NOT_TRACKED";
  ContainerExpression *container = length->as_container_expression();
  if (container == NULL) return "LENGTH_IS_NOT_A_CONTAINER_RELATION";
  if (container->get_operation() != "SIZE") {
    return "LENGTH_IS_" + container->get_operation();
  }
  return "LENGTH_SIZES_ANOTHER_STATE";
}

std::string ContainerSupport::unsupported(const char *category,
                                          MethodSymbolizerHandle &handle) {
  std::string reason(category == NULL ? "UNSPECIFIED" : category);
  reason += ":";
  reason += handle.get_callee_holder_name();
  reason += ".";
  reason += handle.get_callee_name();
  Method *callee = handle.get_callee_method();
  if (callee != NULL && callee->signature() != NULL) {
    reason += callee->signature()->as_C_string();
  }
  return reason;
}

// ---------------------------------------------------------------------------
// Selected whole-container state.
// ---------------------------------------------------------------------------

namespace {

// ---------------------------------------------------------------------------
// Reading a container's concrete members from the heap.
//
// Retention is by value, so the moment a symbolic operand first reaches a
// container the engine has to state what that container already held -- and
// there is nobody to ask.  The Java side used to hand the members over
// (System.snapshotContainerExpression), which made the record depend on
// instrumentation reaching the object before the first symbolic access; the
// race between that offer and the first write is what left bug3's allKeys
// base unstated.  So the VM reads them itself, here.
//
// Only the classes SymMap/SymList/SymSet actually admit are walked, and only
// their backing storage: the views and iterators those sets also name are
// derived from a backing container and are reached through it.  Anything else
// is reported by name rather than guessed at -- see unsupported_class below.
// ---------------------------------------------------------------------------

// One field offset, looked up by name on first use and then cached per klass.
// find_field walks the field stream, and this runs on the first symbolic
// access of every tracked container, so the lookup is done once per (klass,
// field) and never again.
class FieldOffsetCache {
public:
  FieldOffsetCache() {}

  int offset(oop holder, const char *name, const char *signature) {
    if (holder == NULL || holder->klass() == NULL) return -1;
    const Key key(holder->klass(), name);
    std::map<Key, int>::const_iterator found = _offsets.find(key);
    if (found != _offsets.end()) return found->second;
    fieldDescriptor fd;
    const int resolved =
        OopUtils::get_fd_by_name(holder, name, signature, fd) == NULL
            ? -1 : fd.offset();
    _offsets[key] = resolved;
    return resolved;
  }

private:
  struct Key {
    Klass *klass;
    const char *name;
    Key(Klass *k, const char *n) : klass(k), name(n) {}
    bool operator<(const Key &other) const {
      if (klass != other.klass) return klass < other.klass;
      return strcmp(name, other.name) < 0;
    }
  };
  std::map<Key, int> _offsets;
};

FieldOffsetCache *field_offsets() {
  // Function-local so it is constructed on first use and never during static
  // initialisation; the engine is single-session and this is only reached
  // with a context, which serialises it well enough for a cache whose worst
  // case is a redundant lookup.
  static FieldOffsetCache cache;
  return &cache;
}

bool klass_name_is(oop obj, const char *name) {
  if (obj == NULL || obj->klass() == NULL || obj->klass()->name() == NULL) {
    return false;
  }
  return obj->klass()->name()->equals(name, (int) strlen(name));
}

bool read_hash_map(oop map, std::vector<oop> *keys, std::vector<oop> *values);

// HashMap/LinkedHashMap: table is a Node[]; each bin is a chain linked by
// `next`.  A treeified bin holds TreeNodes, and TreeNode extends
// LinkedHashMap.Entry extends HashMap.Node, so `next` still threads every
// member of the bin -- one chain walk covers both bin kinds and no red-black
// traversal is needed.
bool read_hash_map(oop map, std::vector<oop> *keys, std::vector<oop> *values) {
  const int table_offset =
      field_offsets()->offset(map, "table", "[Ljava/util/HashMap$Node;");
  if (table_offset < 0) return false;
  oop table = map->obj_field(table_offset);
  // A HashMap that has never been written has a null table.  That is an
  // exactly empty map, not an unreadable one.
  if (table == NULL) return true;
  if (!table->is_objArray()) return false;
  objArrayOop bins = objArrayOop(table);
  for (int bin = 0; bin < bins->length(); ++bin) {
    oop node = bins->obj_at(bin);
    // Bounded by the table length times the longest chain; a corrupted cycle
    // would otherwise spin here.
    int guard = 0;
    while (node != NULL && guard++ < (1 << 20)) {
      const int key_offset =
          field_offsets()->offset(node, "key", "Ljava/lang/Object;");
      const int value_offset =
          field_offsets()->offset(node, "value", "Ljava/lang/Object;");
      const int next_offset =
          field_offsets()->offset(node, "next", "Ljava/util/HashMap$Node;");
      if (key_offset < 0 || value_offset < 0 || next_offset < 0) return false;
      keys->push_back(node->obj_field(key_offset));
      values->push_back(node->obj_field(value_offset));
      node = node->obj_field(next_offset);
    }
  }
  return true;
}

// HashSet/LinkedHashSet are a HashMap whose values are a shared placeholder;
// the members are its keys, and an ASSOCIATIVE shape is not what a set reads
// back as, so the members are reported as values.
bool read_hash_set(oop set, std::vector<oop> *values) {
  const int map_offset =
      field_offsets()->offset(set, "map", "Ljava/util/HashMap;");
  if (map_offset < 0) return false;
  oop map = set->obj_field(map_offset);
  if (map == NULL) return true;
  std::vector<oop> keys;
  std::vector<oop> ignored;
  if (!read_hash_map(map, &keys, &ignored)) return false;
  for (size_t index = 0; index < keys.size(); ++index) {
    values->push_back(keys[index]);
  }
  return true;
}

// ArrayList: elementData is the backing array and `size` is how much of it is
// live.  The array is usually longer than the list; reading past `size` would
// state stale members a clear() left behind.
bool read_array_list(oop list, std::vector<oop> *values) {
  const int data_offset =
      field_offsets()->offset(list, "elementData", "[Ljava/lang/Object;");
  const int size_offset = field_offsets()->offset(list, "size", "I");
  if (data_offset < 0 || size_offset < 0) return false;
  oop data = list->obj_field(data_offset);
  const int size = list->int_field(size_offset);
  if (data == NULL) return size == 0;
  if (!data->is_objArray()) return false;
  objArrayOop elements = objArrayOop(data);
  if (size < 0 || size > elements->length()) return false;
  for (int index = 0; index < size; ++index) {
    values->push_back(elements->obj_at(index));
  }
  return true;
}

// ArrayDeque: a circular buffer between head and tail, so iteration order is
// head..tail modulo the capacity rather than 0..length.
bool read_array_deque(oop deque, std::vector<oop> *values) {
  const int data_offset =
      field_offsets()->offset(deque, "elements", "[Ljava/lang/Object;");
  const int head_offset = field_offsets()->offset(deque, "head", "I");
  const int tail_offset = field_offsets()->offset(deque, "tail", "I");
  if (data_offset < 0 || head_offset < 0 || tail_offset < 0) return false;
  oop data = deque->obj_field(data_offset);
  if (data == NULL) return true;
  if (!data->is_objArray()) return false;
  objArrayOop elements = objArrayOop(data);
  const int capacity = elements->length();
  if (capacity == 0) return true;
  const int head = deque->int_field(head_offset);
  const int tail = deque->int_field(tail_offset);
  if (head < 0 || head >= capacity || tail < 0 || tail >= capacity) {
    return false;
  }
  for (int index = head; index != tail; index = (index + 1) % capacity) {
    values->push_back(elements->obj_at(index));
  }
  return true;
}

} // anonymous namespace

bool ContainerSupport::read_concrete_members(oop container,
                                             std::vector<oop> *keys,
                                             std::vector<oop> *values,
                                             const char **unsupported_class) {
  if (unsupported_class != NULL) *unsupported_class = NULL;
  if (container == NULL || keys == NULL || values == NULL) return false;

  if (container->is_array()) {
    if (!container->is_objArray()) {
      // A primitive array's elements are read by the element-store path, not
      // here; nothing about its identity is unreadable, so this is not an
      // unsupported class.
      return true;
    }
    objArrayOop elements = objArrayOop(container);
    for (int index = 0; index < elements->length(); ++index) {
      values->push_back(elements->obj_at(index));
    }
    return true;
  }

  if (klass_name_is(container, "java/util/HashMap")
      || klass_name_is(container, "java/util/LinkedHashMap")) {
    return read_hash_map(container, keys, values);
  }
  if (klass_name_is(container, "java/util/HashSet")
      || klass_name_is(container, "java/util/LinkedHashSet")) {
    return read_hash_set(container, values);
  }
  if (klass_name_is(container, "java/util/ArrayList")) {
    return read_array_list(container, values);
  }
  if (klass_name_is(container, "java/util/ArrayDeque")) {
    return read_array_deque(container, values);
  }

  // Admitted by the model but not walked here.  Named, never guessed at: a
  // reader that could not tell "held nothing" from "this engine cannot read
  // it" would solve with an empty container.
  if (unsupported_class != NULL && container->klass() != NULL
      && container->klass()->name() != NULL) {
    *unsupported_class = container->klass()->name()->as_C_string();
  }
  return false;
}

int ContainerSupport::install_receiver_snapshot(
    oop container, const char *shape, bool *truncated,
    const char **unsupported_class) {
  if (truncated != NULL) *truncated = false;
  if (unsupported_class != NULL) *unsupported_class = NULL;
  if (container == NULL || shape == NULL || ConcolicMngr::ctx == NULL) {
    return -1;
  }

  std::vector<oop> keys;
  std::vector<oop> values;
  if (!read_concrete_members(container, &keys, &values, unsupported_class)) {
    return -1;
  }

  const bool associative = strcmp(shape, "ASSOCIATIVE") == 0;
  if (associative && keys.size() != values.size()) return -1;
  const int entries = (int) values.size();

  // The same bound the Java-driven offer obeyed.  Past it the container keeps
  // its opaque root and the refusal is stated: "held something this engine
  // declined to state" is a different fact from "held nothing", and a reader
  // that cannot tell them apart would solve with an empty container.
  if (entries > ConcolicMngr::initialSnapshotMaxEntries()) {
    ConcolicMngr::ctx->container_state(container, shape);
    if (truncated != NULL) *truncated = true;
    return -2;
  }

  exp_list_t no_arguments;
  Expression *root = ConcolicMngr::ctx->container_state(container, shape);
  if (root == NULL) return -1;
  Expression *state =
      new ContainerExpression(shape, "SNAPSHOT_BASE", root, no_arguments);
  for (int index = 0; index < entries; ++index) {
    exp_list_t arguments;
    if (associative) {
      arguments.push_back(concrete_value(keys[index]));
      arguments.push_back(concrete_value(values[index]));
    } else {
      arguments.push_back(concrete_value(values[index]));
    }
    state = new ContainerExpression(
        shape, associative ? "PUT" : "APPEND", state, arguments);
  }
  ConcolicMngr::ctx->set_container_state(container, state);
  return entries;
}

int ContainerSupport::snapshot_entry_count(Expression *state) {
  int entries = 0;
  Expression *cursor = state;
  while (cursor != NULL) {
    ContainerExpression *relation = cursor->as_container_expression();
    if (relation == NULL) return -1;
    const std::string &operation = relation->get_operation();
    if (operation == "SNAPSHOT_BASE") return entries;
    if (operation != "PUT" && operation != "APPEND") return -1;
    ++entries;
    cursor = relation->get_receiver();
  }
  return -1;
}

// A recorded chain is finite and strictly descends, so this bound only keeps
// a corrupted state from spinning; hitting it is answered as "not a chain
// this engine built", which leaves the contents unknown.
static const int CONTAINER_CHAIN_DEPTH_LIMIT = 1 << 20;

bool ContainerSupport::states_initial_content(Expression *state) {
  Expression *cursor = state;
  for (int depth = 0; depth < CONTAINER_CHAIN_DEPTH_LIMIT; ++depth) {
    if (cursor == NULL) return false;
    ContainerExpression *relation = cursor->as_container_expression();
    if (relation == NULL) return false;
    const std::string &operation = relation->get_operation();
    if (operation == "SNAPSHOT_BASE") return true;
    if (operation == "STATE") return false;
    cursor = relation->get_receiver();
  }
  return false;
}

bool ContainerSupport::recorded_history(
    Expression *state, Expression **root,
    std::vector<ContainerExpression *> *history) {
  if (root == NULL || history == NULL) return false;
  history->clear();
  Expression *cursor = state;
  for (int depth = 0; depth < CONTAINER_CHAIN_DEPTH_LIMIT; ++depth) {
    if (cursor == NULL) return false;
    ContainerExpression *relation = cursor->as_container_expression();
    if (relation == NULL) return false;
    if (relation->get_operation() == "STATE") {
      *root = cursor;
      // Collected newest first; a replay of the history has to walk it in
      // the order the recorder watched it happen.
      std::reverse(history->begin(), history->end());
      return true;
    }
    if (relation->get_operation() == "SNAPSHOT_BASE") return false;
    history->push_back(relation);
    cursor = relation->get_receiver();
  }
  return false;
}

bool ContainerSupport::undo_indexed_history(
    const std::vector<ContainerExpression *> &history, int member_count,
    std::vector<int> *base_members) {
  if (base_members == NULL || member_count < 0) return false;
  base_members->clear();
  base_members->reserve((size_t) member_count);
  for (int index = 0; index < member_count; ++index) {
    base_members->push_back(index);
  }
  // Undone newest first: each step's working set is exactly the content the
  // container held immediately after the mutation being undone, which is the
  // state that mutation's own recorded position addresses.
  for (size_t step = history.size(); step > 0; --step) {
    ContainerExpression *relation = history[step - 1];
    if (relation == NULL || relation->get_shape() != "INDEXED") return false;
    const std::string &operation = relation->get_operation();
    if (operation == "APPEND") {
      if (base_members->empty()) return false;
      base_members->pop_back();
      continue;
    }
    if (operation != "INSERT") return false;
    const exp_list_t &arguments = relation->get_arguments();
    if (arguments.empty() || arguments[0] == NULL) return false;
    jint position = 0;
    if (!arguments[0]->concrete_int_value(&position)) return false;
    if (position < 0 || (size_t) position >= base_members->size()) {
      return false;
    }
    base_members->erase(base_members->begin() + position);
  }
  return true;
}

bool ContainerSupport::whole_state_selectable(oop container) {
  if (container == NULL || container->is_array()) return false;
  if (shape(container) == NULL) return false;
  if (container->klass() == NULL || container->klass()->name() == NULL) {
    return false;
  }
  ResourceMark rm;
  const std::string name(container->klass()->name()->as_C_string());
  return SymList::target(name) || SymMap::target(name)
      || SymSet::target(name);
}

SharedFieldVersions::Location ContainerSupport::state_location(oop container) {
  SharedFieldVersions::Location location;
  if (container == NULL || ConcolicMngr::ctx == NULL) return location;
  sym_rid_t owner = ConcolicMngr::ctx->canonical_container_id(container);
  if (owner == NULL_SYM_RID) return location;
  return SharedFieldVersions::Location(
      owner, SharedFieldVersions::SLOT_WHOLE_STATE,
      SharedFieldVersions::LOC_MAP_STATE);
}

void ContainerSupport::state_base_before_operation(oop container) {
  if (container == NULL || ConcolicMngr::ctx == NULL) return;
  if (shape(container) == NULL) return;

  // Called from a model's invoke hook: the arguments are in hand and the
  // callee body has NOT run, so the receiver still holds exactly the contents
  // the log must begin from.  This is the only place a write-first container
  // can be read honestly -- by the time the finish hook publishes the
  // mutation, the concrete put has already happened and a walk would state a
  // base that includes the entry being written.
  SharedFieldVersions::Location existing = state_location(container);
  if (existing.is_valid() && SharedFieldVersions::is_tracked(existing)) return;

  SharedFieldVersions::InitialSnapshot snapshot;
  snapshot_for_receiver(container, &snapshot, true);

  // state_location needs the container shadow, which the walk above mints.
  SharedFieldVersions::Location location = state_location(container);
  if (!location.is_valid()) return;
  if (SharedFieldVersions::is_tracked(location)) return;
  Expression *base = ConcolicMngr::ctx->find_container_state(container);
  if (base == NULL) return;
  SharedFieldVersions::publish_initial(
      location, base, SharedFieldVersions::ConcreteBits(), snapshot);
}

void ContainerSupport::snapshot_for_receiver(
    oop container, SharedFieldVersions::InitialSnapshot *out, bool receiver_is_base) {
  if (out == NULL) return;
  *out = SharedFieldVersions::InitialSnapshot();
  if (container == NULL) return;

  // The walk reads the container as it is *now*.  That is the base only when
  // nothing has been applied to it yet -- which is true on the first symbolic
  // READ and false on a first symbolic WRITE, because the concrete mutation
  // has already run by the time the model publishes its relation.  Counting
  // then would overstate the base by the very entry being written, so the
  // refusal is stated instead of a wrong number.
  if (!receiver_is_base) {
    out->unsupported_class = "MUTATED_BEFORE_FIRST_READ";
    return;
  }

  const char *container_shape = shape(container);
  if (container_shape == NULL) {
    out->unsupported_class = "NO_MODELLED_SHAPE";
    return;
  }
  bool truncated = false;
  const char *unsupported = NULL;
  const int entries =
      install_receiver_snapshot(container, container_shape, &truncated,
                                &unsupported);
  if (entries >= 0) {
    out->stated = true;
    out->entries = entries;
    return;
  }
  if (truncated) {
    // Over the bound: the container kept its opaque root and the count is
    // still worth stating -- "held more than this engine will write down" is
    // a different fact from "held nothing".
    out->truncated = true;
    return;
  }
  out->unsupported_class =
      unsupported == NULL ? "UNREADABLE_CONTAINER" : unsupported;
}

bool ContainerSupport::guarded_mutation(const std::string &callee) {
  if (ConcolicMngr::ctx == NULL) return false;
  // Control dependence, asked of the plan, not "after a branch": the call
  // site's own method must be one whose stores the plan says are
  // control-dependent, and one of that method's guard branches must have
  // decided something symbolic on this path.
  if (!SharedFieldVersions::guarded_store_admitted()) return false;
  return callee == "put" || callee == "remove" || callee == "clear"
      || callee == "add" || callee == "offer" || callee == "set";
}

jlong ContainerSupport::publish_state(oop container, Expression *new_state,
                                      const char *operation) {
  // A container state expression exists only because something symbolic went
  // into the container, so reaching here at all is the by-value condition:
  // the state is kept, and starts this container's log if it is the first.
  if (new_state == NULL) return 0;
  SharedFieldVersions::Location location = state_location(container);
  if (!location.is_valid()) return 0;
  // Start the log at the state this mutation extends, not at the mutation.
  // A container relation resolves as base + PUT/REMOVE_IF/..., so a log whose
  // first entry is already a PUT leaves that PUT's receiver unresolvable --
  // which is what retention by value did to bug3's allKeys base until this
  // existed.  The receiver of the relation being published *is* that base,
  // and publish_initial is a no-op once the location is tracked.
  if (!SharedFieldVersions::is_tracked(location)) {
    ContainerExpression *relation = new_state->as_container_expression();
    Expression *base = relation == NULL ? NULL : relation->get_receiver();
    if (base != NULL) {
      // State what the container already held, from the container itself.
      // The base is published with that fact attached, so a relation chain
      // resolves against recorded contents instead of an opaque root.  A
      // class the engine cannot walk is published as a stated refusal, never
      // as an empty container.
      SharedFieldVersions::InitialSnapshot snapshot;
      snapshot_for_receiver(container, &snapshot, false);
      SharedFieldVersions::publish_initial(
          location, base, SharedFieldVersions::ConcreteBits(), snapshot);
    }
  }
  // The publishing task already names the merged local path case.  Copying
  // the complete PC into every PUT/REMOVE version is both redundant and
  // prohibitively large in service loops; the Composer binds read-from arms
  // to that task's case selector instead.  A whole state is not one word,
  // so the version states none.
  return SharedFieldVersions::publish_value(
      location, new_state, SharedFieldVersions::ConcreteBits(), NULL, true,
      SharedFieldVersions::VERSION_STATE, operation);
}

void ContainerSupport::abandon_state(oop container,
                                     const std::string &reason) {
  if (container == NULL || ConcolicMngr::ctx == NULL) return;
  mark_state_gap(container, reason.c_str());
  ConcolicMngr::ctx->forget_container_state(container);
}

bool ContainerSupport::mark_state_gap(oop container, const char *reason) {
  if (!SharedFieldVersions::has_carriers()) return false;
  SharedFieldVersions::Location location = state_location(container);
  return SharedFieldVersions::mark_writer_set_incomplete(location, reason);
}

ContainerSupport::StateQuery ContainerSupport::query_state(
    oop container, const char *shape, const char *operation,
    const exp_list_t &arguments, BasicType result_type,
    const std::string &java_type) {
  StateQuery answer;
  if (operation == NULL) return answer;
  const std::string type_name = java_type.empty()
      ? std::string(1, type2char(result_type)) : java_type;

  SharedFieldVersions::Location location = state_location(container);
  if (!location.is_valid()) return answer;
  if (!SharedFieldVersions::is_tracked(location)) {
    // First symbolic access of an untracked container, and it is a read: the
    // value it answers depends on what the container already holds, so the
    // log starts here with that content stated.  The receiver has not been
    // mutated by this operation, so walking it now reads exactly the base.
    SharedFieldVersions::InitialSnapshot snapshot;
    snapshot_for_receiver(container, &snapshot, true);
    Expression *base = ConcolicMngr::ctx->find_container_state(container);
    if (base == NULL) return answer;
    SharedFieldVersions::publish_initial(
        location, base, SharedFieldVersions::ConcreteBits(), snapshot);
    if (!SharedFieldVersions::is_tracked(location)) return answer;
  }
  answer.selected = true;

  SharedFieldVersions::ReadPlan plan;
  if (!SharedFieldVersions::plan_read(
          location, SharedFieldVersions::ConcreteBits(), &plan)) {
    return answer;
  }

  // An untracked writer produces an open coverage result, not a symbolic map
  // state.  plan_read has already recorded that gap; keep the concrete query
  // path and do not manufacture a state the solver can choose.
  if (plan.observed.value == NULL) return answer;

  // The query applied to the observed writer's state, not the state.  This is
  // the whole difference between a scalar read and a container one; everything
  // else about the node is the shared shape
  // SharedFieldVersions::build_read_from writes.
  answer.expression = SharedFieldVersions::build_read_from(
      plan, location, type_name,
      new ContainerExpression(shape, operation, plan.observed.value,
                              arguments, result_type, type_name),
      ReturnedValue());
  return answer;
}

// Naming an object is not making it symbolic.  This function answers what a
// reference *is*, for a recording that has to state what it read; it used to
// answer by allocating a shadow, which is the thing that turns an object's
// own loads into symbolic ones -- CONCOLIC_ALOAD gates on
// `arrObj->is_symbolic()`, so naming one array-valued field put every element
// load of that array on the container path, with a state root, a position
// constraint and a path condition per load.  On 17960's seed that was 57 MB of
// expressions and 39 GB of RSS for a recording that had only been asked for a
// name.  So an object with no shadow is named and left alone
// (`name_reference`), and one that already has a shadow answers exactly as
// before.
Expression *ContainerSupport::concrete_value(oop value) {
  if (value == NULL) return SymbolExpression::get(Sym_NULL);
  // The session heap, not the thread context: a thread outside every region
  // names what it stores into a tracked location too (D4).
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  if (value->is_array()) {
    SymArr *array = heap->find_sym_array((arrayOop)value);
    if (array != NULL) {
      return array->get_ref_exp() != NULL
          ? array->get_ref_exp()
          : static_cast<Expression *>(new ArraySymbolExp(
                array->get_sym_rid(), array->get_version(), T_OBJECT));
    }
    // A named array's version is 0, which is the version a shadow allocated
    // for it now would report: an unshadowed array has no recorded mutation
    // to have moved it on.
    sym_rid_t named = heap->name_reference(value);
    return named == NULL_SYM_RID
        ? static_cast<Expression *>(new PlaceHolderSymbolExp(value))
        : static_cast<Expression *>(
              new ArraySymbolExp(named, 0, T_OBJECT));
  }
  Symbol *type = value->klass()->name();
  if (type->equals(SymPrimitive<jboolean>::TYPE_NAME))
    return SymPrimitive<jboolean>::get_exp_of(value);
  if (type->equals(SymPrimitive<jbyte>::TYPE_NAME))
    return SymPrimitive<jbyte>::get_exp_of(value);
  if (type->equals(SymPrimitive<jchar>::TYPE_NAME))
    return SymPrimitive<jchar>::get_exp_of(value);
  if (type->equals(SymPrimitive<jshort>::TYPE_NAME))
    return SymPrimitive<jshort>::get_exp_of(value);
  if (type->equals(SymPrimitive<jint>::TYPE_NAME))
    return SymPrimitive<jint>::get_exp_of(value);
  if (type->equals(SymPrimitive<jlong>::TYPE_NAME))
    return SymPrimitive<jlong>::get_exp_of(value);
  if (type->equals(SymPrimitive<jfloat>::TYPE_NAME))
    return SymPrimitive<jfloat>::get_exp_of(value);
  if (type->equals(SymPrimitive<jdouble>::TYPE_NAME))
    return SymPrimitive<jdouble>::get_exp_of(value);
  if (type == vmSymbols::java_lang_String())
    return SymString::get_exp_of(value);
  SymInstance *identity = heap->find_sym_inst(value);
  if (identity != NULL) return identity->get_or_create_ref_exp(value);
  // Named, not shadowed.  InstanceSymbolExp reads the identity straight out
  // of the header, so this is the same spelling the object's own shadow would
  // give it if it ever gets one -- the allocators adopt a named id.
  sym_rid_t named = heap->name_reference(value);
  return named == NULL_SYM_RID
      ? static_cast<Expression *>(new PlaceHolderSymbolExp(value))
      : static_cast<Expression *>(new InstanceSymbolExp(value));
}

Expression *ContainerSupport::semantic_value(oop value) {
  if (value == NULL || ConcolicMngr::ctx == NULL) return NULL;
  if (value->is_array()) {
    SymArr *array = ConcolicMngr::ctx->find_sym_array((arrayOop)value);
    return array != NULL && array->has_semantic_expression()
        ? array->get_ref_exp() : NULL;
  }
  SymInstance *instance = ConcolicMngr::ctx->find_sym_inst(value);
  return instance != NULL && instance->has_semantic_expression()
      ? instance->get_ref_exp() : NULL;
}

Expression *ContainerSupport::concrete_result(
    MethodSymbolizerHandle &handle) {
  BasicType type = handle.get_result_type();
  switch (type) {
    case T_BOOLEAN:
      return new ConExpression(
          (jboolean)handle.get_result<jint>(T_BOOLEAN));
    case T_BYTE:
      return new ConExpression((jbyte)handle.get_result<jint>(T_BYTE));
    case T_CHAR:
      return new ConExpression((jchar)handle.get_result<jint>(T_CHAR));
    case T_SHORT:
      return new ConExpression((jshort)handle.get_result<jint>(T_SHORT));
    case T_INT:
      return new ConExpression(handle.get_result<jint>(T_INT));
    case T_LONG:
      return new ConExpression(handle.get_result<jlong>(T_LONG));
    case T_FLOAT:
      return new ConExpression(handle.get_result<jfloat>(T_FLOAT));
    case T_DOUBLE:
      return new ConExpression(handle.get_result<jdouble>(T_DOUBLE));
    case T_OBJECT:
    case T_ARRAY:
      return concrete_value(handle.get_result<oop>(type));
    default:
      return NULL;
  }
}

void ContainerSupport::constrain_result(
    MethodSymbolizerHandle &handle, Expression *expression) {
  if (expression == NULL) return;
  Expression *concrete = concrete_result(handle);
  if (concrete == NULL) return;
  ConcolicMngr::record_path_condition(
      new OpSymExpression(expression, concrete, op_eq, true));
}

void ContainerSupport::constrain_position(
    const char *shape, Expression *state, Expression *position,
    bool allow_end) {
  if (state == NULL || position == NULL) return;
  // A concrete position constrains nothing by itself: `k >= 0` is a constant
  // the run already decided, and so is `k < SIZE` when the size is constant
  // too -- a Java array's length.  hdfs-17960's FSImageSaver scanned the
  // NameNode's inode map, a LightWeightGSet whose ~1M-bucket array an earlier
  // region had stored into under symbolic guards, and recorded both facts
  // per bucket: native RSS went from 300 MB to 27 GB in a minute and the
  // kernel killed the JVM.
  jint concrete = 0;
  const bool constant_position = position->concrete_int_value(&concrete);
  if (!constant_position) {
    ConcolicMngr::record_path_condition(new OpSymExpression(
        position, new ConExpression((jint)0), op_ge, true));
  }
  ContainerExpression *relation = state->as_container_expression();
  if (constant_position && relation != NULL
      && relation->has_constant_size()) {
    return;
  }
  exp_list_t no_arguments;
  Expression *size =
      new ContainerExpression(shape, "SIZE", state, no_arguments, T_INT);
  ConcolicMngr::record_path_condition(new OpSymExpression(
      position, size, allow_end ? op_le : op_lt, true));
}

bool ContainerSupport::recorded_element(arrayOop heap_array, SymArr *array,
                                        Expression *state,
                                        Expression *position, jint index,
                                        Expression **stored) {
  jint at = index;
  if (array == NULL || state == NULL || !array->named()
      || array->has_semantic_expression()
      || (position != NULL && !position->concrete_int_value(&at))) {
    return false;
  }
  // The state itself, not what a consumer boundary around it delegates to:
  // the boundary is the cross-process provenance of every element.
  ContainerExpression *relation = state->as_container_expression();
  ElementWord word;
  if (relation != state || !relation->stored_at(at, stored, &word)) {
    return false;
  }
  if (*stored == NULL || !word.stated) return true;
  // The element must still hold what the write left: a write no hook saw
  // (JNI, a muted store) made the log stale.  The heap then decides, as a
  // concrete read, and the container's log, if it has one, is marked
  // incomplete by name -- detected, never silently the stale value.
  jlong held = 0;
  if (heap_array->is_objArray()) {
    oop element = objArrayOop(heap_array)->obj_at(at);
    held = element == NULL ? 0 : (jlong) element->get_sym_rid();
  } else {
    held = SharedFieldVersions::element_bits(heap_array, at).bits;
  }
  if (held != word.bits) {
    mark_state_gap(heap_array, "UNHOOKED_ELEMENT_WRITE");
    *stored = NULL;
    return true;
  }
  // A concrete store left exactly the heap's word: the element is concrete
  // (a constant as an expression would read as symbolic downstream).
  if (!word.symbolic) *stored = NULL;
  return true;
}

void ContainerSupport::attach_result(oop result, Expression *expression,
                                     oop owner) {
  if (result == NULL || expression == NULL) return;
  if (result->is_array()) {
    SymArr *array =
        ConcolicMngr::ctx->get_or_alloc_sym_array((arrayOop)result);
    if (array != NULL) array->set_ref_exp(expression);
    return;
  }
  // A JVM-wide object keeps no expression; it rides the result slot (item 5).
  SymInstance *instance = jvm_shared_object(result) ? NULL
      : ConcolicMngr::ctx->get_or_alloc_sym_inst(result);
  if (instance == NULL) return;
  instance->set_ref_exp(expression);
  instance->enable_demand_symbolic_fields();
  if (owner != NULL) {
    ConcolicMngr::ctx->alias_container(result, owner);
  }
}

void ContainerSupport::publish_attached_state(oop destination,
                                              Expression *attached) {
  if (destination == NULL || attached == NULL) return;
  SharedFieldVersions::Location location = state_location(destination);
  if (location.is_valid()) {
    SharedFieldVersions::publish_value(
        location, attached, SharedFieldVersions::ConcreteBits(), NULL, true,
        SharedFieldVersions::VERSION_STATE, "ATTACH");
  }
  if (!destination->is_array()) return;
  // An array's tracked elements are locations of their own, read per
  // element: each gets the attached state's element as a version, with the
  // word the heap holds.
  arrayOop array = arrayOop(destination);
  std::vector<int> slots;
  SharedFieldVersions::tracked_elements(array->get_sym_rid(), 0,
                                        array->length(), &slots);
  const BasicType element_type = array->is_typeArray()
      ? TypeArrayKlass::cast(array->klass())->element_type() : T_OBJECT;
  for (size_t index = 0; index < slots.size(); ++index) {
    exp_list_t position;
    position.push_back(new ConExpression((jint) slots[index]));
    SharedFieldVersions::publish_held(
        SharedFieldVersions::Location(array->get_sym_rid(), slots[index],
            SharedFieldVersions::LOC_ARRAY_ELEMENT),
        SharedFieldVersions::Cell(array, element_type),
        new ContainerExpression("INDEXED", "READ", attached, position,
                                element_type),
        NULL, SharedFieldVersions::VERSION_WRITE);
  }
}

#endif  // ENABLE_CONCOLIC
