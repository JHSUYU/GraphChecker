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
#include "concolic/reference/symbolicString.hpp"
#include "oops/fieldStreams.hpp"

#include <pthread.h>

#include <algorithm>
#include <map>
#include <stdio.h>
#include <string.h>
#include <vector>

namespace {

bool klass_name_is(Klass *klass, const char *name) {
  return klass != NULL && klass->name() != NULL
      && klass->name()->equals(name, (int) strlen(name));
}

bool klass_name_is(oop obj, const char *name) {
  return obj != NULL && klass_name_is(obj->klass(), name);
}

// The classes whose contract this engine models, by exact name; see
// ContainerSupport::Capability.
ContainerSupport::Capability exact_capability(Klass *klass) {
  if (klass_name_is(klass, "java/util/HashMap")
      || klass_name_is(klass, "java/util/LinkedHashMap")) {
    return ContainerSupport::CAPABILITY_HASH_MAP;
  }
  if (klass_name_is(klass, "java/util/concurrent/ConcurrentHashMap")) {
    return ContainerSupport::CAPABILITY_CONCURRENT_MAP;
  }
  if (klass_name_is(klass, "java/util/Hashtable")) {
    return ContainerSupport::CAPABILITY_HASHTABLE;
  }
  if (klass_name_is(klass, "java/util/HashSet")
      || klass_name_is(klass, "java/util/LinkedHashSet")) {
    return ContainerSupport::CAPABILITY_HASH_SET;
  }
  if (klass_name_is(klass, "java/util/ArrayDeque")) {
    return ContainerSupport::CAPABILITY_INDEXED;
  }
  return ContainerSupport::CAPABILITY_NONE;
}

// One backing field of a JDK view, iterator, entry or wrapper: the class it
// is declared on and its name and descriptor.  A walk follows these until it
// reaches a modeled container.
struct BackingField {
  const char *klass;
  const char *name;
  const char *descriptor;
};

const BackingField BACKING_FIELDS[] = {
  {"java/util/HashMap$KeySet", "this$0", "Ljava/util/HashMap;"},
  {"java/util/HashMap$Values", "this$0", "Ljava/util/HashMap;"},
  {"java/util/HashMap$EntrySet", "this$0", "Ljava/util/HashMap;"},
  {"java/util/HashMap$KeyIterator", "this$0", "Ljava/util/HashMap;"},
  {"java/util/HashMap$ValueIterator", "this$0", "Ljava/util/HashMap;"},
  {"java/util/HashMap$EntryIterator", "this$0", "Ljava/util/HashMap;"},
  {"java/util/LinkedHashMap$LinkedKeySet", "this$0",
   "Ljava/util/LinkedHashMap;"},
  {"java/util/LinkedHashMap$LinkedValues", "this$0",
   "Ljava/util/LinkedHashMap;"},
  {"java/util/LinkedHashMap$LinkedEntrySet", "this$0",
   "Ljava/util/LinkedHashMap;"},
  {"java/util/LinkedHashMap$LinkedKeyIterator", "this$0",
   "Ljava/util/LinkedHashMap;"},
  {"java/util/LinkedHashMap$LinkedValueIterator", "this$0",
   "Ljava/util/LinkedHashMap;"},
  {"java/util/LinkedHashMap$LinkedEntryIterator", "this$0",
   "Ljava/util/LinkedHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$KeySetView", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$ValuesView", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$EntrySetView", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$KeyIterator", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$ValueIterator", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$EntryIterator", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/concurrent/ConcurrentHashMap$MapEntry", "map",
   "Ljava/util/concurrent/ConcurrentHashMap;"},
  {"java/util/Hashtable$KeySet", "this$0", "Ljava/util/Hashtable;"},
  {"java/util/Hashtable$ValueCollection", "this$0", "Ljava/util/Hashtable;"},
  {"java/util/Hashtable$EntrySet", "this$0", "Ljava/util/Hashtable;"},
  {"java/util/Hashtable$Enumerator", "this$0", "Ljava/util/Hashtable;"},
  {"java/util/Collections$UnmodifiableMap", "m", "Ljava/util/Map;"},
  {"java/util/Collections$UnmodifiableCollection", "c",
   "Ljava/util/Collection;"},
  {"java/util/Collections$UnmodifiableSet", "c", "Ljava/util/Collection;"},
  {"java/util/Collections$UnmodifiableMap$UnmodifiableEntrySet", "c",
   "Ljava/util/Collection;"},
  {"java/util/Collections$SynchronizedMap", "m", "Ljava/util/Map;"},
  {"java/util/Collections$SynchronizedCollection", "c",
   "Ljava/util/Collection;"},
  {"java/util/Collections$SynchronizedSet", "c", "Ljava/util/Collection;"},
  {"java/util/Collections$CheckedMap", "m", "Ljava/util/Map;"},
  {"java/util/Collections$CheckedCollection", "c", "Ljava/util/Collection;"},
  {"java/util/Collections$CheckedSet", "c", "Ljava/util/Collection;"},
};
const size_t BACKING_FIELD_COUNT =
    sizeof(BACKING_FIELDS) / sizeof(BACKING_FIELDS[0]);

const BackingField *backing_field_of(Klass *klass) {
  for (size_t index = 0; index < BACKING_FIELD_COUNT; ++index) {
    if (klass_name_is(klass, BACKING_FIELDS[index].klass)) {
      return &BACKING_FIELDS[index];
    }
  }
  return NULL;
}

// One field offset, looked up by name on first use and then cached per
// klass.  The lookup walks the klass's field streams comparing names -- no
// symbol is made, so no SymbolTable lock is taken -- and the cache has its
// own leaf mutex: it is asked by every thread, some of them under a stripe.
class FieldOffsetCache {
public:
  FieldOffsetCache() { pthread_mutex_init(&_mutex, NULL); }

  int offset(oop holder, const char *name, const char *signature) {
    if (holder == NULL || holder->klass() == NULL) return -1;
    const Key key(holder->klass(), name);
    pthread_mutex_lock(&_mutex);
    std::map<Key, int>::const_iterator found = _offsets.find(key);
    const bool cached = found != _offsets.end();
    const int known = cached ? found->second : -1;
    pthread_mutex_unlock(&_mutex);
    if (cached) return known;
    const int resolved = lookup(holder->klass(), name, signature);
    pthread_mutex_lock(&_mutex);
    _offsets[key] = resolved;
    pthread_mutex_unlock(&_mutex);
    return resolved;
  }

private:
  static int lookup(Klass *klass, const char *name, const char *signature) {
    for (Klass *current = klass; current != NULL;
         current = current->super()) {
      if (!current->oop_is_instance()) continue;
      for (JavaFieldStream fields(InstanceKlass::cast(current));
           !fields.done(); fields.next()) {
        if (!fields.access_flags().is_static()
            && fields.name()->equals(name, (int) strlen(name))
            && fields.signature()->equals(signature,
                                          (int) strlen(signature))) {
          return fields.offset();
        }
      }
    }
    return -1;
  }

  struct Key {
    Klass *klass;
    const char *name;
    Key(Klass *k, const char *n) : klass(k), name(n) {}
    bool operator<(const Key &other) const {
      if (klass != other.klass) return klass < other.klass;
      return strcmp(name, other.name) < 0;
    }
  };
  pthread_mutex_t _mutex;
  std::map<Key, int> _offsets;
};

FieldOffsetCache *field_offsets() {
  // Function-local so it is constructed on first use and never during
  // static initialisation.
  static FieldOffsetCache cache;
  return &cache;
}

oop object_field(oop holder, const char *name, const char *signature) {
  const int offset = field_offsets()->offset(holder, name, signature);
  return offset < 0 ? (oop) NULL : holder->obj_field(offset);
}

// The one hop from a view, iterator, entry or wrapper to what it is backed
// by, or NULL.
oop backing_of(oop value) {
  const BackingField *field = backing_field_of(value->klass());
  return field == NULL ? (oop) NULL
      : object_field(value, field->name, field->descriptor);
}

}  // namespace

ContainerSupport::Capability ContainerSupport::capability(oop value) {
  if (value == NULL) return CAPABILITY_NONE;
  if (value->is_array()) return CAPABILITY_INDEXED;
  Klass *klass = value->klass();
  const Capability exact = exact_capability(klass);
  if (exact == CAPABILITY_HASH_MAP
      && klass_name_is(klass, "java/util/LinkedHashMap")) {
    // A LinkedHashMap built in access order moves an entry on every get:
    // its iteration order is a function of its reads.
    const int offset =
        field_offsets()->offset(value, "accessOrder", "Z");
    if (offset < 0 || value->bool_field(offset)) return CAPABILITY_NONE;
  }
  if (exact != CAPABILITY_NONE) return exact;
  // The existing positional rule: every AbstractList subclass.
  for (Klass *current = klass; current != NULL; current = current->super()) {
    if (klass_name_is(current, "java/util/AbstractList")) {
      return CAPABILITY_INDEXED;
    }
  }
  return CAPABILITY_NONE;
}

const char *ContainerSupport::shape(oop value) {
  switch (capability(value)) {
    case CAPABILITY_INDEXED: return "INDEXED";
    case CAPABILITY_HASH_MAP:
    case CAPABILITY_CONCURRENT_MAP:
    case CAPABILITY_HASHTABLE:
    case CAPABILITY_HASH_SET: return "ASSOCIATIVE";
    default: return NULL;
  }
}

std::string ContainerSupport::unmodeled_reason(oop value) {
  if (value == NULL || value->is_array()
      || capability(value) != CAPABILITY_NONE) {
    return std::string();
  }
  Klass *klass = value->klass();
  if (klass_name_is(klass, "java/util/LinkedHashMap")) {
    return "ACCESS_ORDER_UNMODELED";
  }
  for (Klass *current = klass->super(); current != NULL;
       current = current->super()) {
    if (exact_capability(current) != CAPABILITY_NONE) {
      ResourceMark rm;
      return std::string("CONTAINER_SUBCLASS_UNMODELED:")
          + klass->name()->as_C_string();
    }
  }
  return std::string();
}

oop ContainerSupport::backing_container(oop value) {
  // A wrapper of a view of a map is two hops; four bounds a cycle.
  for (int hop = 0; value != NULL && hop < 4; ++hop) {
    if (!value->is_array() && capability(value) != CAPABILITY_NONE) {
      return value;
    }
    if (value->is_array()) return NULL;
    value = backing_of(value);
  }
  return NULL;
}

bool ContainerSupport::names_container(oop value) {
  if (value == NULL || value->is_array()) return false;
  return exact_capability(value->klass()) != CAPABILITY_NONE
      || backing_field_of(value->klass()) != NULL;
}

oop ContainerSupport::canonicalize(oop value) {
  oop container = backing_container(value);
  if (container == NULL || container == value || ConcolicMngr::ctx == NULL) {
    return value;
  }
  ConcolicMngr::ctx->alias_container(value, container);
  return container;
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

// The members one walk reads, and where it stops: past `limit` members it
// says only that it is over the bound, and a walker that meets a state it
// cannot read names why (`refused`).
class MemberWalk {
public:
  MemberWalk(std::vector<oop> *keys, std::vector<oop> *values, size_t limit)
      : _keys(keys), _values(values), _limit(limit), _over_bound(false),
        _refused(NULL) {}

  // Records one member; false when the walk should stop.
  bool add(oop key, oop value) {
    if (_keys != NULL) _keys->push_back(key);
    _values->push_back(value);
    if (_values->size() > _limit) {
      _over_bound = true;
      return false;
    }
    return true;
  }
  bool refuse(const char *reason) {
    _refused = reason;
    return false;
  }
  // Over the bound without being walked.
  void exceed() { _over_bound = true; }
  bool over_bound() const { return _over_bound; }
  const char *refused() const { return _refused; }

private:
  std::vector<oop> *_keys;
  std::vector<oop> *_values;
  size_t _limit;
  bool _over_bound;
  const char *_refused;
};

// A chain of entries linked by `next`, from `node`: HashMap's and
// Hashtable's bins, a ConcurrentHashMap bin or tree bin.  Bounded against a
// corrupted cycle.
bool walk_chain(oop node, const char *key_name, const char *value_name,
                const char *next_descriptor, MemberWalk *walk) {
  for (int guard = 0; node != NULL && guard < (1 << 20); ++guard) {
    const int key_offset =
        field_offsets()->offset(node, key_name, "Ljava/lang/Object;");
    const int value_offset =
        field_offsets()->offset(node, value_name, "Ljava/lang/Object;");
    const int next_offset =
        field_offsets()->offset(node, "next", next_descriptor);
    if (key_offset < 0 || value_offset < 0 || next_offset < 0) return false;
    if (!walk->add(node->obj_field(key_offset),
                   node->obj_field(value_offset))) {
      return true;
    }
    node = node->obj_field(next_offset);
  }
  return true;
}

// HashMap/LinkedHashMap: table is a Node[]; each bin is a chain linked by
// `next`.  A treeified bin holds TreeNodes, and TreeNode extends
// LinkedHashMap.Entry extends HashMap.Node, so `next` still threads every
// member of the bin -- one chain walk covers both bin kinds and no red-black
// traversal is needed.
bool read_hash_map(oop map, MemberWalk *walk) {
  const int table_offset =
      field_offsets()->offset(map, "table", "[Ljava/util/HashMap$Node;");
  if (table_offset < 0) return false;
  oop table = map->obj_field(table_offset);
  // A HashMap that has never been written has a null table.  That is an
  // exactly empty map, not an unreadable one.
  if (table == NULL) return true;
  if (!table->is_objArray()) return false;
  objArrayOop bins = objArrayOop(table);
  for (int bin = 0; bin < bins->length() && !walk->over_bound(); ++bin) {
    if (!walk_chain(bins->obj_at(bin), "key", "value",
                    "Ljava/util/HashMap$Node;", walk)) {
      return false;
    }
  }
  return true;
}

// A ConcurrentHashMap's table: a bin whose hash is >= 0 is a chain by
// `next`; a TREEBIN (-2) threads its TreeNodes from `first` by `next`; a
// RESERVED (-3) placeholder of a computeIfAbsent in flight holds nothing; a
// MOVED (-1) forwarding node means a resize is copying the table, and what
// the map holds is then split between two tables no lock-free walk can read
// at one instant.  More than CONCURRENT_MAP_MAX_BINS bins is over the bound
// without being walked.
const int CONCURRENT_MAP_MAX_BINS = 4096;
const int CONCURRENT_MAP_MOVED = -1;
const int CONCURRENT_MAP_TREEBIN = -2;
const int CONCURRENT_MAP_RESERVED = -3;
const char *const CONCURRENT_NODE =
    "Ljava/util/concurrent/ConcurrentHashMap$Node;";

bool read_concurrent_hash_map(oop map, MemberWalk *walk) {
  const int table_offset = field_offsets()->offset(
      map, "table", "[Ljava/util/concurrent/ConcurrentHashMap$Node;");
  if (table_offset < 0) return false;
  oop table = map->obj_field(table_offset);
  // Never written: the table is allocated lazily.  Exactly empty.
  if (table == NULL) return true;
  if (!table->is_objArray()) return false;
  objArrayOop bins = objArrayOop(table);
  if (bins->length() > CONCURRENT_MAP_MAX_BINS) {
    walk->exceed();
    return true;
  }
  for (int bin = 0; bin < bins->length() && !walk->over_bound(); ++bin) {
    oop node = bins->obj_at(bin);
    if (node == NULL) continue;
    const int hash_offset = field_offsets()->offset(node, "hash", "I");
    if (hash_offset < 0) return false;
    const int hash = node->int_field(hash_offset);
    if (hash == CONCURRENT_MAP_MOVED) return walk->refuse("RESIZING");
    if (hash == CONCURRENT_MAP_RESERVED) continue;
    if (hash == CONCURRENT_MAP_TREEBIN) {
      node = object_field(node, "first",
                          "Ljava/util/concurrent/ConcurrentHashMap$TreeNode;");
    }
    if (!walk_chain(node, "key", "val", CONCURRENT_NODE, walk)) return false;
  }
  return true;
}

// Hashtable: table is an Entry[] of chains by `next`.
bool read_hashtable(oop table_owner, MemberWalk *walk) {
  const int table_offset = field_offsets()->offset(
      table_owner, "table", "[Ljava/util/Hashtable$Entry;");
  if (table_offset < 0) return false;
  oop table = table_owner->obj_field(table_offset);
  if (table == NULL) return true;
  if (!table->is_objArray()) return false;
  objArrayOop bins = objArrayOop(table);
  for (int bin = 0; bin < bins->length() && !walk->over_bound(); ++bin) {
    if (!walk_chain(bins->obj_at(bin), "key", "value",
                    "Ljava/util/Hashtable$Entry;", walk)) {
      return false;
    }
  }
  return true;
}

// HashSet/LinkedHashSet are a HashMap whose values are a shared placeholder;
// the members are its keys, and an ASSOCIATIVE shape is not what a set reads
// back as, so the members are reported as values.
bool read_hash_set(oop set, MemberWalk *walk, size_t limit) {
  oop map = object_field(set, "map", "Ljava/util/HashMap;");
  if (map == NULL) {
    return field_offsets()->offset(set, "map", "Ljava/util/HashMap;") >= 0;
  }
  std::vector<oop> keys;
  std::vector<oop> ignored;
  MemberWalk inner(&keys, &ignored, limit);
  if (!read_hash_map(map, &inner)) return false;
  for (size_t index = 0; index < keys.size(); ++index) {
    if (!walk->add(NULL, keys[index])) break;
  }
  return true;
}

// ArrayList: elementData is the backing array and `size` is how much of it is
// live.  The array is usually longer than the list; reading past `size` would
// state stale members a clear() left behind.
bool read_array_list(oop list, MemberWalk *walk) {
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
    if (!walk->add(NULL, elements->obj_at(index))) break;
  }
  return true;
}

// ArrayDeque: a circular buffer between head and tail, so iteration order is
// head..tail modulo the capacity rather than 0..length.
bool read_array_deque(oop deque, MemberWalk *walk) {
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
    if (!walk->add(NULL, elements->obj_at(index))) break;
  }
  return true;
}

} // anonymous namespace

bool ContainerSupport::read_concrete_members(oop container,
                                             std::vector<oop> *keys,
                                             std::vector<oop> *values,
                                             const char **unsupported_class,
                                             bool *over_bound) {
  if (unsupported_class != NULL) *unsupported_class = NULL;
  if (over_bound != NULL) *over_bound = false;
  if (container == NULL || keys == NULL || values == NULL) return false;
  // One past the snapshot bound is enough to know a walk is over it.
  const size_t limit = (size_t) ConcolicMngr::initialSnapshotMaxEntries();

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

  MemberWalk associative(keys, values, limit);
  MemberWalk positional(NULL, values, limit);
  MemberWalk *walk = &positional;
  bool read = false;
  switch (capability(container)) {
    case CAPABILITY_HASH_MAP:
      walk = &associative;
      read = read_hash_map(container, walk);
      break;
    case CAPABILITY_CONCURRENT_MAP:
      walk = &associative;
      read = read_concurrent_hash_map(container, walk);
      break;
    case CAPABILITY_HASHTABLE:
      walk = &associative;
      read = read_hashtable(container, walk);
      break;
    case CAPABILITY_HASH_SET:
      read = read_hash_set(container, walk, limit);
      break;
    case CAPABILITY_INDEXED:
      if (klass_name_is(container, "java/util/ArrayList")) {
        read = read_array_list(container, walk);
      } else if (klass_name_is(container, "java/util/ArrayDeque")) {
        read = read_array_deque(container, walk);
      }
      break;
    default:
      break;
  }
  if (read && walk->refused() == NULL) {
    if (over_bound != NULL) *over_bound = walk->over_bound();
    return true;
  }
  // Admitted by the model but not walked here, or caught in a state no walk
  // can read.  Named, never guessed at: a reader that could not tell "held
  // nothing" from "this engine cannot read it" would solve with an empty
  // container.
  if (unsupported_class != NULL) {
    *unsupported_class = walk->refused() != NULL ? walk->refused()
        : container->klass()->name()->as_C_string();
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
  bool over_bound = false;
  if (!read_concrete_members(container, &keys, &values, unsupported_class,
                             &over_bound)) {
    return -1;
  }

  const bool associative = strcmp(shape, "ASSOCIATIVE") == 0;
  if (!over_bound && associative && keys.size() != values.size()) return -1;
  const int entries = (int) values.size();

  // The same bound the Java-driven offer obeyed.  Past it the container keeps
  // its opaque root and the refusal is stated: "held something this engine
  // declined to state" is a different fact from "held nothing", and a reader
  // that cannot tell them apart would solve with an empty container.
  if (over_bound || entries > ConcolicMngr::initialSnapshotMaxEntries()) {
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

SharedFieldVersions::Location ContainerSupport::state_location(oop container) {
  SharedFieldVersions::Location location;
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  if (container == NULL || heap == NULL) return location;
  // A view a modeled call made is aliased to its container already; one the
  // program built (a wrapper, a view of a map nobody tracked yet) is found
  // through its backing fields.
  sym_rid_t owner = heap->canonical_container_id(container);
  const bool own = owner == NULL_SYM_RID || owner == container->get_sym_rid();
  oop backing = own ? backing_container(container) : (oop) NULL;
  if (backing != NULL && backing != container) {
    owner = heap->canonical_container_id(backing);
  }
  if (owner == NULL_SYM_RID) return location;
  return SharedFieldVersions::Location(
      owner, SharedFieldVersions::SLOT_WHOLE_STATE,
      SharedFieldVersions::LOC_MAP_STATE);
}

SharedFieldVersions::Location ContainerSupport::state_base_before_operation(
    oop container, SharedFieldVersions::InitialSnapshot *started) {
  SharedFieldVersions::Location none;
  if (started != NULL) *started = SharedFieldVersions::InitialSnapshot();
  if (container == NULL || ConcolicMngr::ctx == NULL) return none;
  if (shape(container) == NULL) return none;

  // Called from a model's invoke hook: the arguments are in hand and the
  // callee body has NOT run, so the receiver still holds exactly the contents
  // the log must begin from.  This is the only place a write-first container
  // can be read honestly -- by the time the finish hook publishes the
  // mutation, the concrete put has already happened and a walk would state a
  // base that includes the entry being written.  A reference store of the
  // container asks before its store the same way.
  SharedFieldVersions::Location existing = state_location(container);
  if (existing.is_valid() && SharedFieldVersions::is_tracked(existing)) {
    return existing;
  }

  SharedFieldVersions::InitialSnapshot snapshot;
  snapshot_for_receiver(container, &snapshot, true);

  // The state the walk stated, or -- a refused walk mints none -- the bare
  // root, so the log still begins here and its INITIAL states the refusal
  // (a map caught mid-resize is RESIZING, not an unreadable class).
  Expression *base =
      ConcolicMngr::ctx->container_state(container, shape(container));
  if (base == NULL) return none;
  SharedFieldVersions::Location location = state_location(container);
  if (!location.is_valid()) return none;
  if (SharedFieldVersions::is_tracked(location)) return location;
  SharedFieldVersions::publish_initial(
      location, base, SharedFieldVersions::ConcreteBits(), snapshot);
  if (started != NULL) *started = snapshot;
  return location;
}

void ContainerSupport::referent_state(
    oop referent, SharedFieldVersions::ReferentState *out) {
  oop container = backing_container(referent);
  if (container == NULL) return;
  SharedFieldVersions::Location location;
  if (ConcolicMngr::ctx == NULL) {
    // A thread outside every region cannot start a log; one that stands is
    // still named.
    location = state_location(container);
    if (!location.is_valid() || !SharedFieldVersions::is_tracked(location)) {
      out->refused = "NO_CONTEXT";
      return;
    }
  } else {
    SharedFieldVersions::InitialSnapshot started;
    location = state_base_before_operation(container, &started);
    if (!location.is_valid()) {
      ResourceMark rm;
      out->refused = std::string("UNREADABLE_CONTAINER:")
          + container->klass()->name()->as_C_string();
      return;
    }
    if (started.present() && !started.stated) {
      // The log began here and could not state what the container held.
      if (started.truncated) {
        out->refused = "TRUNCATED";
      } else if (started.unsupported_class == "RESIZING") {
        out->refused = "RESIZING";
      } else {
        out->refused = "UNREADABLE_CONTAINER:" + started.unsupported_class;
      }
      return;
    }
  }
  out->owner = location.owner;
  out->version_id = SharedFieldVersions::live_version(location, NULL);
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
  // Control dependence, asked of the plan, not "after a branch": this call
  // must be a store site the plan says is control-dependent, and one of that
  // site's guard branches must have decided something symbolic on this path.
  if (!(callee == "put" || callee == "remove" || callee == "clear"
        || callee == "add" || callee == "offer" || callee == "set")) {
    return false;
  }
  return SharedFieldVersions::guarded_store_admitted(NULL, "CALL " + callee);
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
    const std::string &java_type, Expression *owner) {
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
                              arguments, result_type, type_name, NULL,
                              owner),
      ReturnedValue());
  return answer;
}

Expression *ContainerSupport::receiver_owner(Expression *receiver) {
  if (receiver == NULL) return NULL;
  Expression *inherited = NULL;
  if (receiver->derived_container_value(&inherited)) return inherited;
  return receiver->is_guarded_reference_read() ? receiver : NULL;
}

Expression *ContainerSupport::observed_state(oop container) {
  if (container == NULL || ConcolicMngr::ctx == NULL) return NULL;
  SharedFieldVersions::Location location = state_location(container);
  SharedFieldVersions::ReadPlan plan;
  if (location.is_valid()
      && SharedFieldVersions::plan_read(
             location, SharedFieldVersions::ConcreteBits(), &plan)
      && plan.observed.value != NULL) {
    return SharedFieldVersions::build_read_from(
        plan, location, "L", plan.observed.value, ReturnedValue());
  }
  return ConcolicMngr::ctx->find_container_state(container);
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
