#ifdef ENABLE_CONCOLIC

#include "concolic/sharedFieldVersions.hpp"

#include <algorithm>

#include "classfile/javaClasses.hpp"
#include "classfile/symbolTable.hpp"
#include "classfile/systemDictionary.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/readFromExpression.hpp"
#include "concolic/exp/consumerBoundaryExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "oops/arrayKlass.hpp"
#include "oops/cpCache.hpp"
#include "oops/instanceKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "oops/typeArrayOop.hpp"
#include "runtime/fieldDescriptor.hpp"
#include "utilities/ostream.hpp"
#include "webridge/utils/rapidjson/stringbuffer.h"
#include "webridge/utils/rapidjson/writer.h"

bool SharedFieldVersions::_open = false;
SharedFieldVersions::SlotStore SharedFieldVersions::_slots;
volatile int SharedFieldVersions::_carrier_count = 0;
volatile int SharedFieldVersions::_guarded_store_count = 0;
pthread_mutex_t SharedFieldVersions::_mutex = PTHREAD_MUTEX_INITIALIZER;

#define STRIPE_INIT_8 PTHREAD_MUTEX_INITIALIZER, PTHREAD_MUTEX_INITIALIZER, \
  PTHREAD_MUTEX_INITIALIZER, PTHREAD_MUTEX_INITIALIZER,                     \
  PTHREAD_MUTEX_INITIALIZER, PTHREAD_MUTEX_INITIALIZER,                     \
  PTHREAD_MUTEX_INITIALIZER, PTHREAD_MUTEX_INITIALIZER
pthread_mutex_t SharedFieldVersions::_stripes[SharedFieldVersions::STRIPES] = {
  STRIPE_INIT_8, STRIPE_INIT_8, STRIPE_INIT_8, STRIPE_INIT_8,
  STRIPE_INIT_8, STRIPE_INIT_8, STRIPE_INIT_8, STRIPE_INIT_8
};
#undef STRIPE_INIT_8

namespace {

// One location can retain many versions, each with a value and a path guard.
// This envelope bound keeps individually bounded roots from accumulating
// into one unbounded native StringBuffer.
static const size_t MAX_VERSION_ENVELOPE_BYTES = 32u * 1024u * 1024u;

// What an envelope costs so far: the buffer plus the table its references
// will pull in.  A stopping rule, not a ceiling (see write_versions_envelope).
size_t envelope_bytes(const rapidjson::StringBuffer &buffer,
                      VmExpressionArtifactScope &artifact) {
  return buffer.GetSize() + artifact.pending_table_size();
}

class MapLock {
public:
  MapLock(pthread_mutex_t *mutex) : _mutex(mutex) {
    pthread_mutex_lock(_mutex);
  }
  ~MapLock() { pthread_mutex_unlock(_mutex); }
private:
  pthread_mutex_t *_mutex;
};

} // anonymous namespace

#define MAP_LOCK MapLock map_guard(&_mutex)

// ---------------------------------------------------------------------------
// Sessions, slots and stripes.
// ---------------------------------------------------------------------------

void SharedFieldVersions::open_session() {
  MAP_LOCK;
  guarantee(_slots.empty(), "versions outlived the previous session");
  _carrier_count = 0;
  _open = true;
}

void SharedFieldVersions::close_session() {
  // Every stripe, then the map: no thread may be inside a slot while the
  // store is cleared.  Every Expression named here belongs to the session
  // arena and is freed with it.
  for (int stripe = 0; stripe < STRIPES; ++stripe) {
    pthread_mutex_lock(&_stripes[stripe]);
  }
  {
    MAP_LOCK;
    _slots.clear();
    _carrier_count = 0;
    _open = false;
  }
  for (int stripe = STRIPES - 1; stripe >= 0; --stripe) {
    pthread_mutex_unlock(&_stripes[stripe]);
  }
}

int SharedFieldVersions::stripe_of(const Location &location) {
  julong hash = (julong) location.owner * UCONST64(0x9E3779B97F4A7C15);
  hash ^= (julong)(juint) location.slot * UCONST64(0xC2B2AE3D27D4EB4F);
  hash ^= (julong)(juint) location.kind;
  hash ^= hash >> 29;
  return (int)(hash % (julong) STRIPES);
}

void SharedFieldVersions::lock(const Location &location) {
  pthread_mutex_lock(&_stripes[stripe_of(location)]);
}

void SharedFieldVersions::unlock(const Location &location) {
  pthread_mutex_unlock(&_stripes[stripe_of(location)]);
}

void SharedFieldVersions::lock_stripes(const std::vector<int> &stripes) {
  for (size_t index = 0; index < stripes.size(); ++index) {
    pthread_mutex_lock(&_stripes[stripes[index]]);
  }
}

void SharedFieldVersions::unlock_stripes(const std::vector<int> &stripes) {
  for (size_t index = stripes.size(); index > 0; --index) {
    pthread_mutex_unlock(&_stripes[stripes[index - 1]]);
  }
}

SharedFieldVersions::Slot *SharedFieldVersions::find_slot(
    const Location &location) {
  MAP_LOCK;
  if (!_open) return NULL;
  SlotStore::iterator found = _slots.find(location);
  return found == _slots.end() ? NULL : &found->second;
}

SharedFieldVersions::Slot *SharedFieldVersions::find_or_create_slot(
    const Location &location) {
  MAP_LOCK;
  if (!_open) return NULL;
  // A std::map node never moves, so the pointer stays valid after the map
  // lock is released; its contents are the stripe's.
  Slot *slot = &_slots[location];
  _carrier_count = (int) _slots.size();
  return slot;
}

bool SharedFieldVersions::is_tracked(const Location &location) {
  if (!location.is_valid()) return false;
  MAP_LOCK;
  return _open && _slots.find(location) != _slots.end();
}

jlong SharedFieldVersions::append_locked(Slot *slot, Version *version) {
  // Minted under the stripe: ids of one location ascend in log order, which
  // is heap order.
  version->version_id = GlobalSymbolicSession::next_event_id();
  slot->versions.push_back(*version);
  if (slot->versions.size() > MAX_VERSIONS_PER_LOCATION) {
    // A dropped writer is a writer a later read can no longer name.
    slot->versions.erase(slot->versions.begin());
    incomplete_locked(slot, "VERSION_BOUND");
  }
  return version->version_id;
}

void SharedFieldVersions::incomplete_locked(Slot *slot, const char *reason) {
  if (slot->writer_set_complete) {
    slot->writer_set_complete = false;
    slot->incomplete_reason = reason == NULL ? "UNSPECIFIED" : reason;
  }
}

SharedFieldVersions::Attribution SharedFieldVersions::current_attribution() {
  Attribution who;
  if (ConcolicMngr::ctx == NULL) return who;
  who.context_id = ConcolicMngr::ctx->get_context_id();
  who.region_id = ConcolicMngr::ctx->get_region_id();
  who.task_id = ConcolicMngr::ctx->get_task_id();
  who.region_enter_event_id = ConcolicMngr::ctx->region_enter_event();
  who.site = current_site();
  return who;
}

void SharedFieldVersions::fill_version(Version *version, const Store &store) {
  version->version_kind = store.version_kind;
  version->operation = store.operation;
  version->writer = store.writer;
  version->path_guard = store.path_guard;
}

// ---------------------------------------------------------------------------
// Writes.
// ---------------------------------------------------------------------------

void SharedFieldVersions::prepare_store(Store *store,
                                        const Location &location,
                                        Expression *value,
                                        Expression *path_guard, bool symbolic,
                                        bool starts_log, int version_kind) {
  store->location = location;
  store->value = value;
  store->path_guard = path_guard;
  store->symbolic = symbolic;
  store->starts_log = symbolic || starts_log;
  store->version_kind = version_kind;
}

bool SharedFieldVersions::begin_store_locked(Store *store, const Cell &cell) {
  store->versioned = false;
  store->base_value = NULL;
  store->base = ConcreteBits();
  if (!store->location.is_valid()) return false;
  const bool tracked = find_slot(store->location) != NULL;
  if (!tracked && !store->starts_log) return false;
  store->versioned = true;
  store->writer = current_attribution();
  if (tracked) return true;
  // The log begins at the value this store replaces, read here, under the
  // stripe, so no store can fall between it and this one.  Without it a
  // reader whose writer's guard flipped would have no "the store did not
  // happen" candidate.  A symbolic store keeps its old start: the value it
  // stores is the first thing the log knows.
  if (!store->symbolic && cell.holder != NULL) {
    store->base = cell_word(store->location, cell);
    store->base_value = cell_value(store->location, cell, store->base);
  }
  return true;
}

jlong SharedFieldVersions::end_store_locked(Store *store,
                                            const ConcreteBits &stored,
                                            oop stored_reference) {
  if (!store->versioned) return 0;
  Slot *slot = find_slot(store->location);
  if (slot == NULL) {
    slot = find_or_create_slot(store->location);
    if (slot == NULL) return 0;
    if (store->base_value != NULL) {
      Version base;
      base.version_kind = VERSION_INITIAL;
      base.value = store->base_value;
      base.stored = store->base;
      if (base.stored.stated() && base.value != NULL) {
        base.stored_constant = base.value;
      }
      append_locked(slot, &base);
    }
  }
  Version version;
  fill_version(&version, *store);
  version.stored = stored;
  if (store->value != NULL) {
    version.value = store->value;
  } else if (stored.stated()) {
    version.value = primitive_expression(stored.type, stored.bits);
    version.stored_constant = version.value;
  } else {
    version.value = reference_expression(stored_reference);
  }
  if (version.value == NULL) {
    // A referent no session names: the write happened and says nothing.
    incomplete_locked(slot, "UNNAMED_REFERENT");
    return 0;
  }
  return append_locked(slot, &version);
}

jlong SharedFieldVersions::publish_value(const Location &location,
                                         Expression *value,
                                         const ConcreteBits &stored,
                                         Expression *path_guard,
                                         bool symbolic, int version_kind,
                                         const char *operation) {
  if (!location.is_valid() || value == NULL) return 0;
  // A location no symbolic value has reached costs one counter read.
  if (!symbolic && path_guard == NULL && !has_carriers()) return 0;
  // A concrete store is evidence too when it is control-dependent on a
  // symbolic decision: what the location holds afterwards is a function of
  // that predicate (HDFS-11741's removeExpiredKeys under a CLOCK root).  The
  // plan says which store methods are control-dependent on which branch
  // sites (install_guarded_store_sites); asked only when it can matter.
  const bool starts_log = symbolic
      || (path_guard != NULL && !is_tracked(location)
          && guarded_store_admitted());
  Store store;
  prepare_store(&store, location, value, path_guard, symbolic, starts_log,
                version_kind);
  if (operation != NULL) store.operation = operation;
  lock(location);
  begin_store_locked(&store, Cell());
  jlong id = end_store_locked(&store, stored, NULL);
  unlock(location);
  return id;
}

jlong SharedFieldVersions::publish_held(const Location &location,
                                        const Cell &cell, Expression *value,
                                        Expression *path_guard,
                                        int version_kind) {
  if (!location.is_valid() || value == NULL) return 0;
  Store store;
  prepare_store(&store, location, value, path_guard, true, true,
                version_kind);
  lock(location);
  begin_store_locked(&store, Cell());
  // The word is the one the cell holds now: nothing can store between this
  // read and the version, because a store takes the same stripe.
  jlong id = end_store_locked(&store, cell_word(location, cell), NULL);
  unlock(location);
  return id;
}

jlong SharedFieldVersions::publish_initial(const Location &location,
                                           Expression *base,
                                           const ConcreteBits &stored,
                                           const InitialSnapshot &snapshot) {
  if (!location.is_valid() || base == NULL) return 0;
  Version version;
  version.version_kind = VERSION_INITIAL;
  version.value = base;
  version.stored = stored;
  version.initial_snapshot_present = snapshot.present();
  version.initial_snapshot_stated = snapshot.stated;
  version.initial_snapshot_entries = snapshot.entries;
  version.initial_snapshot_truncated = snapshot.truncated;
  version.initial_snapshot_unsupported_class = snapshot.unsupported_class;
  version.writer = current_attribution();
  lock(location);
  jlong id = 0;
  if (find_slot(location) == NULL) {
    Slot *slot = find_or_create_slot(location);
    if (slot != NULL) id = append_locked(slot, &version);
  }
  unlock(location);
  return id;
}

jlong SharedFieldVersions::publish_initial_held(const Location &location,
                                                const Cell &cell,
                                                Expression **base_out) {
  if (base_out != NULL) *base_out = NULL;
  if (!location.is_valid()) return 0;
  Attribution writer = current_attribution();
  lock(location);
  jlong id = 0;
  if (find_slot(location) == NULL) {
    Version version;
    version.version_kind = VERSION_INITIAL;
    version.writer = writer;
    version.stored = cell_word(location, cell);
    version.value = cell_value(location, cell, version.stored);
    if (version.stored.stated()) version.stored_constant = version.value;
    Slot *slot = version.value == NULL ? NULL : find_or_create_slot(location);
    if (slot != NULL) {
      id = append_locked(slot, &version);
      if (base_out != NULL) *base_out = version.value;
    }
  }
  unlock(location);
  return id;
}

bool SharedFieldVersions::mark_writer_set_incomplete_locked(
    const Location &location, const char *reason) {
  Slot *slot = find_slot(location);
  if (slot == NULL) return false;
  incomplete_locked(slot, reason);
  return true;
}

bool SharedFieldVersions::mark_writer_set_incomplete(
    const Location &location, const char *reason) {
  if (!location.is_valid()) return false;
  lock(location);
  bool marked = mark_writer_set_incomplete_locked(location, reason);
  unlock(location);
  return marked;
}

// ---------------------------------------------------------------------------
// Reads.
// ---------------------------------------------------------------------------

void SharedFieldVersions::prepare_read(ReadPlan *plan) {
  *plan = ReadPlan();
  plan->reader = current_attribution();
}

bool SharedFieldVersions::plan_read_locked(const Location &location,
                                           const ConcreteBits &loaded,
                                           ReadPlan *plan) {
  if (!location.is_valid()) return false;
  Slot *slot = find_slot(location);
  if (slot == NULL || slot->versions.empty()) return false;

  // The last version is the newest, and under the stripe it is what the
  // location held when this load ran -- unless the word says not.
  size_t observed = slot->versions.size() - 1;
  if (slot->versions[observed].stored.contradicts(loaded)) {
    // A writer no hook saw came between (see the class comment).  First a
    // retained version that stored exactly this word: it is what the read
    // returned.  Else the loaded constant, published as that write.
    incomplete_locked(slot, "UNOBSERVED_WRITE");
    bool retained = false;
    for (size_t index = observed; index > 0; --index) {
      if (slot->versions[index - 1].stored.equals(loaded)) {
        observed = index - 1;
        retained = true;
        break;
      }
    }
    if (!retained) {
      Version unobserved;
      unobserved.version_kind = VERSION_UNOBSERVED;
      unobserved.value = primitive_expression(loaded.type, loaded.bits);
      unobserved.stored = loaded;
      unobserved.stored_constant = unobserved.value;
      append_locked(slot, &unobserved);
      observed = slot->versions.size() - 1;
    }
  }

  Version &version = slot->versions[observed];
  plan->observed_exact = version.stored.equals(loaded);
  if (plan->observed_exact && version.stored_constant == NULL) {
    // Built once per version, for every read that returns its word.
    version.stored_constant =
        primitive_expression(version.stored.type, version.stored.bits);
  }
  plan->observed = version;
  plan->writer_set_complete = slot->writer_set_complete;
  plan->read_event_id = GlobalSymbolicSession::next_event_id();

  ReadRecord record;
  record.read_event_id = plan->read_event_id;
  record.reader = plan->reader;
  slot->reads.push_back(record);
  if (slot->reads.size() > MAX_READS_PER_LOCATION) {
    slot->reads.erase(slot->reads.begin());
    slot->read_log_complete = false;
  }
  return true;
}

bool SharedFieldVersions::plan_read(const Location &location,
                                    const ConcreteBits &loaded,
                                    ReadPlan *plan) {
  if (plan == NULL || !location.is_valid() || ConcolicMngr::ctx == NULL) {
    return false;
  }
  prepare_read(plan);
  lock(location);
  bool planned = plan_read_locked(location, loaded, plan);
  unlock(location);
  if (planned) {
    // Reading tracked state is what makes this thread's branches relevant:
    // by value, the read is the declaration (laneBJ's REGION.f0132fca).
    ConcolicMngr::ctx->set_pc_admitted(true);
  }
  return planned;
}

jlong SharedFieldVersions::live_version(const Location &location,
                                        std::string *version_kind) {
  if (version_kind != NULL) version_kind->clear();
  if (!location.is_valid()) return 0;
  lock(location);
  Slot *slot = find_slot(location);
  jlong id = 0;
  if (slot != NULL && !slot->versions.empty()) {
    const Version &version = slot->versions.back();
    if (version_kind != NULL) *version_kind = version_label(version);
    id = version.version_id;
  }
  unlock(location);
  return id;
}

void SharedFieldVersions::tracked_elements(sym_rid_t owner, int from, int to,
                                           std::vector<int> *slots) {
  slots->clear();
  if (owner == NULL_SYM_RID || from >= to || !has_carriers()) return;
  MAP_LOCK;
  if (!_open) return;
  SlotStore::const_iterator it =
      _slots.lower_bound(Location(owner, from, LOC_INSTANCE_FIELD));
  for (; it != _slots.end() && it->first.owner == owner
         && it->first.slot < to; ++it) {
    if (it->first.kind == LOC_ARRAY_ELEMENT) {
      slots->push_back(it->first.slot);
    }
  }
}

Expression *SharedFieldVersions::build_read_from(
    const ReadPlan &plan, const Location &location,
    const std::string &type_name, Expression *observed_value,
    const ReturnedValue &returned) {
  guarantee(observed_value != NULL,
            "a read-from needs the value of the version it observed");
  Expression *selection = new ReadFromExpression(
      plan.observed.version_id, version_label(plan.observed), observed_value,
      type_name, plan.read_event_id, location.owner, location.slot,
      location_kind_name(location.kind), plan.writer_set_complete,
      plan.observed_exact, returned, plan.reader.site.class_name,
      plan.reader.site.method_name, plan.reader.site.method_descriptor,
      plan.reader.site.bci);
  return new ConsumerBoundaryExpression(
      selection, type_name, ConsumerBoundaryExpression::FIELD_READ,
      plan.read_event_id);
}

Expression *SharedFieldVersions::scalar_read(const ReadPlan &plan,
                                             const Location &location,
                                             const std::string &type_name,
                                             const ConcreteBits &loaded,
                                             oop reference) {
  ReturnedValue returned;
  if (plan.observed_exact && plan.observed.stored_constant != NULL
      && !plan.observed.stored.is_null()) {
    // The word the observed version stored: its constant, shared by every
    // read that returned it.
    returned.kind = ReturnedValue::CONSTANT;
    returned.constant = plan.observed.stored_constant;
  } else {
    returned = returned_value(loaded, reference);
  }
  return build_read_from(plan, location, type_name, plan.observed.value,
                         returned);
}

ReturnedValue SharedFieldVersions::returned_value(const ConcreteBits &word,
                                                  oop reference) {
  ReturnedValue returned;
  if (word.stated() && !word.is_null()) {
    returned.kind = ReturnedValue::CONSTANT;
    returned.constant = primitive_expression(word.type, word.bits);
  } else if (reference == NULL) {
    returned.kind = ReturnedValue::NULL_REFERENCE;
  } else if (reference->klass() == SystemDictionary::String_klass()) {
    // Stated up to a bound, past which only its length is: a read of a
    // configuration blob or a serialized message would otherwise put its
    // whole content into every node that returned it.
    const int length = java_lang_String::utf8_length(reference);
    if (length >= 0 && (size_t) length > MAX_RETURNED_STRING_BYTES) {
      returned.kind = ReturnedValue::TRUNCATED_STRING;
      returned.length = length;
    } else {
      ResourceMark rm;
      returned.kind = ReturnedValue::STRING;
      returned.content = OopUtils::java_string_to_c(reference);
    }
  }
  return returned;
}

// ---------------------------------------------------------------------------
// Words and constants.
// ---------------------------------------------------------------------------

Expression *SharedFieldVersions::primitive_expression(BasicType type,
                                                      jlong bits) {
  switch (type) {
    case T_BOOLEAN:
      return new ConExpression((jboolean)(bits & 1));
    case T_BYTE:
      return new ConExpression((jbyte) bits);
    case T_CHAR:
      return new ConExpression((jchar) bits);
    case T_SHORT:
      return new ConExpression((jshort) bits);
    case T_INT:
      return new ConExpression((jint) bits);
    case T_LONG:
      return new ConExpression((jlong) bits);
    case T_FLOAT:
      return new ConExpression(jfloat_cast((jint) bits));
    case T_DOUBLE:
      return new ConExpression(jdouble_cast(bits));
    case T_OBJECT:
      // The null word of a wrapper-typed cell.
      return SymbolExpression::get(Sym_NULL);
    default:
      return NULL;
  }
}

Expression *SharedFieldVersions::reference_expression(oop value) {
  if (value == NULL) return SymbolExpression::get(Sym_NULL);
  // Prefers an existing shadow's identity and otherwise names the referent
  // concretely; never an unconstrained symbol.  Answered from the session
  // heap, so a thread outside every region names what it stores too (D4: a
  // reference such a thread stored used to publish nothing, and readers kept
  // the referent the heap no longer held).
  if (GlobalSymbolicSession::heap() == NULL) return NULL;
  return ContainerSupport::concrete_value(value);
}

SharedFieldVersions::ConcreteBits SharedFieldVersions::boxed_word(oop box) {
  if (box == NULL) return ConcreteBits(T_OBJECT, 0);
  jvalue value;
  const BasicType type = java_lang_boxing_object::get_value(box, &value);
  switch (type) {
    case T_BOOLEAN: return ConcreteBits(type, raw_bits(value.z));
    case T_BYTE:    return ConcreteBits(type, raw_bits(value.b));
    case T_CHAR:    return ConcreteBits(type, raw_bits(value.c));
    case T_SHORT:   return ConcreteBits(type, raw_bits(value.s));
    case T_INT:     return ConcreteBits(type, raw_bits(value.i));
    case T_LONG:    return ConcreteBits(type, raw_bits(value.j));
    default:        return ConcreteBits();
  }
}

BasicType SharedFieldVersions::wrapper_value_type(Symbol *signature) {
  if (signature == NULL || signature->utf8_length() < 16) return T_ILLEGAL;
  if (signature->equals("Ljava/lang/Long;")) return T_LONG;
  if (signature->equals("Ljava/lang/Integer;")) return T_INT;
  if (signature->equals("Ljava/lang/Boolean;")) return T_BOOLEAN;
  if (signature->equals("Ljava/lang/Short;")) return T_SHORT;
  if (signature->equals("Ljava/lang/Byte;")) return T_BYTE;
  if (signature->equals("Ljava/lang/Character;")) return T_CHAR;
  return T_ILLEGAL;
}

BasicType SharedFieldVersions::wrapper_value_type(
    ConstantPoolCacheEntry *entry) {
  if (entry == NULL || !entry->is_field_entry()) return T_ILLEGAL;
  Klass *holder = entry->f1_as_klass();
  if (holder == NULL || !holder->oop_is_instance()) return T_ILLEGAL;
  return wrapper_value_type(
      InstanceKlass::cast(holder)->field_signature(entry->field_index()));
}

Expression *SharedFieldVersions::field_value(oop owner, int field_offset,
                                             BasicType type) {
  if (owner == NULL) return NULL;
  if (type == T_OBJECT || type == T_ARRAY) {
    // The referent's identity, in the spelling an owner identity has, so the
    // composer can equate this read reference with the owner of another
    // read; null answers with the null symbol.
    return reference_expression(owner->obj_field(field_offset));
  }
  const ConcreteBits held = field_bits(owner, field_offset, type);
  return primitive_expression(held.type, held.bits);
}

SharedFieldVersions::ConcreteBits SharedFieldVersions::field_bits(
    oop owner, int field_offset, BasicType type) {
  if (owner == NULL) return ConcreteBits();
  switch (type) {
    case T_BOOLEAN:
      return ConcreteBits(type, raw_bits(owner->bool_field(field_offset)));
    case T_BYTE:
      return ConcreteBits(type, raw_bits(owner->byte_field(field_offset)));
    case T_CHAR:
      return ConcreteBits(type, raw_bits(owner->char_field(field_offset)));
    case T_SHORT:
      return ConcreteBits(type, raw_bits(owner->short_field(field_offset)));
    case T_INT:
      return ConcreteBits(type, raw_bits(owner->int_field(field_offset)));
    case T_LONG:
      return ConcreteBits(type, raw_bits(owner->long_field(field_offset)));
    case T_FLOAT:
      return ConcreteBits(type, raw_bits(owner->float_field(field_offset)));
    case T_DOUBLE:
      return ConcreteBits(type, raw_bits(owner->double_field(field_offset)));
    default:
      return ConcreteBits();
  }
}

SharedFieldVersions::ConcreteBits SharedFieldVersions::element_bits(
    arrayOop array, int index) {
  if (array == NULL || !array->is_typeArray() || index < 0
      || index >= array->length()) {
    return ConcreteBits();
  }
  typeArrayOop elements = typeArrayOop(array);
  const BasicType type =
      TypeArrayKlass::cast(array->klass())->element_type();
  switch (type) {
    case T_BOOLEAN:
      return ConcreteBits(type, raw_bits(elements->bool_at(index)));
    case T_BYTE:
      return ConcreteBits(type, raw_bits(elements->byte_at(index)));
    case T_CHAR:
      return ConcreteBits(type, raw_bits(elements->char_at(index)));
    case T_SHORT:
      return ConcreteBits(type, raw_bits(elements->short_at(index)));
    case T_INT:
      return ConcreteBits(type, raw_bits(elements->int_at(index)));
    case T_LONG:
      return ConcreteBits(type, raw_bits(elements->long_at(index)));
    case T_FLOAT:
      return ConcreteBits(type, raw_bits(elements->float_at(index)));
    case T_DOUBLE:
      return ConcreteBits(type, raw_bits(elements->double_at(index)));
    default:
      return ConcreteBits();
  }
}

namespace {

// The referent one reference cell holds right now.
oop cell_referent(const SharedFieldVersions::Location &location,
                  const SharedFieldVersions::Cell &cell) {
  if (cell.holder == NULL) return NULL;
  if (location.kind == SharedFieldVersions::LOC_ARRAY_ELEMENT) {
    if (!cell.holder->is_objArray()) return NULL;
    objArrayOop elements = objArrayOop(cell.holder);
    return location.slot >= 0 && location.slot < elements->length()
        ? elements->obj_at(location.slot) : (oop) NULL;
  }
  return cell.holder->obj_field(location.slot);
}

} // anonymous namespace

SharedFieldVersions::ConcreteBits SharedFieldVersions::cell_word(
    const Location &location, const Cell &cell) {
  if (cell.holder == NULL) return ConcreteBits();
  if (location.kind == LOC_ARRAY_ELEMENT) {
    return cell.holder->is_typeArray()
        ? element_bits(arrayOop(cell.holder), location.slot)
        : (cell.boxed ? boxed_word(cell_referent(location, cell))
                      : ConcreteBits());
  }
  if (cell.type == T_OBJECT || cell.type == T_ARRAY) {
    return cell.boxed ? boxed_word(cell_referent(location, cell))
                      : ConcreteBits();
  }
  return field_bits(cell.holder, location.slot, cell.type);
}

Expression *SharedFieldVersions::cell_value(const Location &location,
                                            const Cell &cell,
                                            const ConcreteBits &word) {
  if (word.stated()) return primitive_expression(word.type, word.bits);
  if (cell.holder == NULL) return NULL;
  return reference_expression(cell_referent(location, cell));
}

const char *SharedFieldVersions::location_kind_name(int kind) {
  switch (kind) {
    case LOC_INSTANCE_FIELD: return "INSTANCE_FIELD";
    case LOC_STATIC_FIELD:   return "STATIC_FIELD";
    case LOC_ARRAY_ELEMENT:  return "ARRAY_ELEMENT";
    case LOC_MAP_STATE:      return "MAP_STATE";
    default:                 return "UNKNOWN";
  }
}

const char *SharedFieldVersions::version_kind_name(int kind) {
  switch (kind) {
    case VERSION_INITIAL:    return "INITIAL";
    case VERSION_WRITE:      return "WRITE";
    case VERSION_RMW:        return "RMW";
    case VERSION_STATE:      return "STATE";
    case VERSION_UNOBSERVED: return "UNOBSERVED";
    default:                 return "UNKNOWN";
  }
}

std::string SharedFieldVersions::version_label(const Version &version) {
  const std::string kind(version_kind_name(version.version_kind));
  if (version.version_kind != VERSION_STATE || version.operation.empty()) {
    return kind;
  }
  return kind + "_" + version.operation;
}

// ---------------------------------------------------------------------------
// Guarded stores.
// ---------------------------------------------------------------------------

// Store method -> the branch sites its stores are control-dependent on.
// Session state under _mutex, replaced wholesale by an install.
typedef std::map<std::string, std::vector<std::string> > GuardedStoreTable;
static GuardedStoreTable _guarded_store_sites;
// Method -> its row of the table, or NULL for a method the table does not
// name; filled on first ask, emptied with the table.
typedef std::map<Method *, const std::vector<std::string> *> GuardedMethodMemo;
static GuardedMethodMemo _guarded_methods;

int SharedFieldVersions::install_guarded_store_sites(const char *table) {
  MAP_LOCK;
  _guarded_store_sites.clear();
  _guarded_methods.clear();
  _guarded_store_count = 0;
  if (table == NULL) return 0;
  std::string text(table);
  size_t at = 0;
  while (at < text.size()) {
    size_t end = text.find('\n', at);
    if (end == std::string::npos) end = text.size();
    std::string line = text.substr(at, end - at);
    at = end + 1;
    size_t tab = line.find('\t');
    if (tab == std::string::npos || tab == 0) continue;
    std::string method = line.substr(0, tab);
    // The remaining TAB-separated fields are the guard ids, which are Soot
    // signatures with commas in their parameter lists: nothing else splits.
    std::vector<std::string> guards;
    size_t from = tab + 1;
    while (from <= line.size()) {
      size_t next = line.find('\t', from);
      if (next == std::string::npos) next = line.size();
      std::string guard = line.substr(from, next - from);
      if (!guard.empty()) guards.push_back(guard);
      from = next + 1;
    }
    // A store method with no guard site admits nothing; drop the row.
    if (!guards.empty()) _guarded_store_sites[method] = guards;
  }
  _guarded_store_count = (int) _guarded_store_sites.size();
  return _guarded_store_count;
}

bool SharedFieldVersions::guarded_store_admitted(Method *store_method) {
  if (ConcolicMngr::ctx == NULL || _guarded_store_count == 0) return false;
  std::vector<std::string> guards;
  if (store_method != NULL) {
    MAP_LOCK;
    GuardedMethodMemo::const_iterator memo = _guarded_methods.find(store_method);
    const std::vector<std::string> *row = NULL;
    if (memo != _guarded_methods.end()) {
      row = memo->second;
    } else {
      ResourceMark rm;
      std::string method = std::string(
          store_method->method_holder()->name()->as_C_string()) + "#"
          + store_method->name()->as_C_string()
          + store_method->signature()->as_C_string();
      GuardedStoreTable::const_iterator found =
          _guarded_store_sites.find(method);
      row = found == _guarded_store_sites.end() ? NULL : &found->second;
      _guarded_methods[store_method] = row;
    }
    if (row == NULL) return false;
    guards = *row;
  } else {
    ThreadContext::CodeSite standing;
    if (!ConcolicMngr::ctx->current_code_site(&standing)) return false;
    std::string method = standing.class_name + "#" + standing.method_name
        + standing.method_descriptor;
    MAP_LOCK;
    GuardedStoreTable::const_iterator found =
        _guarded_store_sites.find(method);
    if (found == _guarded_store_sites.end()) return false;
    guards = found->second;
  }
  // Outside the lock: asking the thread context is not this store's business
  // to do while holding the version store.
  for (size_t index = 0; index < guards.size(); ++index) {
    if (ConcolicMngr::ctx->branch_site_decided(guards[index])) return true;
  }
  return false;
}

SharedFieldVersions::EventSite SharedFieldVersions::current_site() {
  EventSite site;
  if (ConcolicMngr::ctx == NULL) return site;
  ThreadContext::CodeSite standing;
  if (!ConcolicMngr::ctx->current_code_site(&standing)) return site;
  site.class_name = standing.class_name;
  site.method_name = standing.method_name;
  site.method_descriptor = standing.method_descriptor;
  site.bci = standing.bci;
  return site;
}

// One writer for the `site` member, so a version, a read record and a
// ReadFromExpression spell it identically.  Absent when the event named no
// site: an unstated site is not bci 0 of an unnamed method.
void SharedFieldVersions::write_site(
    rapidjson::Writer<rapidjson::StringBuffer> &writer,
    const EventSite &site) {
  if (!site.stated()) return;
  writer.Key("site");
  writer.StartObject();
  writer.Key("className");
  writer.String(site.class_name.c_str());
  writer.Key("methodName");
  writer.String(site.method_name.c_str());
  writer.Key("methodDescriptor");
  writer.String(site.method_descriptor.c_str());
  writer.Key("bci");
  writer.Int(site.bci);
  writer.EndObject();
}

// ---------------------------------------------------------------------------
// Read-outs.
// ---------------------------------------------------------------------------

// One `SHARED_FIELD_VERSIONS` envelope, written into a caller's document and
// left open: the single-location answer and the whole read-out both close it
// their own way, so they emit byte-identical envelopes.  Returns true when
// the envelope was cut short by `budget_bytes` (0 = the default bound).
bool SharedFieldVersions::write_versions_envelope(
    rapidjson::Writer<rapidjson::StringBuffer> &writer,
    const rapidjson::StringBuffer &buffer,
    VmExpressionArtifactScope &expression_artifact,
    const Location &location, const Slot &slot, bool selected,
    size_t budget_bytes) {
  using namespace rapidjson;
  const size_t bound = budget_bytes == 0
      ? MAX_VERSION_ENVELOPE_BYTES : budget_bytes;
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("SHARED_FIELD_VERSIONS");
  writer.Key("sessionId");
  writer.Int64(GlobalSymbolicSession::session_id());
  writer.Key("selected");
  writer.Bool(selected);
  writer.Key("location");
  writer.StartObject();
  writer.Key("ownerSymRid");
  writer.Int64((jlong) location.owner);
  writer.Key("slot");
  writer.Int(location.slot);
  writer.Key("locationKind");
  writer.String(location_kind_name(location.kind));
  writer.EndObject();
  writer.Key("writerSetComplete");
  writer.Bool(slot.writer_set_complete);
  if (!slot.writer_set_complete) {
    // Why: the first writer the log could not name (UNOBSERVED_WRITE, a
    // detected unmodeled mutation, the version bound).
    writer.Key("incompleteReason");
    writer.String(slot.incomplete_reason.c_str());
  }
  writer.Key("versions");
  writer.StartArray();
  bool serialization_truncated = false;
  const VersionList &versions = slot.versions;
  for (size_t index = 0; index < versions.size(); ++index) {
    if (envelope_bytes(buffer, expression_artifact) >= bound) {
      serialization_truncated = true;
      break;
    }
    const Version &version = versions[index];
    writer.StartObject();
    writer.Key("fieldVersionId");
    writer.Int64(version.version_id);
    writer.Key("versionKind");
    writer.String(version_label(version).c_str());
    writer.Key("writerContextId");
    writer.Int64(version.writer.context_id);
    writer.Key("regionId");
    writer.String(version.writer.region_id.c_str());
    writer.Key("taskId");
    writer.String(version.writer.task_id.c_str());
    writer.Key("regionEnterEventId");
    writer.Int64(version.writer.region_enter_event_id);
    write_site(writer, version.writer.site);
    // Whatever this engine has to say about the contents that predate the
    // log: a stated count, a refusal over the bound, or a class it cannot
    // read.  `stated` is true only for a stated count (D2: a refusal used to
    // read as a stated empty base).
    if (version.initial_snapshot_present) {
      writer.Key("initialSnapshot");
      writer.StartObject();
      writer.Key("stated");
      writer.Bool(version.initial_snapshot_stated);
      writer.Key("entries");
      writer.Int(version.initial_snapshot_entries);
      writer.Key("truncated");
      writer.Bool(version.initial_snapshot_truncated);
      if (!version.initial_snapshot_unsupported_class.empty()) {
        writer.Key("unsupportedClass");
        writer.String(
            version.initial_snapshot_unsupported_class.c_str());
      }
      writer.EndObject();
    }
    writer.Key("expression");
    if (version.value == NULL) {
      writer.Null();
    } else {
      version.value->serialize(writer);
    }
    writer.Key("pathGuard");
    if (envelope_bytes(buffer, expression_artifact) >= bound) {
      // Keep the version structurally valid; the envelope flag below makes
      // this null unusable as an allegedly empty guard.
      writer.Null();
      serialization_truncated = true;
    } else if (version.path_guard == NULL) {
      // The empty conjunction, stated so it is never "not recorded".
      writer.Null();
    } else {
      version.path_guard->serialize(writer);
    }
    writer.EndObject();
    if (serialization_truncated) break;
  }
  writer.EndArray();
  writer.Key("readLogTruncated");
  writer.Bool(!slot.read_log_complete);
  writer.Key("reads");
  writer.StartArray();
  for (size_t index = 0; index < slot.reads.size(); ++index) {
    if (envelope_bytes(buffer, expression_artifact) >= bound) {
      serialization_truncated = true;
      break;
    }
    const ReadRecord &read = slot.reads[index];
    writer.StartObject();
    writer.Key("readEventId");
    writer.Int64(read.read_event_id);
    writer.Key("readerContextId");
    writer.Int64(read.reader.context_id);
    writer.Key("regionId");
    writer.String(read.reader.region_id.c_str());
    writer.Key("taskId");
    writer.String(read.reader.task_id.c_str());
    writer.Key("regionEnterEventId");
    writer.Int64(read.reader.region_enter_event_id);
    write_site(writer, read.reader.site);
    writer.EndObject();
  }
  writer.EndArray();
  // After both arrays: it reports either being cut short.  Triaged by Java
  // as EXPRESSION_SERIALIZATION_TRUNCATED.
  writer.Key("serializationTruncated");
  writer.Bool(serialization_truncated);
  return serialization_truncated;
}

namespace {

// The highest event id a location carries: its order and resume point.
// Event ids are unique per location -- a version id and a read id are each
// appended to exactly one slot -- so no two locations share one.
jlong location_high_event(const SharedFieldVersions::Slot &slot) {
  jlong high = 0;
  for (size_t i = 0; i < slot.versions.size(); ++i) {
    if (slot.versions[i].version_id > high) high = slot.versions[i].version_id;
  }
  for (size_t i = 0; i < slot.reads.size(); ++i) {
    if (slot.reads[i].read_event_id > high) high = slot.reads[i].read_event_id;
  }
  return high;
}

struct TrackedLocation {
  SharedFieldVersions::Location location;
  SharedFieldVersions::Slot slot;
  jlong high;
  TrackedLocation() : high(0) {}
};

bool by_high_event(const TrackedLocation &a, const TrackedLocation &b) {
  return a.high < b.high;
}

} // anonymous namespace

std::string SharedFieldVersions::tracked_locations(jlong after_event_id,
                                                   jint max_bytes) {
  using namespace rapidjson;
  // The locations, under the map lock; each one's contents under its own
  // stripe (the map lock is never held around a stripe).  Serialized with
  // no lock at all: an Expression is not rendered under the version store.
  std::vector<Location> locations;
  {
    MAP_LOCK;
    if (_open) {
      for (SlotStore::const_iterator it = _slots.begin(); it != _slots.end();
           ++it) {
        locations.push_back(it->first);
      }
    }
  }
  std::vector<TrackedLocation> selected;
  for (size_t index = 0; index < locations.size(); ++index) {
    lock(locations[index]);
    Slot *slot = find_slot(locations[index]);
    if (slot != NULL) {
      const jlong high = location_high_event(*slot);
      // Selected when anything it carries is at or after the watermark.
      if (after_event_id <= 0 || high >= after_event_id) {
        TrackedLocation entry;
        entry.location = locations[index];
        entry.slot = *slot;
        entry.high = high;
        selected.push_back(entry);
      }
    }
    unlock(locations[index]);
  }
  // By the highest event, the key the selection is made on (D3: ordering by
  // the lowest and resuming at it repeated pages and could step back).
  std::sort(selected.begin(), selected.end(), by_high_event);

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  VmExpressionArtifactScope expression_artifact;
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("SHARED_TRACKED_LOCATIONS");
  writer.Key("sessionId");
  writer.Int64(GlobalSymbolicSession::session_id());
  writer.Key("authority");
  writer.String("VM_TRACKED_LOCATION_VERSIONS_V1");
  writer.Key("locations");
  writer.StartArray();

  const size_t budget = max_bytes > 0 ? (size_t) max_bytes : 0;
  bool complete = true;
  jlong next_after = 0;
  size_t emitted = 0;
  for (size_t index = 0; index < selected.size(); ++index) {
    // Stop at a location boundary, never inside one; the first location is
    // always emitted, so a budget smaller than one envelope still progresses.
    if (budget != 0 && emitted > 0
        && envelope_bytes(buffer, expression_artifact) >= budget) {
      complete = false;
      // One past the last emitted location's highest event: every emitted
      // location is below it and every unemitted one at or above it.
      next_after = selected[index - 1].high + 1;
      break;
    }
    const TrackedLocation &entry = selected[index];
    // Each envelope keeps its own per-envelope bound: the document budget is
    // a boundary between locations, never a cut inside one.
    write_versions_envelope(writer, buffer, expression_artifact,
                            entry.location, entry.slot, true, 0);
    writer.EndObject();
    emitted++;
  }
  writer.EndArray();
  writer.Key("locationCount");
  writer.Int64((jlong) emitted);
  writer.Key("complete");
  writer.Bool(complete);
  writer.Key("nextAfterEventId");
  writer.Int64(next_after);
  expression_artifact.write_table(writer);
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

std::string SharedFieldVersions::describe(const Location &location) {
  using namespace rapidjson;
  Slot copy;
  bool selected = false;
  if (location.is_valid()) {
    lock(location);
    Slot *slot = find_slot(location);
    if (slot != NULL) {
      selected = true;
      copy = *slot;
    }
    unlock(location);
  }

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  VmExpressionArtifactScope expression_artifact;
  write_versions_envelope(writer, buffer, expression_artifact, location,
                          copy, selected, 0);
  expression_artifact.write_table(writer);
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

// ---------------------------------------------------------------------------
// The Java-facing evidence API.
// ---------------------------------------------------------------------------

namespace {

/**
 * Resolves the location a Java caller named into an addressable slot.  A
 * static field is addressed as `getstatic` addresses it: the declaring
 * class's mirror and the mirror-relative offset.
 */
bool resolve_field_location(oop owner_oop, const char *declaring_class,
                            const char *field_name, const char *descriptor,
                            SharedFieldVersions::Location *location,
                            fieldDescriptor *field, oop *carrier_owner) {
  if (owner_oop == NULL) return false;

  const std::string holder_name(declaring_class);
  const std::string name(field_name);
  const std::string signature(descriptor);

  // Static: the caller handed us a Class object.
  if (owner_oop->klass() == SystemDictionary::Class_klass()
      && !java_lang_Class::is_primitive(owner_oop)) {
    Klass *named = java_lang_Class::as_Klass(owner_oop);
    Thread *thread = Thread::current();
    TempNewSymbol symbol_name = SymbolTable::new_symbol(name.c_str(), thread);
    TempNewSymbol symbol_signature =
        SymbolTable::new_symbol(signature.c_str(), thread);
    for (Klass *candidate = named; candidate != NULL;
         candidate = candidate->super()) {
      if (!candidate->oop_is_instance()) continue;
      ResourceMark rm;
      if (holder_name != candidate->external_name()) continue;
      InstanceKlass *holder = InstanceKlass::cast(candidate);
      if (!holder->find_local_field(symbol_name, symbol_signature, field)) {
        return false;
      }
      if (!field->is_static()) return false;
      *carrier_owner = holder->java_mirror();
      *location = SharedFieldVersions::Location(
          NULL_SYM_RID, field->offset(),
          SharedFieldVersions::LOC_STATIC_FIELD);
      return true;
    }
    return false;
  }

  Klass *declaring = OopUtils::get_local_fd_by_name(
      owner_oop, holder_name, name, signature, *field);
  if (declaring == NULL || field->is_static()) return false;
  *carrier_owner = owner_oop;
  *location = SharedFieldVersions::Location(
      NULL_SYM_RID, field->offset(),
      SharedFieldVersions::LOC_INSTANCE_FIELD);
  return true;
}

} // anonymous namespace

std::string ConcolicMngr::getTrackedLocationVersions(jlong after_event_id,
                                                     jint max_bytes) {
  return SharedFieldVersions::tracked_locations(after_event_id, max_bytes);
}

std::string ConcolicMngr::getSharedMapVersions(Handle map) {
  SharedFieldVersions::Location location;
  if (has_active_context() && !map.is_null()) {
    // Resolved, never allocated: asking what a location recorded must not be
    // the thing that gives it an identity.
    location = ContainerSupport::state_location(map());
  }
  return SharedFieldVersions::describe(location);
}

std::string ConcolicMngr::getSharedFieldVersions(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor) {
  SharedFieldVersions::Location location;
  if (has_active_context() && !owner.is_null()
      && declaring_class != NULL && field_name != NULL
      && descriptor != NULL) {
    ResourceMark rm;
    fieldDescriptor field;
    oop carrier_owner = NULL;
    if (resolve_field_location(owner(), declaring_class, field_name,
                               descriptor, &location, &field,
                               &carrier_owner)) {
      SymInstance *shadow = ctx->find_sym_inst(carrier_owner);
      location.owner = shadow == NULL ? NULL_SYM_RID : shadow->get_sym_rid();
    }
  }
  return SharedFieldVersions::describe(location);
}

std::string ConcolicMngr::getSharedElementVersions(Handle array, jint index) {
  SharedFieldVersions::Location location;
  if (has_active_context() && !array.is_null() && array()->is_array()
      && index >= 0) {
    SymArr *shadow = ctx->find_sym_array(arrayOop(array()));
    if (shadow != NULL) {
      location = SharedFieldVersions::Location(
          shadow->get_sym_rid(), index,
          SharedFieldVersions::LOC_ARRAY_ELEMENT);
    }
  }
  return SharedFieldVersions::describe(location);
}

#endif // ENABLE_CONCOLIC
