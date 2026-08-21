#ifdef ENABLE_CONCOLIC

#include "concolic/sharedFieldVersions.hpp"

#include "classfile/javaClasses.hpp"
#include "classfile/symbolTable.hpp"
#include "classfile/systemDictionary.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/eventLedger.hpp"
#include "concolic/exp/readFromExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "oops/arrayKlass.hpp"
#include "oops/instanceKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "runtime/fieldDescriptor.hpp"
#include "utilities/ostream.hpp"
#include "webridge/utils/rapidjson/stringbuffer.h"
#include "webridge/utils/rapidjson/writer.h"

bool SharedFieldVersions::_open = false;
SharedFieldVersions::SlotStore SharedFieldVersions::_slots;
volatile int SharedFieldVersions::_carrier_count = 0;
volatile int SharedFieldVersions::_planned_field_read_count = 0;
volatile int SharedFieldVersions::_field_evidence_alias_count = 0;
pthread_mutex_t SharedFieldVersions::_mutex = PTHREAD_MUTEX_INITIALIZER;
SharedFieldVersions::PlannedFieldReadStore
    SharedFieldVersions::_planned_field_reads;
SharedFieldVersions::FieldEvidenceAliasStore
    SharedFieldVersions::_field_evidence_aliases;

namespace {

// One location can retain many versions, each with a value and a path guard.
// Expression::serialize bounds each root independently; this envelope bound
// prevents those individually bounded roots from accumulating into one
// unbounded native StringBuffer.
static const size_t MAX_VERSION_ENVELOPE_BYTES = 32u * 1024u * 1024u;

class VersionLock {
public:
  VersionLock(pthread_mutex_t *mutex) : _mutex(mutex) {
    pthread_mutex_lock(_mutex);
  }
  ~VersionLock() { pthread_mutex_unlock(_mutex); }
private:
  pthread_mutex_t *_mutex;
};

bool descriptor_matches_type(const std::string &descriptor, BasicType type) {
  if (descriptor.empty()) return false;
  switch (descriptor[0]) {
    case 'Z': return type == T_BOOLEAN;
    case 'B': return type == T_BYTE;
    case 'C': return type == T_CHAR;
    case 'S': return type == T_SHORT;
    case 'I': return type == T_INT;
    case 'J': return type == T_LONG;
    case 'F': return type == T_FLOAT;
    case 'D': return type == T_DOUBLE;
    case 'L':
    case '[': return type == T_OBJECT || type == T_ARRAY;
    default:  return false;
  }
}

bool fingerprints_equal(const SharedFieldVersions::Fingerprint &left,
                        const SharedFieldVersions::Fingerprint &right) {
  return left.kind == right.kind && left.bits == right.bits;
}

// A scheduled primitive edge still has to replay the producer's concrete
// value.  Reference transport may materialize an isomorphic destination
// object with a different identity, so references validate descriptor and
// nullness rather than requiring the source oop's session id.
bool planned_value_matches(const std::string &descriptor,
                           const SharedFieldVersions::Fingerprint &producer,
                           const SharedFieldVersions::Fingerprint &observed) {
  if (descriptor.empty()) return false;
  if (descriptor[0] == 'L' || descriptor[0] == '[') {
    return producer.kind == SharedFieldVersions::FP_NULL
        ? observed.kind == SharedFieldVersions::FP_NULL
        : observed.kind != SharedFieldVersions::FP_NULL;
  }
  return producer.kind == SharedFieldVersions::FP_PRIMITIVE
      && fingerprints_equal(producer, observed);
}

} // anonymous namespace

#define VERSION_LOCK VersionLock version_guard(&_mutex)

void SharedFieldVersions::open_session() {
  VERSION_LOCK;
  guarantee(_slots.empty(), "versions outlived the previous session");
  guarantee(_planned_field_reads.empty(),
            "planned field reads outlived the previous session");
  guarantee(_field_evidence_aliases.empty(),
            "field evidence aliases outlived the previous session");
  _carrier_count = 0;
  _planned_field_read_count = 0;
  _field_evidence_alias_count = 0;
  _open = true;
}

void SharedFieldVersions::close_session() {
  VERSION_LOCK;
  // Every Expression named here belongs to the session arena and is freed with
  // it.  Dropping the records is exactly a decision to stop naming them.
  _planned_field_reads.clear();
  _field_evidence_aliases.clear();
  _slots.clear();
  _carrier_count = 0;
  _planned_field_read_count = 0;
  _field_evidence_alias_count = 0;
  _open = false;
}

SharedFieldVersions::Slot *SharedFieldVersions::find_slot_locked(
    const Location &location) {
  SlotStore::iterator found = _slots.find(location);
  return found == _slots.end() ? NULL : &found->second;
}

int SharedFieldVersions::carrier_count() {
  VERSION_LOCK;
  return (int) _slots.size();
}

bool SharedFieldVersions::is_carrier(const Location &location) {
  if (!location.is_valid()) return false;
  VERSION_LOCK;
  return _open && _slots.find(location) != _slots.end();
}

jlong SharedFieldVersions::select_carrier(const Location &location,
                                          Expression *initial,
                                          const Fingerprint &fingerprint,
                                          const char *descriptor) {
  if (!location.is_valid()) return 0;

  // Built before the lock: the ledger event this version *is*, and the writer
  // evidence copied out of this thread's context.  Neither may happen inside
  // the critical section, and the ledger lock is therefore never held together
  // with this store's lock.  A fieldVersionId is an event id: one id space.
  jlong version_id = EventLedger::record(
      EventLedger::EVENT_FIELD_WRITE, location.owner, location.slot,
      "INITIAL");
  if (version_id == 0) version_id = GlobalSymbolicSession::next_event_id();
  Version version;
  version.version_id = version_id;
  version.version_kind = VERSION_INITIAL;
  version.value = initial;
  version.path_guard = NULL;
  version.fingerprint = fingerprint;
  version.volatile_write = false;
  if (ConcolicMngr::ctx != NULL) {
    version.writer_context_id = ConcolicMngr::ctx->get_context_id();
    version.writer_java_thread_id =
        ConcolicMngr::ctx->get_owner_java_thread_id();
    version.region_id = ConcolicMngr::ctx->get_region_id();
    version.task_id = ConcolicMngr::ctx->get_task_id();
    version.writer_step = ConcolicMngr::ctx->tick_clock();
    version.writer_clock = ConcolicMngr::ctx->clock();
  }

  VERSION_LOCK;
  if (!_open) return 0;
  if (_slots.find(location) != _slots.end()) return 0;
  Slot &slot = _slots[location];
  slot.descriptor = descriptor == NULL ? "" : descriptor;
  slot.writer_set_complete = true;
  slot.versions.push_back(version);
  slot.versions_observed++;
  _carrier_count = (int) _slots.size();
  return version_id;
}

jlong SharedFieldVersions::publish(const Location &location, Expression *value,
                                   Expression *path_guard,
                                   const Fingerprint &fingerprint,
                                   bool volatile_write, int version_kind,
                                   const char *operation) {
  if (!location.is_valid() || value == NULL) return 0;

  const bool named = operation != NULL && operation[0] != '\0';
  jlong version_id = EventLedger::record(
      EventLedger::EVENT_FIELD_WRITE, location.owner, location.slot,
      named ? operation : version_kind_name(version_kind));
  if (version_id == 0) version_id = GlobalSymbolicSession::next_event_id();
  Version version;
  version.version_id = version_id;
  version.version_kind = version_kind;
  if (named) version.operation = operation;
  version.value = value;
  version.path_guard = path_guard;
  version.fingerprint = fingerprint;
  version.volatile_write = volatile_write;
  if (ConcolicMngr::ctx != NULL) {
    version.writer_context_id = ConcolicMngr::ctx->get_context_id();
    version.writer_java_thread_id =
        ConcolicMngr::ctx->get_owner_java_thread_id();
    version.region_id = ConcolicMngr::ctx->get_region_id();
    version.task_id = ConcolicMngr::ctx->get_task_id();
    version.writer_step = ConcolicMngr::ctx->tick_clock();
    version.writer_clock = ConcolicMngr::ctx->clock();
  }

  VERSION_LOCK;
  if (!_open) return 0;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL) return 0;
  slot->versions.push_back(version);
  slot->versions_observed++;
  if (slot->versions.size() > MAX_VERSIONS_PER_LOCATION) {
    // A dropped writer is a writer a later read can no longer name.  Say so
    // permanently rather than answering as if the set were still whole.
    slot->versions.erase(slot->versions.begin());
    slot->writer_set_complete = false;
    slot->versions_dropped++;
  }
  return version_id;
}

bool SharedFieldVersions::mark_writer_set_incomplete(
    const Location &location) {
  if (!location.is_valid()) return false;
  VERSION_LOCK;
  if (!_open) return false;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL) return false;
  slot->writer_set_complete = false;
  return true;
}

bool SharedFieldVersions::versions_of(const Location &location,
                                      VersionList *out,
                                      bool *writer_set_complete) {
  if (out == NULL) return false;
  out->clear();
  if (writer_set_complete != NULL) *writer_set_complete = true;
  if (!location.is_valid()) return false;
  VERSION_LOCK;
  if (!_open) return false;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL) return false;
  *out = slot->versions;
  if (writer_set_complete != NULL) {
    *writer_set_complete = slot->writer_set_complete;
  }
  return true;
}

jlong SharedFieldVersions::current_state_version(
    const Location &location, Expression *current,
    const std::string &task_id) {
  if (!location.is_valid() || current == NULL) {
    return SELECT_MISSING_METADATA;
  }
  VERSION_LOCK;
  if (!_open) return SELECT_NO_ACTIVE_CONTEXT;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL) return SELECT_VERSION_NOT_FOUND;

  jlong match = 0;
  for (size_t index = 0; index < slot->versions.size(); ++index) {
    const Version &version = slot->versions[index];
    if (version.version_kind != VERSION_STATE || version.value != current
        || version.task_id != task_id) {
      continue;
    }
    if (match != 0) return SELECT_VERSION_AMBIGUOUS;
    match = version.version_id;
  }
  return match == 0 ? SELECT_VERSION_NOT_FOUND : match;
}

jlong SharedFieldVersions::lookup_state_version(
    jlong version_id, Location *source_location, Expression **state) {
  if (source_location == NULL || state == NULL || version_id <= 0) {
    return SELECT_MISSING_METADATA;
  }
  *source_location = Location();
  *state = NULL;
  VERSION_LOCK;
  if (!_open) return SELECT_NO_ACTIVE_CONTEXT;

  bool found = false;
  for (SlotStore::const_iterator slot = _slots.begin();
       slot != _slots.end(); ++slot) {
    for (size_t index = 0; index < slot->second.versions.size(); ++index) {
      const Version &version = slot->second.versions[index];
      if (version.version_id != version_id) continue;
      if (version.version_kind != VERSION_STATE || version.value == NULL) {
        return SELECT_UNSUPPORTED_TARGET;
      }
      if (found) return SELECT_VERSION_AMBIGUOUS;
      found = true;
      *source_location = slot->first;
      *state = version.value;
    }
  }
  return found ? version_id : SELECT_VERSION_NOT_FOUND;
}

jlong SharedFieldVersions::record_planned_state_read(
    const Location &source_location, jlong version_id,
    const char *selected_edge_id) {
  if (!source_location.is_valid() || version_id <= 0) {
    return SELECT_MISSING_METADATA;
  }
  if (selected_edge_id == NULL || selected_edge_id[0] == '\0') {
    return SELECT_INVALID_EDGE;
  }
  if (ConcolicMngr::ctx == NULL) return SELECT_NO_ACTIVE_CONTEXT;

  // This read is explicit schedule evidence, so the chosen version and edge
  // are inputs to the decision rather than inferred from concrete equality.
  ConcolicMngr::ctx->tick_clock();
  jlong read_event_id = EventLedger::record(
      EventLedger::EVENT_FIELD_READ, source_location.owner,
      source_location.slot, "PLANNED_PRODUCER_STATE");
  if (read_event_id == 0) {
    read_event_id = GlobalSymbolicSession::next_event_id();
  }
  EventLedger::add_observed_edge(
      version_id, read_event_id, EventLedger::EDGE_FIELD_READ_FROM);

  ReadRecord record;
  record.read_event_id = read_event_id;
  record.reader_context_id = ConcolicMngr::ctx->get_context_id();
  record.reader_java_thread_id =
      ConcolicMngr::ctx->get_owner_java_thread_id();
  record.region_id = ConcolicMngr::ctx->get_region_id();
  record.resolution = RESOLVE_EXACT;
  record.reason = REASON_PLANNED_PRODUCER_STATE;
  record.chosen_version_id = version_id;
  record.candidate_count = 1;
  record.selected_edge_id = selected_edge_id;

  VERSION_LOCK;
  if (!_open) return SELECT_NO_ACTIVE_CONTEXT;
  Slot *slot = find_slot_locked(source_location);
  if (slot == NULL) return SELECT_VERSION_NOT_FOUND;
  slot->reads.push_back(record);
  slot->reads_observed++;
  if (slot->reads.size() > MAX_READS_PER_LOCATION) {
    slot->reads.erase(slot->reads.begin());
    slot->read_log_complete = false;
    slot->reads_dropped++;
  }
  return read_event_id;
}

jlong SharedFieldVersions::current_field_version(
    const Location &location, Expression *current,
    const Fingerprint &observed, const std::string &task_id,
    const char *descriptor) {
  if (!location.is_valid() || descriptor == NULL || descriptor[0] == '\0') {
    return SELECT_MISSING_METADATA;
  }
  VERSION_LOCK;
  if (!_open) return SELECT_NO_ACTIVE_CONTEXT;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL || slot->versions.empty()) return SELECT_VERSION_NOT_FOUND;
  if (location.kind != LOC_INSTANCE_FIELD
      && location.kind != LOC_STATIC_FIELD) {
    return SELECT_UNSUPPORTED_TARGET;
  }
  if (slot->descriptor != descriptor) return SELECT_UNSUPPORTED_TARGET;

  // Every selected scalar store publishes after its concrete write.  The last
  // retained version is therefore the only version this pure query may call
  // current; searching backward by concrete equality would turn equal writes
  // into ambiguous provenance.
  const Version &version = slot->versions.back();
  if (version.version_kind == VERSION_STATE || version.value == NULL
      || version.task_id != task_id) {
    return SELECT_VERSION_NOT_FOUND;
  }
  if (current != NULL && current != version.value) {
    return SELECT_VERSION_NOT_FOUND;
  }
  if (!planned_value_matches(slot->descriptor, version.fingerprint,
                             observed)) {
    return SELECT_VERSION_NOT_FOUND;
  }
  return version.version_id;
}

jlong SharedFieldVersions::lookup_field_version(
    jlong version_id, const char *descriptor, Location *source_location,
    Version *version) {
  if (version_id <= 0 || descriptor == NULL || descriptor[0] == '\0'
      || source_location == NULL || version == NULL) {
    return SELECT_MISSING_METADATA;
  }
  *source_location = Location();
  *version = Version();
  VERSION_LOCK;
  if (!_open) return SELECT_NO_ACTIVE_CONTEXT;

  bool found = false;
  for (SlotStore::const_iterator slot = _slots.begin();
       slot != _slots.end(); ++slot) {
    if (slot->first.kind != LOC_INSTANCE_FIELD
        && slot->first.kind != LOC_STATIC_FIELD) {
      continue;
    }
    for (size_t index = 0; index < slot->second.versions.size(); ++index) {
      const Version &candidate = slot->second.versions[index];
      if (candidate.version_id != version_id) continue;
      if (slot->second.descriptor != descriptor
          || candidate.version_kind == VERSION_STATE
          || candidate.value == NULL) {
        return SELECT_UNSUPPORTED_TARGET;
      }
      if (found) return SELECT_VERSION_AMBIGUOUS;
      found = true;
      *source_location = slot->first;
      *version = candidate;
    }
  }
  return found ? version_id : SELECT_VERSION_NOT_FOUND;
}

jlong SharedFieldVersions::plan_exact_field_read(
    const Location &destination, jlong version_id, const char *descriptor,
    const char *selected_edge_id) {
  if (!destination.is_valid() || version_id <= 0
      || descriptor == NULL || descriptor[0] == '\0') {
    return SELECT_MISSING_METADATA;
  }
  if (selected_edge_id == NULL || selected_edge_id[0] == '\0') {
    return SELECT_INVALID_EDGE;
  }
  if (ConcolicMngr::ctx == NULL) return SELECT_NO_ACTIVE_CONTEXT;
  if (destination.kind != LOC_INSTANCE_FIELD
      && destination.kind != LOC_STATIC_FIELD) {
    return SELECT_UNSUPPORTED_TARGET;
  }

  VERSION_LOCK;
  if (!_open) return SELECT_NO_ACTIVE_CONTEXT;
  const bool destination_selected =
      _slots.find(destination) != _slots.end();

  Location source;
  Version producer;
  bool found = false;
  for (SlotStore::const_iterator slot = _slots.begin();
       slot != _slots.end(); ++slot) {
    if (slot->first.kind != LOC_INSTANCE_FIELD
        && slot->first.kind != LOC_STATIC_FIELD) {
      continue;
    }
    for (size_t index = 0; index < slot->second.versions.size(); ++index) {
      const Version &candidate = slot->second.versions[index];
      if (candidate.version_id != version_id) continue;
      if (slot->second.descriptor != descriptor
          || candidate.version_kind == VERSION_STATE
          || candidate.value == NULL) {
        return SELECT_UNSUPPORTED_TARGET;
      }
      if (found) return SELECT_VERSION_AMBIGUOUS;
      found = true;
      source = slot->first;
      producer = candidate;
    }
  }
  if (!found) return SELECT_VERSION_NOT_FOUND;
  const bool same_location = destination.owner == source.owner
      && destination.slot == source.slot
      && destination.kind == source.kind;
  if (destination_selected && !same_location) {
    // A separately selected destination has its own writer universe and must
    // be resolved by the normal read-from path.  The one exception is the
    // actual producer location itself: a later selected region in the same
    // workload session can read the same Java field after the producer
    // commits.  Requiring an unselected destination there rejects the exact
    // in-process shared-state edge that this API is meant to attest.
    return SELECT_UNSUPPORTED_TARGET;
  }

  PlannedFieldKey key(destination, ConcolicMngr::ctx->get_context_id());
  PlannedFieldReadStore::iterator existing = _planned_field_reads.find(key);
  if (existing != _planned_field_reads.end()) {
    if (existing->second.version_id == version_id
        && existing->second.descriptor == descriptor
        && existing->second.selected_edge_id == selected_edge_id) {
      return version_id;
    }
    return SELECT_VERSION_AMBIGUOUS;
  }

  PlannedFieldRead planned;
  planned.source = source;
  planned.version_id = version_id;
  planned.descriptor = descriptor;
  planned.selected_edge_id = selected_edge_id;
  planned.expression = producer.value;
  planned.fingerprint = producer.fingerprint;
  planned.writer_clock = producer.writer_clock;
  _planned_field_reads[key] = planned;
  _field_evidence_aliases[key] = source;
  _planned_field_read_count = (int) _planned_field_reads.size();
  _field_evidence_alias_count = (int) _field_evidence_aliases.size();
  return version_id;
}

bool SharedFieldVersions::is_planned_field_read(
    const Location &destination) {
  if (!destination.is_valid() || ConcolicMngr::ctx == NULL) return false;
  VERSION_LOCK;
  if (!_open) return false;
  PlannedFieldKey key(destination, ConcolicMngr::ctx->get_context_id());
  return _planned_field_reads.find(key) != _planned_field_reads.end();
}

bool SharedFieldVersions::consume_planned_field_read(
    const Location &destination, Expression *current_shadow,
    const Fingerprint &observed, BasicType type, ReadResult *result) {
  if (result == NULL) return false;
  *result = ReadResult();
  if (!destination.is_valid() || ConcolicMngr::ctx == NULL) return false;

  PlannedFieldRead planned;
  {
    VERSION_LOCK;
    if (!_open) return false;
    PlannedFieldKey key(destination, ConcolicMngr::ctx->get_context_id());
    PlannedFieldReadStore::iterator found = _planned_field_reads.find(key);
    if (found == _planned_field_reads.end()) return false;
    planned = found->second;

    // Explicit consumer symbolization wins over concrete producer-state
    // provenance.  This is what keeps this ABI from becoming a discovery
    // root or overwriting a separately configured symbolic shadow.
    bool valid = (current_shadow == NULL
                  || current_shadow == planned.expression)
        && descriptor_matches_type(planned.descriptor, type)
        && planned_value_matches(planned.descriptor, planned.fingerprint,
                                 observed);
    Slot *source_slot = find_slot_locked(planned.source);
    bool retained = false;
    if (source_slot != NULL) {
      for (size_t index = 0; index < source_slot->versions.size(); ++index) {
        if (source_slot->versions[index].version_id == planned.version_id
            && source_slot->versions[index].value == planned.expression) {
          retained = true;
          break;
        }
      }
    }
    _planned_field_reads.erase(found);
    _planned_field_read_count = (int) _planned_field_reads.size();
    if (!valid || !retained) {
      _field_evidence_aliases.erase(key);
      _field_evidence_alias_count = (int) _field_evidence_aliases.size();
      return false;
    }
  }

  // The getfield/getstatic that observed the value is the read event.  The
  // earlier Java admission was only a plan and intentionally allocated no
  // event or read row.
  ConcolicMngr::ctx->tick_clock();
  jlong read_event_id = EventLedger::record(
      EventLedger::EVENT_FIELD_READ, planned.source.owner,
      planned.source.slot, "PLANNED_PRODUCER_STATE");
  if (read_event_id == 0) {
    read_event_id = GlobalSymbolicSession::next_event_id();
  }
  EventLedger::add_observed_edge(
      planned.version_id, read_event_id,
      EventLedger::EDGE_FIELD_READ_FROM);

  ReadRecord record;
  record.read_event_id = read_event_id;
  record.reader_context_id = ConcolicMngr::ctx->get_context_id();
  record.reader_java_thread_id =
      ConcolicMngr::ctx->get_owner_java_thread_id();
  record.region_id = ConcolicMngr::ctx->get_region_id();
  record.resolution = RESOLVE_EXACT;
  record.reason = REASON_PLANNED_PRODUCER_STATE;
  record.chosen_version_id = planned.version_id;
  record.candidate_count = 1;
  record.selected_edge_id = planned.selected_edge_id;
  record.observed = observed;

  {
    VERSION_LOCK;
    if (!_open) return false;
    Slot *source_slot = find_slot_locked(planned.source);
    if (source_slot == NULL) return false;
    source_slot->reads.push_back(record);
    source_slot->reads_observed++;
    if (source_slot->reads.size() > MAX_READS_PER_LOCATION) {
      source_slot->reads.erase(source_slot->reads.begin());
      source_slot->read_log_complete = false;
      source_slot->reads_dropped++;
    }
  }

  result->resolution = RESOLVE_EXACT;
  result->reason = REASON_PLANNED_PRODUCER_STATE;
  result->read_event_id = read_event_id;
  result->chosen_version_id = planned.version_id;
  result->expression = planned.expression;
  result->writer_clock = planned.writer_clock;
  return true;
}

void SharedFieldVersions::cancel_planned_field_reads(
    const Location &destination) {
  if (!destination.is_valid()) return;
  VERSION_LOCK;
  for (PlannedFieldReadStore::iterator it = _planned_field_reads.begin();
       it != _planned_field_reads.end();) {
    if (!(it->first.destination < destination)
        && !(destination < it->first.destination)) {
      _field_evidence_aliases.erase(it->first);
      PlannedFieldReadStore::iterator removed = it++;
      _planned_field_reads.erase(removed);
    } else {
      ++it;
    }
  }
  for (FieldEvidenceAliasStore::iterator it =
           _field_evidence_aliases.begin();
       it != _field_evidence_aliases.end();) {
    if (!(it->first.destination < destination)
        && !(destination < it->first.destination)) {
      FieldEvidenceAliasStore::iterator removed = it++;
      _field_evidence_aliases.erase(removed);
    } else {
      ++it;
    }
  }
  _planned_field_read_count = (int) _planned_field_reads.size();
  _field_evidence_alias_count = (int) _field_evidence_aliases.size();
}

SharedFieldVersions::Location SharedFieldVersions::evidence_location(
    const Location &destination) {
  if (!destination.is_valid() || ConcolicMngr::ctx == NULL) {
    return destination;
  }
  VERSION_LOCK;
  if (!_open) return destination;
  PlannedFieldKey key(destination, ConcolicMngr::ctx->get_context_id());
  FieldEvidenceAliasStore::const_iterator found =
      _field_evidence_aliases.find(key);
  return found == _field_evidence_aliases.end()
      ? destination : found->second;
}

const char *SharedFieldVersions::resolution_name(int resolution) {
  switch (resolution) {
    case RESOLVE_EXACT:   return "EXACT";
    case RESOLVE_GUARDED: return "GUARDED";
    default:              return "NONE";
  }
}

const char *SharedFieldVersions::read_reason_name(int reason) {
  switch (reason) {
    case REASON_UNIQUE_VERSION:       return "UNIQUE_VERSION";
    case REASON_VALUE_DISTINGUISHED:  return "VALUE_DISTINGUISHED";
    case REASON_SYNC_ORDERED:         return "SYNC_ORDERED";
    case REASON_AMBIGUOUS_WRITERS:    return "AMBIGUOUS_WRITERS";
    case REASON_UNTRACKED_WRITER:     return "UNTRACKED_WRITER";
    case REASON_INCOMPLETE_WRITER_SET:return "INCOMPLETE_WRITER_SET";
    case REASON_PLANNED_PRODUCER_STATE:return "PLANNED_PRODUCER_STATE";
    default:                          return "NOT_SELECTED";
  }
}

bool SharedFieldVersions::plan_read(const Location &location,
                                    const Fingerprint &observed,
                                    ReadPlan *plan) {
  if (plan == NULL) return false;
  *plan = ReadPlan();
  if (!location.is_valid() || ConcolicMngr::ctx == NULL) return false;

  VersionList versions;
  bool complete = true;
  if (!versions_of(location, &versions, &complete) || versions.empty()) {
    return false;
  }

  const jlong reader_context = ConcolicMngr::ctx->get_context_id();
  const VectorClock &reader_clock = ConcolicMngr::ctx->clock();
  // A read is an ordered action of this thread like any other, and it enters
  // the same event space as the writes it is about to be resolved against.
  ConcolicMngr::ctx->tick_clock();
  plan->read_event_id = EventLedger::record(
      EventLedger::EVENT_FIELD_READ, location.owner, location.slot, "READ");
  if (plan->read_event_id == 0) {
    plan->read_event_id = GlobalSymbolicSession::next_event_id();
  }

  // ---- program order -----------------------------------------------------
  // Of this thread's own writes only the last can be read by this thread:
  // intra-thread coherence guarantees a thread sees its own most recent store.
  // Another thread's earlier write is *not* excluded the same way -- a racing
  // read may legally observe a stale value -- so only the reader's own context
  // is filtered here.  Ordering across threads is a happens-before question,
  // handled below.
  jlong own_latest = 0;
  for (size_t index = 0; index < versions.size(); ++index) {
    if (versions[index].writer_context_id == reader_context
        && versions[index].version_id > own_latest) {
      own_latest = versions[index].version_id;
    }
  }

  std::vector<Version> ordered;
  for (size_t index = 0; index < versions.size(); ++index) {
    const Version &version = versions[index];
    if (version.writer_context_id == reader_context
        && version.version_id != own_latest) {
      continue;
    }
    ordered.push_back(version);
  }

  // ---- happens-before -----------------------------------------------------
  // A write this read is hb-after and that is itself hb-after every other
  // hb-ordered write is the writer this read must have seen: coherence forbids
  // observing a write that a happens-before-later write to the same location
  // overwrote.  Whether any such relation exists at all depends on the
  // synchronization the program performed.
  std::vector<Version> visible;
  bool all_ordered = !ordered.empty();
  for (size_t index = 0; index < ordered.size(); ++index) {
    if (reader_clock.knows(ordered[index].writer_context_id,
                           ordered[index].writer_step)) {
      visible.push_back(ordered[index]);
    } else {
      all_ordered = false;
    }
  }
  jlong sync_dominant = 0;
  if (all_ordered && visible.size() > 1) {
    for (size_t index = 0; index < visible.size(); ++index) {
      bool dominates = true;
      for (size_t other = 0; other < visible.size(); ++other) {
        if (other == index) continue;
        if (!visible[index].writer_clock.knows(
                visible[other].writer_context_id,
                visible[other].writer_step)) {
          dominates = false;
          break;
        }
      }
      if (dominates) {
        sync_dominant = visible[index].version_id;
        break;
      }
    }
  }

  // ---- value evidence -----------------------------------------------------
  // Rules writers out, never in.  A candidate with no comparable fingerprint
  // survives every filter, which is the conservative direction.
  std::vector<Version> candidates;
  bool filtered_any = false;
  for (size_t index = 0; index < ordered.size(); ++index) {
    if (ordered[index].fingerprint.excludes(observed)) {
      filtered_any = true;
      continue;
    }
    candidates.push_back(ordered[index]);
  }

  int reason = REASON_AMBIGUOUS_WRITERS;
  jlong chosen = 0;
  bool untracked = candidates.empty();
  if (sync_dominant != 0 && !untracked) {
    bool dominant_survived = false;
    for (size_t index = 0; index < candidates.size(); ++index) {
      if (candidates[index].version_id == sync_dominant) {
        dominant_survived = true;
      }
    }
    if (dominant_survived) {
      chosen = sync_dominant;
      reason = REASON_SYNC_ORDERED;
    } else {
      // The write that happens-after every other tracked write is not the one
      // this read returned.  Coherence forbids the read from having seen
      // anything the dominant write overwrote, so the value came from a store
      // outside the tracked set -- and every surviving candidate is
      // hb-before the dominant one, so none of them can be it either.
      untracked = true;
      candidates.clear();
    }
  }
  if (untracked) {
    // No tracked writer can have stored the value this read returned.  That is
    // a permanent fact about this location, not a property of this one read.
    reason = REASON_UNTRACKED_WRITER;
    chosen = 0;
  } else if (chosen == 0 && candidates.size() == 1) {
    chosen = candidates[0].version_id;
    reason = filtered_any || ordered.size() > 1
        ? REASON_VALUE_DISTINGUISHED : REASON_UNIQUE_VERSION;
  }

  bool exact = chosen != 0 && complete;
  if (chosen != 0 && !complete) {
    // The candidate would have been exact, but writers have already been lost
    // here, so the disjunction stays open.
    reason = REASON_INCOMPLETE_WRITER_SET;
  }

  plan->candidates = candidates;
  plan->reason = reason;
  plan->writer_set_complete = complete && !untracked;
  if (exact) {
    for (size_t index = 0; index < candidates.size(); ++index) {
      if (candidates[index].version_id == chosen) {
        plan->writer_clock = candidates[index].writer_clock;
      }
    }
    plan->resolution = RESOLVE_EXACT;
    plan->chosen_version_id = chosen;
    // An exact read-from is an observed causal edge and belongs in the one
    // order domain.  A guarded read contributes none, deliberately: an
    // undecided choice has no edge, and drawing one would be the guess this
    // whole mechanism exists to avoid.
    EventLedger::add_observed_edge(chosen, plan->read_event_id,
                                   EventLedger::EDGE_FIELD_READ_FROM);
  } else {
    plan->resolution = RESOLVE_GUARDED;
  }

  ReadRecord record;
  record.read_event_id = plan->read_event_id;
  record.reader_context_id = reader_context;
  record.reader_java_thread_id = ConcolicMngr::ctx->get_owner_java_thread_id();
  record.region_id = ConcolicMngr::ctx->get_region_id();
  record.resolution = plan->resolution;
  record.reason = plan->reason;
  record.chosen_version_id = plan->chosen_version_id;
  record.candidate_count = (int) candidates.size();
  record.observed = observed;

  VERSION_LOCK;
  Slot *slot = find_slot_locked(location);
  if (slot != NULL) {
    if (untracked) slot->writer_set_complete = false;
    slot->reads.push_back(record);
    slot->reads_observed++;
    if (slot->reads.size() > MAX_READS_PER_LOCATION) {
      // The dropped row is a read this location really served and can no
      // longer show.  It does not make the writer set incomplete -- the
      // decision it recorded was already taken against the versions that are
      // still here -- but it does mean the log is a sample.  Say so
      // permanently, and keep the count, so a consumer cannot read the
      // retained rows as the whole read history.
      slot->reads.erase(slot->reads.begin());
      slot->read_log_complete = false;
      slot->reads_dropped++;
    }
  }
  return true;
}

bool SharedFieldVersions::resolve_read(const Location &location,
                                       const Fingerprint &observed,
                                       BasicType type, ReadResult *result) {
  if (result == NULL) return false;
  *result = ReadResult();

  ReadPlan plan;
  if (!plan_read(location, observed, &plan)) return false;

  result->resolution = plan.resolution;
  result->reason = plan.reason;
  result->read_event_id = plan.read_event_id;
  result->chosen_version_id = plan.chosen_version_id;
  result->writer_clock = plan.writer_clock;

  if (plan.resolution == RESOLVE_EXACT) {
    // The writer's own expression, handed over rather than wrapped, so that
    // the reader's arithmetic composes onto it.
    for (size_t index = 0; index < plan.candidates.size(); ++index) {
      if (plan.candidates[index].version_id == plan.chosen_version_id) {
        result->expression = plan.candidates[index].value;
      }
    }
    return true;
  }

  // Guarded.  rf_unknown is appended unconditionally: without it the
  // disjunction would assert that this run observed every writer.
  std::vector<ReadFromExpression::Candidate> arms;
  for (size_t index = 0; index < plan.candidates.size(); ++index) {
    const Version &version = plan.candidates[index];
    ReadFromExpression::Candidate arm;
    char selector[32];
    int length = snprintf(selector, sizeof(selector), "rf%d", (int) index + 1);
    arm.selector = std::string(selector, length < 0 ? 0 : length);
    arm.field_version_id = version.version_id;
    arm.writer_context_id = version.writer_context_id;
    arm.writer_java_thread_id = version.writer_java_thread_id;
    arm.region_id = version.region_id;
    arm.task_id = version.task_id;
    arm.version_kind = version_label(version);
    arm.volatile_write = version.volatile_write;
    // A scalar location's value *is* what a reader of it observes, so the arm
    // is the version's own expression.  A whole-state location is the case
    // where that is not true; see ContainerSupport::query_state.
    arm.value = version.value;
    arm.path_guard = version.path_guard;
    for (size_t other = 0; other < plan.candidates.size(); ++other) {
      if (other == index) continue;
      arm.competing_version_ids.push_back(plan.candidates[other].version_id);
    }
    arms.push_back(arm);
  }
  ReadFromExpression::Candidate unknown;
  unknown.selector = "rf_unknown";
  unknown.unknown = true;
  unknown.value = new UnknownWriterSymbolExp(
      location.owner, location.slot, plan.read_event_id, type);
  arms.push_back(unknown);

  result->expression = new ReadFromExpression(
      arms, std::string(1, type2char(type)), plan.read_event_id,
      location.owner, location.slot, location_kind_name(location.kind),
      read_reason_name(plan.reason), plan.writer_set_complete);
  return true;
}

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
    default:
      return NULL;
  }
}

SharedFieldVersions::Fingerprint SharedFieldVersions::primitive_fingerprint(
    BasicType type, jlong bits) {
  switch (type) {
    case T_BOOLEAN:
      return Fingerprint(FP_PRIMITIVE, bits & 1);
    case T_BYTE:
    case T_CHAR:
    case T_SHORT:
    case T_INT:
    case T_LONG:
    case T_FLOAT:
    case T_DOUBLE:
      return Fingerprint(FP_PRIMITIVE, bits);
    default:
      return Fingerprint();
  }
}

Expression *SharedFieldVersions::reference_expression(oop value) {
  if (value == NULL) return SymbolExpression::get(Sym_NULL);
  if (ConcolicMngr::ctx == NULL) return NULL;
  // Prefers an existing shadow's identity and otherwise names the referent
  // concretely.  It never mints a fresh unconstrained symbol, which is what
  // separates "this reference, observed" from "some reference, unknown".
  return ContainerSupport::concrete_value(value);
}

SharedFieldVersions::Fingerprint SharedFieldVersions::reference_fingerprint(
    oop value) {
  if (value == NULL) return Fingerprint(FP_NULL, 0);
  // A referent with no session identity has no comparable fingerprint.  Never
  // fall back to the oop address: GC moves it, and a stale address compares
  // unequal to the very object it names.
  if (!value->is_symbolic()) return Fingerprint();
  return Fingerprint(FP_IDENTITY, (jlong) value->get_sym_rid());
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
    case VERSION_INITIAL: return "INITIAL";
    case VERSION_WRITE:   return "WRITE";
    case VERSION_RMW:     return "RMW";
    case VERSION_STATE:   return "STATE";
    default:              return "UNKNOWN";
  }
}

std::string SharedFieldVersions::version_label(const Version &version) {
  const std::string kind(version_kind_name(version.version_kind));
  if (version.version_kind != VERSION_STATE || version.operation.empty()) {
    return kind;
  }
  return kind + "_" + version.operation;
}

const char *SharedFieldVersions::fingerprint_kind_name(int kind) {
  switch (kind) {
    case FP_NONE:     return "NONE";
    case FP_PRIMITIVE:return "PRIMITIVE";
    case FP_NULL:     return "NULL";
    case FP_IDENTITY: return "IDENTITY";
    default:          return "UNKNOWN";
  }
}

std::string SharedFieldVersions::describe(const Location &location) {
  using namespace rapidjson;
  VersionList versions;
  std::vector<ReadRecord> reads;
  bool complete = true;
  bool read_log_complete = true;
  jlong versions_observed = 0;
  jlong versions_dropped = 0;
  jlong reads_observed = 0;
  jlong reads_dropped = 0;
  bool selected = false;
  {
    VERSION_LOCK;
    Slot *slot = location.is_valid() && _open
        ? find_slot_locked(location) : NULL;
    if (slot != NULL) {
      selected = true;
      versions = slot->versions;
      reads = slot->reads;
      complete = slot->writer_set_complete;
      read_log_complete = slot->read_log_complete;
      versions_observed = slot->versions_observed;
      versions_dropped = slot->versions_dropped;
      reads_observed = slot->reads_observed;
      reads_dropped = slot->reads_dropped;
    }
  }

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("SHARED_FIELD_VERSIONS");
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
  writer.Bool(complete);
  // How many versions this location really published, and how many the
  // retention bound has since dropped, so a reader can distinguish "well
  // under the bound" from "sitting exactly on it".  `writerSetComplete`
  // already says whether truncation happened at all; these say how close the
  // location is to it.
  writer.Key("versionsObserved");
  writer.Int64(versions_observed);
  writer.Key("versionsDropped");
  writer.Int64(versions_dropped);
  writer.Key("versionRetentionBound");
  writer.Int64((jlong) MAX_VERSIONS_PER_LOCATION);
  writer.Key("versions");
  writer.StartArray();
  size_t serialized_versions = 0;
  bool serialization_truncated = false;
  for (size_t index = 0; index < versions.size(); ++index) {
    if (buffer.GetSize() >= MAX_VERSION_ENVELOPE_BYTES) {
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
    writer.Int64(version.writer_context_id);
    writer.Key("writerJavaThreadId");
    writer.Int64(version.writer_java_thread_id);
    writer.Key("writerStep");
    writer.Int64(version.writer_step);
    writer.Key("regionId");
    writer.String(version.region_id.c_str());
    writer.Key("taskId");
    writer.String(version.task_id.c_str());
    writer.Key("volatileWrite");
    writer.Bool(version.volatile_write);
    writer.Key("fingerprintKind");
    writer.String(fingerprint_kind_name(version.fingerprint.kind));
    writer.Key("fingerprint");
    writer.Int64(version.fingerprint.bits);
    writer.Key("expression");
    if (version.value == NULL) {
      writer.Null();
    } else {
      version.value->serialize(writer);
    }
    writer.Key("pathGuard");
    if (buffer.GetSize() >= MAX_VERSION_ENVELOPE_BYTES) {
      // Keep the current version structurally valid.  The explicit envelope
      // flag below makes this null unusable as an allegedly empty guard.
      writer.Null();
      serialization_truncated = true;
    } else if (version.path_guard == NULL) {
      // The empty conjunction.  Reported explicitly so that "unguarded" is
      // never confused with "the guard was not recorded".
      writer.Null();
    } else {
      version.path_guard->serialize(writer);
    }
    writer.EndObject();
    ++serialized_versions;
    if (serialization_truncated) break;
  }
  writer.EndArray();
  writer.Key("serializationTruncated");
  writer.Bool(serialization_truncated);
  writer.Key("serializedVersionCount");
  writer.Int64((jlong)serialized_versions);
  writer.Key("versionSerializationByteBound");
  writer.Int64((jlong)MAX_VERSION_ENVELOPE_BYTES);

  // Whether the array below is the whole read history or only its tail.
  // Emitted whether or not truncation happened, so "not truncated" is an
  // assertion this store made rather than a member a reader had to assume
  // from an absent key.  Reported in the negative, unlike `writerSetComplete`,
  // because that is the vocabulary the consumer of this envelope already
  // names the finding in.
  writer.Key("readLogTruncated");
  writer.Bool(!read_log_complete);
  writer.Key("readsObserved");
  writer.Int64(reads_observed);
  writer.Key("readsDropped");
  writer.Int64(reads_dropped);
  writer.Key("readRetentionBound");
  writer.Int64((jlong) MAX_READS_PER_LOCATION);

  // Every retained read, with the rule it was decided by.  "Exact" is a claim
  // about evidence, so the evidence travels with it.
  writer.Key("reads");
  writer.StartArray();
  for (size_t index = 0; index < reads.size(); ++index) {
    const ReadRecord &read = reads[index];
    writer.StartObject();
    writer.Key("readEventId");
    writer.Int64(read.read_event_id);
    writer.Key("readerContextId");
    writer.Int64(read.reader_context_id);
    writer.Key("readerJavaThreadId");
    writer.Int64(read.reader_java_thread_id);
    writer.Key("regionId");
    writer.String(read.region_id.c_str());
    writer.Key("resolution");
    writer.String(resolution_name(read.resolution));
    writer.Key("reason");
    writer.String(read_reason_name(read.reason));
    writer.Key("chosenFieldVersionId");
    writer.Int64(read.chosen_version_id);
    writer.Key("candidateCount");
    writer.Int(read.candidate_count);
    writer.Key("selectedEdgeId");
    writer.String(read.selected_edge_id.c_str());
    writer.Key("observedFingerprintKind");
    writer.String(fingerprint_kind_name(read.observed.kind));
    writer.Key("observedFingerprint");
    writer.Int64(read.observed.bits);
    writer.EndObject();
  }
  writer.EndArray();
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

// ---------------------------------------------------------------------------
// The Java-facing selection and evidence API.
//
// It lives here, next to the store, for the same reason the handoff API lives
// in expressionBroker.cpp: everything it has to reason about -- what a
// location is, when it is addressable, what its initial value denotes -- is
// this file's subject, and splitting it across concolicMngr.cpp would leave
// the two halves free to disagree about it.
// ---------------------------------------------------------------------------

namespace {

/**
 * Resolves the location a Java caller named into an addressable slot.
 *
 * A static field is addressed exactly as `getstatic` addresses it: the owner
 * is the *declaring* class's mirror and the slot is the mirror-relative field
 * offset.  Taking the mirror of the class the caller happened to name would
 * split one static location in two whenever a subclass is used to reach an
 * inherited field, and the two halves would never see each other's writes.
 */
bool resolve_field_location(oop owner_oop, const char *declaring_class,
                            const char *field_name, const char *descriptor,
                            SharedFieldVersions::Location *location,
                            fieldDescriptor *field, oop *carrier_owner,
                            jlong *status) {
  *status = SharedFieldVersions::SELECT_FIELD_NOT_FOUND;
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

/** The value a field holds right now, as an expression and a fingerprint. */
void observe_field(oop owner_oop, const fieldDescriptor &field,
                   SymInstance *shadow, Expression **value,
                   SharedFieldVersions::Fingerprint *fingerprint) {
  const int offset = field.offset();
  const BasicType type = field.field_type();
  Expression *existing = shadow == NULL ? NULL : shadow->get(offset);

  if (type == T_OBJECT || type == T_ARRAY) {
    oop referent = owner_oop->obj_field(offset);
    *fingerprint = SharedFieldVersions::reference_fingerprint(referent);
    *value = existing != NULL
        ? existing : SharedFieldVersions::reference_expression(referent);
    // reference_expression never returns NULL for a resolvable oop, but a
    // context-less caller would; fall back to the explicit null symbol rather
    // than publishing a version with no value at all.
    if (*value == NULL) *value = SymbolExpression::get(Sym_NULL);
    return;
  }

  jlong bits = 0;
  switch (type) {
    case T_BOOLEAN: bits = owner_oop->bool_field(offset) ? 1 : 0; break;
    case T_BYTE:    bits = owner_oop->byte_field(offset); break;
    case T_CHAR:    bits = owner_oop->char_field(offset); break;
    case T_SHORT:   bits = owner_oop->short_field(offset); break;
    case T_INT:     bits = owner_oop->int_field(offset); break;
    case T_LONG:    bits = owner_oop->long_field(offset); break;
    case T_FLOAT:   bits = (jlong) jint_cast(owner_oop->float_field(offset));
                    break;
    case T_DOUBLE:  bits = jlong_cast(owner_oop->double_field(offset)); break;
    default:        break;
  }
  *fingerprint = SharedFieldVersions::primitive_fingerprint(type, bits);
  *value = existing != NULL
      ? existing : SharedFieldVersions::primitive_expression(type, bits);
}

/** Reads only the concrete comparison fingerprint; creates no shadow/node. */
SharedFieldVersions::Fingerprint observe_field_fingerprint(
    oop owner_oop, const fieldDescriptor &field) {
  const int offset = field.offset();
  const BasicType type = field.field_type();
  if (type == T_OBJECT || type == T_ARRAY) {
    return SharedFieldVersions::reference_fingerprint(
        owner_oop->obj_field(offset));
  }

  jlong bits = 0;
  switch (type) {
    case T_BOOLEAN: bits = owner_oop->bool_field(offset) ? 1 : 0; break;
    case T_BYTE:    bits = owner_oop->byte_field(offset); break;
    case T_CHAR:    bits = owner_oop->char_field(offset); break;
    case T_SHORT:   bits = owner_oop->short_field(offset); break;
    case T_INT:     bits = owner_oop->int_field(offset); break;
    case T_LONG:    bits = owner_oop->long_field(offset); break;
    case T_FLOAT:   bits = (jlong) jint_cast(owner_oop->float_field(offset));
                    break;
    case T_DOUBLE:  bits = jlong_cast(owner_oop->double_field(offset)); break;
    default:        return SharedFieldVersions::Fingerprint();
  }
  return SharedFieldVersions::primitive_fingerprint(type, bits);
}

/** The value an array element holds right now. */
bool observe_element(arrayOop array, int index, Expression **value,
                     SharedFieldVersions::Fingerprint *fingerprint) {
  if (array == NULL || index < 0 || index >= array->length()) return false;
  BasicType type = ArrayKlass::cast(array->klass())->element_type();
  if (type == T_OBJECT || type == T_ARRAY) {
    oop element = objArrayOop(array)->obj_at(index);
    *fingerprint = SharedFieldVersions::reference_fingerprint(element);
    *value = SharedFieldVersions::reference_expression(element);
    if (*value == NULL) *value = SymbolExpression::get(Sym_NULL);
    return true;
  }

  jlong bits = 0;
  switch (type) {
    case T_BOOLEAN: bits = typeArrayOop(array)->bool_at(index) ? 1 : 0; break;
    case T_BYTE:    bits = typeArrayOop(array)->byte_at(index); break;
    case T_CHAR:    bits = typeArrayOop(array)->char_at(index); break;
    case T_SHORT:   bits = typeArrayOop(array)->short_at(index); break;
    case T_INT:     bits = typeArrayOop(array)->int_at(index); break;
    case T_LONG:    bits = typeArrayOop(array)->long_at(index); break;
    case T_FLOAT:
      bits = (jlong) jint_cast(typeArrayOop(array)->float_at(index));
      break;
    case T_DOUBLE:
      bits = jlong_cast(typeArrayOop(array)->double_at(index));
      break;
    default:
      return false;
  }
  *fingerprint = SharedFieldVersions::primitive_fingerprint(type, bits);
  *value = SharedFieldVersions::primitive_expression(type, bits);
  return *value != NULL;
}

} // anonymous namespace

jlong ConcolicMngr::selectSharedFieldCarrier(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (owner.is_null()
      || declaring_class == NULL || declaring_class[0] == '\0'
      || field_name == NULL || field_name[0] == '\0'
      || descriptor == NULL || descriptor[0] == '\0') {
    return SharedFieldVersions::SELECT_MISSING_METADATA;
  }

  ResourceMark rm;
  fieldDescriptor field;
  SharedFieldVersions::Location location;
  oop carrier_owner = NULL;
  jlong status = 0;
  if (!resolve_field_location(owner(), declaring_class, field_name, descriptor,
                              &location, &field, &carrier_owner, &status)) {
    return status;
  }

  // The owner shadow must exist before the location is selected: the
  // interpreter hooks recognise a carrier by its owner's sym_rid, and an owner
  // with no shadow can never match one.
  SymInstance *shadow = ctx->get_or_alloc_sym_inst(carrier_owner);
  if (shadow == NULL) return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  location.owner = shadow->get_sym_rid();

  Expression *initial = NULL;
  SharedFieldVersions::Fingerprint fingerprint;
  observe_field(carrier_owner, field, shadow, &initial, &fingerprint);
  if (initial == NULL) return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;

  jlong version_id =
      SharedFieldVersions::select_carrier(
          location, initial, fingerprint, descriptor);
  if (version_id == 0) return SharedFieldVersions::SELECT_ALREADY_SELECTED;
  // A selected carrier is a materialized symbolic input in the same sense as
  // an explicit symbolize: from here on this thread's branches are relevant.
  ctx->set_pc_admitted(true);
  return version_id;
}

jlong ConcolicMngr::getCurrentSharedFieldVersion(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (owner.is_null()
      || declaring_class == NULL || declaring_class[0] == '\0'
      || field_name == NULL || field_name[0] == '\0'
      || descriptor == NULL || descriptor[0] == '\0') {
    return SharedFieldVersions::SELECT_MISSING_METADATA;
  }

  ResourceMark rm;
  fieldDescriptor field;
  SharedFieldVersions::Location location;
  oop carrier_owner = NULL;
  jlong status = 0;
  if (!resolve_field_location(owner(), declaring_class, field_name, descriptor,
                              &location, &field, &carrier_owner, &status)) {
    return status;
  }

  // Pure means pure with respect to symbolic state: neither the owner nor a
  // non-null referent is assigned a symbolic identity by this lookup.
  SymInstance *shadow = ctx->find_sym_inst(carrier_owner);
  if (shadow == NULL) return SharedFieldVersions::SELECT_VERSION_NOT_FOUND;
  location.owner = shadow->get_sym_rid();
  return SharedFieldVersions::current_field_version(
      location, shadow->get(field.offset()),
      observe_field_fingerprint(carrier_owner, field), ctx->get_task_id(),
      descriptor);
}

jlong ConcolicMngr::admitSharedFieldVersion(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor, jlong version_id,
    const char *selected_edge_id) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (owner.is_null() || version_id <= 0
      || declaring_class == NULL || declaring_class[0] == '\0'
      || field_name == NULL || field_name[0] == '\0'
      || descriptor == NULL || descriptor[0] == '\0') {
    return SharedFieldVersions::SELECT_MISSING_METADATA;
  }
  if (selected_edge_id == NULL || selected_edge_id[0] == '\0') {
    return SharedFieldVersions::SELECT_INVALID_EDGE;
  }

  ResourceMark rm;
  fieldDescriptor field;
  SharedFieldVersions::Location destination;
  oop carrier_owner = NULL;
  jlong status = 0;
  if (!resolve_field_location(owner(), declaring_class, field_name, descriptor,
                              &destination, &field, &carrier_owner, &status)) {
    return status;
  }

  // Prove every producer-side and concrete replay condition before allocating
  // the destination owner shadow.  A stale id, wrong descriptor, primitive
  // mismatch or nullness mismatch therefore has zero symbolic side effects.
  SharedFieldVersions::Location source;
  SharedFieldVersions::Version producer;
  jlong lookup = SharedFieldVersions::lookup_field_version(
      version_id, descriptor, &source, &producer);
  if (lookup <= 0) return lookup;
  SharedFieldVersions::Fingerprint observed =
      observe_field_fingerprint(carrier_owner, field);
  if (!planned_value_matches(descriptor, producer.fingerprint, observed)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  SymInstance *shadow = ctx->find_sym_inst(carrier_owner);
  if (shadow != NULL && shadow->get(field.offset()) != NULL
      && shadow->get(field.offset()) != producer.value) {
    // A separately configured consumer symbol is the discovery authority for
    // this field.  Exact concrete provenance must not overwrite it.  An
    // already-installed producer expression on the very same session field
    // is not a consumer symbol and is admitted without rewriting the slot.
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }
  if (shadow == NULL) shadow = ctx->get_or_alloc_sym_inst(carrier_owner);
  if (shadow == NULL) return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  destination.owner = shadow->get_sym_rid();

  jlong planned = SharedFieldVersions::plan_exact_field_read(
      destination, version_id, descriptor, selected_edge_id);
  if (planned <= 0) return planned;
  ctx->set_pc_admitted(true);
  return planned;
}

jlong ConcolicMngr::selectSharedElementCarrier(Handle array, jint index) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (array.is_null() || !array()->is_array() || index < 0) {
    return SharedFieldVersions::SELECT_MISSING_METADATA;
  }
  arrayOop target = arrayOop(array());
  if (index >= target->length()) {
    return SharedFieldVersions::SELECT_MISSING_METADATA;
  }

  SymArr *shadow = ctx->get_or_alloc_sym_array(target);
  if (shadow == NULL) return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;

  Expression *initial = NULL;
  SharedFieldVersions::Fingerprint fingerprint;
  if (!observe_element(target, index, &initial, &fingerprint)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  SharedFieldVersions::Location location(
      shadow->get_sym_rid(), index, SharedFieldVersions::LOC_ARRAY_ELEMENT);
  jlong version_id =
      SharedFieldVersions::select_carrier(location, initial, fingerprint);
  if (version_id == 0) return SharedFieldVersions::SELECT_ALREADY_SELECTED;
  ctx->set_pc_admitted(true);
  return version_id;
}

jlong ConcolicMngr::selectSharedMapCarrier(Handle map) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (map.is_null()) return SharedFieldVersions::SELECT_MISSING_METADATA;
  oop target = map();
  if (!ContainerSupport::associative(target)) {
    // Only the associative shape has the whole-state algebra this location
    // kind resolves over.  Anything else is refused by name rather than
    // selected and silently never versioned.
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  // Forcing the state root is what makes the map addressable at all: it mints
  // the container shadow the location's owner id is taken from, and it is also
  // the INITIAL version's value, so "the state this map started in" is an
  // ordinary candidate rather than a hole.  Built here, outside every version
  // lock, exactly as the scalar path builds its initial expression.
  Expression *root = ctx->container_state(target, "ASSOCIATIVE");
  if (root == NULL) return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;

  SharedFieldVersions::Location location =
      ContainerSupport::state_location(target);
  if (!location.is_valid()) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }
  // FP_NONE.  A whole map has no comparable concrete fingerprint, and a
  // candidate that cannot be compared survives every value filter -- the
  // conservative direction, and exactly what keeps two writers that installed
  // equal maps two distinct candidates.
  jlong version_id = SharedFieldVersions::select_carrier(
      location, root, SharedFieldVersions::Fingerprint());
  if (version_id == 0) return SharedFieldVersions::SELECT_ALREADY_SELECTED;
  ctx->set_pc_admitted(true);
  return version_id;
}

jlong ConcolicMngr::getCurrentSharedMapVersion(Handle map) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (map.is_null()) return SharedFieldVersions::SELECT_MISSING_METADATA;
  oop target = map();
  if (!ContainerSupport::associative(target)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  // Both lookups are pure: asking for the current version must not be the
  // operation that gives an untracked map a shadow, state root or INITIAL.
  Expression *current = ctx->find_container_state(target);
  SharedFieldVersions::Location location =
      ContainerSupport::state_location(target);
  return SharedFieldVersions::current_state_version(
      location, current, ctx->get_task_id());
}

jlong ConcolicMngr::admitSharedMapVersion(
    Handle map, jlong version_id, const char *selected_edge_id) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (map.is_null() || version_id <= 0) {
    return SharedFieldVersions::SELECT_MISSING_METADATA;
  }
  if (selected_edge_id == NULL || selected_edge_id[0] == '\0') {
    return SharedFieldVersions::SELECT_INVALID_EDGE;
  }
  oop target = map();
  if (!ContainerSupport::associative(target)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  // Resolve every fallible producer-side condition before touching the
  // destination heap.  In particular, a stale id or wrong edge cannot mint a
  // destination shadow or the local INITIAL that ordinary carrier selection
  // creates.
  SharedFieldVersions::Location source;
  Expression *state = NULL;
  jlong lookup = SharedFieldVersions::lookup_state_version(
      version_id, &source, &state);
  if (lookup <= 0) return lookup;

  // The destination owns a local current-state slot, while its evidence id
  // aliases the producer's MAP_STATE location.  Only native session ids and
  // the arena-owned Expression pointer are shared; no source oop reaches Java.
  if (!ctx->admit_container_state(target, source.owner, state)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }
  jlong read_event_id = SharedFieldVersions::record_planned_state_read(
      source, version_id, selected_edge_id);
  if (read_event_id <= 0) return read_event_id;
  ctx->set_pc_admitted(true);
  return read_event_id;
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
    jlong status = 0;
    if (resolve_field_location(owner(), declaring_class, field_name,
                               descriptor, &location, &field, &carrier_owner,
                               &status)) {
      // Look the owner up rather than allocating one: asking what a location
      // recorded must not be the thing that gives it an identity.
      SymInstance *shadow = ctx->find_sym_inst(carrier_owner);
      location.owner = shadow == NULL ? NULL_SYM_RID : shadow->get_sym_rid();
      location = SharedFieldVersions::evidence_location(location);
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
