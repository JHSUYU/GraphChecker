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
#include "oops/instanceKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "runtime/fieldDescriptor.hpp"
#include "utilities/ostream.hpp"
#include "webridge/utils/rapidjson/stringbuffer.h"
#include "webridge/utils/rapidjson/writer.h"

bool SharedFieldVersions::_open = false;
SharedFieldVersions::SlotStore SharedFieldVersions::_slots;
SharedFieldVersions::PendingReadStore
    SharedFieldVersions::_pending_primitive_reads;
SharedFieldVersions::ArmedTokenIndex SharedFieldVersions::_armed_read_tokens;
SharedFieldVersions::ConsumedReadStore
    SharedFieldVersions::_consumed_primitive_reads;
// What one initial-snapshot offer answered, per canonical container id.
// Guarded by _mutex and cleared with the session, like every other record
// here: an offer's answer is a fact about one session's container.
struct InitialSnapshotNote {
  int answer;
  int entries;
  InitialSnapshotNote() : answer(0), entries(-1) {}
  InitialSnapshotNote(int offer_answer, int member_count)
      : answer(offer_answer), entries(member_count) {}
};
static std::map<sym_rid_t, InitialSnapshotNote> _initial_snapshot_notes;
volatile int SharedFieldVersions::_carrier_count = 0;
pthread_mutex_t SharedFieldVersions::_mutex = PTHREAD_MUTEX_INITIALIZER;

namespace {

// One location can retain many versions, each with a value and a path guard.
// Expression::serialize bounds each root independently; this envelope bound
// prevents those individually bounded roots from accumulating into one
// unbounded native StringBuffer.
static const size_t MAX_VERSION_ENVELOPE_BYTES = 32u * 1024u * 1024u;

/**
 * What this envelope actually costs so far.
 *
 * Inside an artifact scope a serialized root leaves a short reference in the
 * buffer and puts its whole DAG in the expression table, so the buffer size
 * alone is not the envelope size -- it is the small part of it.  Every budget
 * question below asks this instead.
 *
 * The budget is a stopping rule rather than a hard ceiling: a root already
 * serialized keeps its definitions, because dropping them would leave a
 * dangling reference in `versions`.  Overshoot is therefore bounded by the
 * last root admitted, and the envelope says it truncated.
 */
size_t envelope_bytes(const rapidjson::StringBuffer &buffer,
                      VmExpressionArtifactScope &artifact) {
  return buffer.GetSize() + artifact.pending_table_size();
}

class VersionLock {
public:
  VersionLock(pthread_mutex_t *mutex) : _mutex(mutex) {
    pthread_mutex_lock(_mutex);
  }
  ~VersionLock() { pthread_mutex_unlock(_mutex); }
private:
  pthread_mutex_t *_mutex;
};

} // anonymous namespace

#define VERSION_LOCK VersionLock version_guard(&_mutex)

void SharedFieldVersions::open_session() {
  VERSION_LOCK;
  guarantee(_slots.empty(), "versions outlived the previous session");
  guarantee(_pending_primitive_reads.empty(),
            "pending replay reads outlived the previous session");
  guarantee(_armed_read_tokens.empty(),
            "replay read receipts outlived the previous session");
  guarantee(_consumed_primitive_reads.empty(),
            "replay read receipts outlived the previous session");
  _initial_snapshot_notes.clear();
  _carrier_count = 0;
  _open = true;
}

void SharedFieldVersions::close_session() {
  VERSION_LOCK;
  // Every Expression named here belongs to the session arena and is freed with
  // it.  Dropping the records is exactly a decision to stop naming them.
  _slots.clear();
  _pending_primitive_reads.clear();
  _armed_read_tokens.clear();
  _consumed_primitive_reads.clear();
  _initial_snapshot_notes.clear();
  _carrier_count = 0;
  _open = false;
}

SharedFieldVersions::Slot *SharedFieldVersions::find_slot_locked(
    const Location &location) {
  SlotStore::iterator found = _slots.find(location);
  return found == _slots.end() ? NULL : &found->second;
}

bool SharedFieldVersions::is_tracked(const Location &location) {
  if (!location.is_valid()) return false;
  VERSION_LOCK;
  return _open && _slots.find(location) != _slots.end();
}

jlong SharedFieldVersions::select_carrier(const Location &location,
                                          Expression *initial) {
  return select_carrier(location, initial, InitialSnapshot());
}

void SharedFieldVersions::note_initial_snapshot(sym_rid_t owner, int answer,
                                                int entries) {
  if (owner == NULL_SYM_RID) return;
  VERSION_LOCK;
  _initial_snapshot_notes[owner] = InitialSnapshotNote(answer, entries);
}

bool SharedFieldVersions::initial_snapshot_note(sym_rid_t owner, int *answer,
                                                int *entries) {
  if (owner == NULL_SYM_RID) return false;
  VERSION_LOCK;
  std::map<sym_rid_t, InitialSnapshotNote>::const_iterator found =
      _initial_snapshot_notes.find(owner);
  if (found == _initial_snapshot_notes.end()) return false;
  if (answer != NULL) *answer = found->second.answer;
  if (entries != NULL) *entries = found->second.entries;
  return true;
}

jlong SharedFieldVersions::select_carrier(const Location &location,
                                          Expression *initial,
                                          const InitialSnapshot &snapshot) {
  if (!location.is_valid()) return 0;

  // A version id correlates this expression with a candidate arm.  Its
  // numeric order is never used to choose what a read observed.
  jlong version_id = GlobalSymbolicSession::next_event_id();
  Version version;
  version.version_id = version_id;
  version.version_kind = VERSION_INITIAL;
  version.value = initial;
  version.path_guard = NULL;
  // Stated, refused, or never offered -- and a stated *empty* container is
  // the case a member count alone cannot express.  Deriving this from
  // `entries > 0` published no snapshot block for the container that held
  // nothing, so its exact empty base read back as "contents unknown": the
  // one carrier whose initial state is pinned hardest was the one left free.
  version.initial_snapshot_present = snapshot.present();
  version.initial_snapshot_entries = snapshot.entries;
  version.initial_snapshot_truncated = snapshot.truncated;
  if (ConcolicMngr::ctx != NULL) {
    version.writer_context_id = ConcolicMngr::ctx->get_context_id();
    version.region_id = ConcolicMngr::ctx->get_region_id();
    version.task_id = ConcolicMngr::ctx->get_task_id();
    version.region_enter_event_id =
        ConcolicMngr::ctx->region_enter_event();
  }

  VERSION_LOCK;
  if (!_open) return 0;
  if (_slots.find(location) != _slots.end()) return 0;
  Slot &slot = _slots[location];
  slot.writer_set_complete = true;
  slot.versions.push_back(version);
  _carrier_count = (int) _slots.size();
  return version_id;
}

jlong SharedFieldVersions::publish_initial(const Location &location,
                                           Expression *base,
                                           const InitialSnapshot &snapshot) {
  if (!location.is_valid() || base == NULL) return 0;
  if (is_tracked(location)) return 0;
  // The base a later mutation extends.  Published as its own version so the
  // log begins where the container did, which is what a relation chain stands
  // on: without it the first PUT has no receiver a reader can resolve.
  return publish(location, base, NULL, VERSION_INITIAL, NULL, true, &snapshot);
}

bool SharedFieldVersions::adopt_initial_snapshot(
    const Location &location, const InitialSnapshot &snapshot) {
  if (!location.is_valid() || !snapshot.present()) return false;
  VERSION_LOCK;
  if (!_open) return false;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL || slot->versions.empty()) return false;
  Version &first = slot->versions.front();
  // Only an INITIAL base can carry a pre-tracking snapshot, and only once:
  // the offer that arrives first is the authority, exactly as it was when
  // selection created the version itself.
  if (first.version_kind != VERSION_INITIAL) return false;
  if (first.initial_snapshot_present) return false;
  first.initial_snapshot_present = true;
  first.initial_snapshot_entries = snapshot.entries;
  first.initial_snapshot_truncated = snapshot.truncated;
  return true;
}

jlong SharedFieldVersions::publish_value(const Location &location,
                                         Expression *value,
                                         Expression *path_guard,
                                         bool symbolic, int version_kind,
                                         const char *operation) {
  if (!location.is_valid() || value == NULL) return 0;
  // A location no symbolic value has ever reached has nothing a reader could
  // want back, and costs one lock-free counter read to dismiss: the store
  // leaves it alone and it stays concrete.  Once one symbolic value has
  // landed, every later store -- concrete ones included -- must be versioned,
  // or a read would go on resolving to an expression the program has since
  // overwritten.
  if (!symbolic && (!has_carriers() || !is_tracked(location))) return 0;
  return publish(location, value, path_guard, version_kind, operation,
                 symbolic);
}

jlong SharedFieldVersions::publish(const Location &location, Expression *value,
                                   Expression *path_guard,
                                   int version_kind,
                                   const char *operation,
                                   bool start_tracking,
                                   const InitialSnapshot *snapshot) {
  if (!location.is_valid() || value == NULL) return 0;

  const bool named = operation != NULL && operation[0] != '\0';
  jlong version_id = GlobalSymbolicSession::next_event_id();
  Version version;
  version.version_id = version_id;
  version.version_kind = version_kind;
  if (named) version.operation = operation;
  version.value = value;
  version.path_guard = path_guard;
  if (snapshot != NULL) {
    version.initial_snapshot_present = snapshot->present();
    version.initial_snapshot_entries = snapshot->entries;
    version.initial_snapshot_truncated = snapshot->truncated;
    version.initial_snapshot_unsupported_class = snapshot->unsupported_class;
  }
  if (ConcolicMngr::ctx != NULL) {
    version.writer_context_id = ConcolicMngr::ctx->get_context_id();
    version.region_id = ConcolicMngr::ctx->get_region_id();
    version.task_id = ConcolicMngr::ctx->get_task_id();
    version.region_enter_event_id =
        ConcolicMngr::ctx->region_enter_event();
  }

  VERSION_LOCK;
  if (!_open) return 0;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL) {
    // The first symbolic value to reach this location starts its log.  A
    // fresh Slot is complete by construction: nothing was written here before
    // that a reader could be missing, because nothing symbolic was.
    if (!start_tracking) return 0;
    slot = &_slots[location];
    _carrier_count = (int) _slots.size();
  }
  slot->versions.push_back(version);
  if (slot->versions.size() > MAX_VERSIONS_PER_LOCATION) {
    // A dropped writer is a writer a later read can no longer name.  Say so
    // permanently rather than answering as if the set were still whole.
    slot->versions.erase(slot->versions.begin());
    slot->writer_set_complete = false;
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

bool SharedFieldVersions::plan_read(const Location &location,
                                    ReadPlan *plan) {
  if (plan == NULL) return false;
  *plan = ReadPlan();
  if (!location.is_valid() || ConcolicMngr::ctx == NULL) return false;

  VersionList versions;
  bool complete = true;
  if (!versions_of(location, &versions, &complete) || versions.empty()) {
    return false;
  }

  plan->read_event_id = GlobalSymbolicSession::next_event_id();
  // Versions are appended in publish order and their ids come from the one
  // session counter, so the last one is the newest and is what the location
  // held when this read ran.
  plan->observed = versions.back();
  plan->writer_set_complete = complete;

  ReadRecord record;
  record.read_event_id = plan->read_event_id;
  record.reader_context_id = ConcolicMngr::ctx->get_context_id();
  record.region_id = ConcolicMngr::ctx->get_region_id();
  record.task_id = ConcolicMngr::ctx->get_task_id();
  record.region_enter_event_id = ConcolicMngr::ctx->region_enter_event();

  VERSION_LOCK;
  Slot *slot = find_slot_locked(location);
  if (slot != NULL) {
    slot->reads.push_back(record);
    if (slot->reads.size() > MAX_READS_PER_LOCATION) {
      slot->reads.erase(slot->reads.begin());
      slot->read_log_complete = false;
    }
  }
  return true;
}

jlong SharedFieldVersions::live_version(const Location &location,
                                        std::string *version_kind) {
  if (version_kind != NULL) version_kind->clear();
  if (!location.is_valid()) return 0;
  VERSION_LOCK;
  if (!_open) return 0;
  Slot *slot = find_slot_locked(location);
  if (slot == NULL || slot->versions.empty()) return 0;
  const Version &version = slot->versions.back();
  if (version_kind != NULL) *version_kind = version_label(version);
  return version.version_id;
}

Expression *SharedFieldVersions::build_read_from(
    const ReadPlan &plan, const Location &location,
    const std::string &type_name, Expression *observed_value) {
  guarantee(observed_value != NULL,
            "a read-from needs the value of the version it observed");
  Expression *selection = new ReadFromExpression(
      plan.observed.version_id, version_label(plan.observed), observed_value,
      type_name, plan.read_event_id, location.owner, location.slot,
      location_kind_name(location.kind), plan.writer_set_complete);
  return new ConsumerBoundaryExpression(
      selection, type_name, ConsumerBoundaryExpression::FIELD_READ,
      plan.read_event_id);
}

bool SharedFieldVersions::resolve_read(const Location &location,
                                       BasicType type, ReadResult *result) {
  if (result == NULL) return false;
  *result = ReadResult();

  ReadPlan plan;
  if (!plan_read(location, &plan)) return false;
  // For a scalar location the observed value is the observed write's own.
  result->expression = build_read_from(
      plan, location, std::string(1, type2char(type)), plan.observed.value);
  return true;
}

jlong SharedFieldVersions::arm_primitive_read(
    jlong context_id, jlong region_enter_event_id, const Location &location,
    BasicType type, jlong value_bits) {
  if (context_id <= 0 || !location.is_valid()) {
    return REPLAY_READ_NO_CONTEXT;
  }
  if (location.kind != LOC_INSTANCE_FIELD
      || !(type == T_BOOLEAN || type == T_BYTE || type == T_CHAR
           || type == T_SHORT || type == T_INT || type == T_LONG)) {
    return REPLAY_READ_UNSUPPORTED;
  }
  // Receipt identity comes from the session's stable monotonic namespace.
  // Allocate it before the versions leaf lock.
  const jlong token = GlobalSymbolicSession::next_event_id();
  PendingReadKey key(context_id, location);
  VERSION_LOCK;
  if (!_open || _slots.find(location) == _slots.end()) {
    return REPLAY_READ_NOT_SELECTED;
  }
  if (_pending_primitive_reads.find(key)
      != _pending_primitive_reads.end()) {
    return REPLAY_READ_ALREADY_PENDING;
  }
  PendingPrimitiveRead read;
  read.token = token;
  read.region_enter_event_id = region_enter_event_id;
  read.type = type;
  read.value_bits = value_bits;
  _pending_primitive_reads[key] = read;
  _armed_read_tokens[token] = key;
  return token;
}

bool SharedFieldVersions::consume_primitive_read(
    jlong context_id, const Location &location, BasicType type,
    jlong *value_bits) {
  if (value_bits == NULL || context_id <= 0 || !location.is_valid()) {
    return false;
  }
  PendingReadKey key(context_id, location);
  VERSION_LOCK;
  PendingReadStore::iterator found = _pending_primitive_reads.find(key);
  if (!_open || found == _pending_primitive_reads.end()
      || found->second.type != type) {
    return false;
  }
  *value_bits = found->second.value_bits;
  _consumed_primitive_reads[found->second.token] = context_id;
  _armed_read_tokens.erase(found->second.token);
  _pending_primitive_reads.erase(found);
  return true;
}

jlong SharedFieldVersions::confirm_primitive_read(jlong context_id,
                                                   jlong token) {
  if (context_id <= 0) return REPLAY_READ_NO_CONTEXT;
  if (token <= 0) return REPLAY_READ_UNKNOWN_TOKEN;
  VERSION_LOCK;
  ConsumedReadStore::iterator consumed =
      _consumed_primitive_reads.find(token);
  if (consumed != _consumed_primitive_reads.end()) {
    if (consumed->second != context_id) return REPLAY_READ_WRONG_CONTEXT;
    _consumed_primitive_reads.erase(consumed);
    return 1;
  }
  ArmedTokenIndex::iterator armed = _armed_read_tokens.find(token);
  if (armed == _armed_read_tokens.end()) return REPLAY_READ_UNKNOWN_TOKEN;
  if (armed->second.context_id != context_id) {
    return REPLAY_READ_WRONG_CONTEXT;
  }
  // Confirmation is the lifetime boundary for this one-shot request.  A
  // read that never consumed it must not affect a later access.
  _pending_primitive_reads.erase(armed->second);
  _armed_read_tokens.erase(armed);
  return REPLAY_READ_PENDING;
}

void SharedFieldVersions::discard_armed_reads(jlong context_id,
                                              jlong region_enter_event_id) {
  if (context_id <= 0) return;
  VERSION_LOCK;
  PendingReadStore::iterator pending = _pending_primitive_reads.begin();
  while (pending != _pending_primitive_reads.end()) {
    // Regions nest on one context: an inner region's close abandons what the
    // inner region armed and leaves the enclosing region's arms pending.
    // Zero is the context-wide purge that context teardown needs.
    if (pending->first.context_id != context_id
        || (region_enter_event_id > 0
            && pending->second.region_enter_event_id
               != region_enter_event_id)) {
      ++pending;
      continue;
    }
    _armed_read_tokens.erase(pending->second.token);
    PendingReadStore::iterator abandoned = pending++;
    _pending_primitive_reads.erase(abandoned);
  }
}

void SharedFieldVersions::forget_context(jlong context_id) {
  if (context_id <= 0) return;
  // The context itself is going away, so every region of it is over.
  discard_armed_reads(context_id, 0);
  VERSION_LOCK;
  ConsumedReadStore::iterator consumed = _consumed_primitive_reads.begin();
  while (consumed != _consumed_primitive_reads.end()) {
    if (consumed->second != context_id) {
      ++consumed;
      continue;
    }
    ConsumedReadStore::iterator retired = consumed++;
    _consumed_primitive_reads.erase(retired);
  }
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

Expression *SharedFieldVersions::reference_expression(oop value) {
  if (value == NULL) return SymbolExpression::get(Sym_NULL);
  if (ConcolicMngr::ctx == NULL) return NULL;
  // Prefers an existing shadow's identity and otherwise names the referent
  // concretely.  It never mints a fresh unconstrained symbol, which is what
  // separates "this reference, observed" from "some reference, unknown".
  return ContainerSupport::concrete_value(value);
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

// One `SHARED_FIELD_VERSIONS` envelope, written into a caller's document.
//
// Split out of describe() so the single-location answer and the whole
// read-out emit byte-identical envelopes: there is one writer, and neither
// caller can drift from the other.  The caller owns the artifact scope and
// writes the expression table once for the whole document, so a subgraph two
// locations share is defined once rather than per location.
//
// `budget_bytes` bounds this envelope alone (0 = the default per-envelope
// bound); `document_bytes` is what the caller has already committed, so the
// bound is checked against the real document rather than this envelope in
// isolation.  Returns true when the envelope was cut short.
bool SharedFieldVersions::write_versions_envelope(
    rapidjson::Writer<rapidjson::StringBuffer> &writer,
    const rapidjson::StringBuffer &buffer,
    VmExpressionArtifactScope &expression_artifact,
    const Location &location, const VersionList &versions,
    const std::vector<ReadRecord> &reads, bool selected, bool complete,
    bool read_log_complete, size_t budget_bytes) {
  using namespace rapidjson;
  const size_t bound = budget_bytes == 0
      ? MAX_VERSION_ENVELOPE_BYTES : budget_bytes;
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("SHARED_FIELD_VERSIONS");
  // The symbolic universe these ids belong to.  An id is only comparable
  // against another id minted by the same session, so every envelope that
  // carries ids names the session that minted them.
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
  writer.Bool(complete);
  writer.Key("versions");
  writer.StartArray();
  bool serialization_truncated = false;
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
    writer.Int64(version.writer_context_id);
    writer.Key("regionId");
    writer.String(version.region_id.c_str());
    writer.Key("taskId");
    writer.String(version.task_id.c_str());
    writer.Key("regionEnterEventId");
    writer.Int64(version.region_enter_event_id);
    // Emitted whenever this engine has something to say about the contents
    // that predate tracking -- a stated count, a refusal over the bound, or a
    // class it cannot read.  `stated` is explicit so an absent count is never
    // mistaken for an empty container.
    if (version.initial_snapshot_present
        || !version.initial_snapshot_unsupported_class.empty()) {
      writer.Key("initialSnapshot");
      writer.StartObject();
      writer.Key("stated");
      writer.Bool(version.initial_snapshot_present
                  && !version.initial_snapshot_truncated);
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
    if (serialization_truncated) break;
  }
  writer.EndArray();
  writer.Key("readLogTruncated");
  writer.Bool(!read_log_complete);
  writer.Key("reads");
  writer.StartArray();
  for (size_t index = 0; index < reads.size(); ++index) {
    // The read log is bounded by the same budget as the versions.  It used to
    // be unbounded: a location with a full read log appended its rows after
    // the versions loop had already decided the envelope was full.
    if (envelope_bytes(buffer, expression_artifact) >= bound) {
      serialization_truncated = true;
      break;
    }
    const ReadRecord &read = reads[index];
    writer.StartObject();
    writer.Key("readEventId");
    writer.Int64(read.read_event_id);
    writer.Key("readerContextId");
    writer.Int64(read.reader_context_id);
    writer.Key("regionId");
    writer.String(read.region_id.c_str());
    writer.Key("taskId");
    writer.String(read.task_id.c_str());
    writer.Key("regionEnterEventId");
    writer.Int64(read.region_enter_event_id);
    writer.EndObject();
  }
  writer.EndArray();
  // Written after both arrays because it now reports either of them being
  // cut short, and after the artifact table has been accounted for.  This is
  // the flag Java triages as EXPRESSION_SERIALIZATION_TRUNCATED; member order
  // in a JSON object carries no meaning to its reader.
  writer.Key("serializationTruncated");
  writer.Bool(serialization_truncated);
  // Deliberately NOT closed here.  The caller writes its expression table
  // into this object (single-location answer) or closes it and writes one
  // table for the whole document (the read-out), and those are the only two
  // shapes.  Leaving the brace to the caller is what lets both exist without
  // the single-location envelope changing by a byte.
  return serialization_truncated;
}

namespace {

// The clock value a location is ordered and selected by: the lowest event id
// it carries, over both its versions and its reads.  A location written
// before an activation and only read during it is selected by its read, which
// is why reads count here as well as writes.
jlong location_low_event(const SharedFieldVersions::Slot &slot) {
  jlong low = 0;
  for (size_t i = 0; i < slot.versions.size(); ++i) {
    const jlong id = slot.versions[i].version_id;
    if (id > 0 && (low == 0 || id < low)) low = id;
  }
  for (size_t i = 0; i < slot.reads.size(); ++i) {
    const jlong id = slot.reads[i].read_event_id;
    if (id > 0 && (low == 0 || id < low)) low = id;
  }
  return low;
}

// The highest event id a location carries; the resume point when a read-out
// stops before it.
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
  jlong low;
  TrackedLocation() : low(0) {}
};

bool by_low_event(const TrackedLocation &a, const TrackedLocation &b) {
  if (a.low != b.low) return a.low < b.low;
  // A total order even when two locations share a lowest id, so a resume is
  // well defined rather than dependent on map iteration order.
  if (a.location.owner != b.location.owner) {
    return a.location.owner < b.location.owner;
  }
  if (a.location.slot != b.location.slot) {
    return a.location.slot < b.location.slot;
  }
  return a.location.kind < b.location.kind;
}

} // anonymous namespace

std::string SharedFieldVersions::tracked_locations(jlong after_event_id,
                                                   jint max_bytes) {
  using namespace rapidjson;
  // Snapshot under the lock, serialize outside it: an Expression may not be
  // rendered while the version lock is held, and the engine lock order
  // (membership -> versions -> arena) forbids taking the arena beneath it.
  std::vector<TrackedLocation> selected;
  bool open = false;
  {
    VERSION_LOCK;
    open = _open;
    if (open) {
      for (SlotStore::const_iterator it = _slots.begin();
           it != _slots.end(); ++it) {
        const jlong high = location_high_event(it->second);
        // Selected when anything it carries is at or after the watermark.
        if (after_event_id > 0 && high < after_event_id) continue;
        TrackedLocation entry;
        entry.location = it->first;
        entry.slot = it->second;
        entry.low = location_low_event(it->second);
        selected.push_back(entry);
      }
    }
  }
  std::sort(selected.begin(), selected.end(), by_low_event);

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
    // Stop at a location boundary, never inside one: a half-written envelope
    // would be a cardinality fault downstream, and the resume point would not
    // be expressible.  The first location is always emitted, so a budget
    // smaller than one envelope makes progress instead of looping forever.
    if (budget != 0 && emitted > 0
        && envelope_bytes(buffer, expression_artifact) >= budget) {
      complete = false;
      next_after = selected[index].low;
      break;
    }
    const TrackedLocation &entry = selected[index];
    // Deliberately not `budget`: the document's budget is a boundary between
    // locations, never a cut inside one.  Passing it down here let an envelope
    // be truncated mid-location while the document still reported
    // complete:true -- a silent truncation, which is the one failure mode a
    // reader cannot see.  Each envelope keeps its own per-envelope bound; one
    // oversized location may overshoot maxBytes, which is what "the first
    // location is always emitted" already concedes.
    write_versions_envelope(writer, buffer, expression_artifact,
                            entry.location, entry.slot.versions,
                            entry.slot.reads, true,
                            entry.slot.writer_set_complete,
                            entry.slot.read_log_complete, 0);
    writer.EndObject();
    emitted++;
  }
  writer.EndArray();
  writer.Key("locationCount");
  writer.Int64((jlong) emitted);
  // What this answer holds, and where to resume.  A truncated read-out that
  // did not say so is the one failure mode invisible downstream.
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
  VersionList versions;
  std::vector<ReadRecord> reads;
  bool complete = true;
  bool read_log_complete = true;
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
    }
  }

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  VmExpressionArtifactScope expression_artifact;
  write_versions_envelope(writer, buffer, expression_artifact, location,
                          versions, reads, selected, complete,
                          read_log_complete, 0);
  expression_artifact.write_table(writer);
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


/** The value an array element holds right now. */
bool observe_element(arrayOop array, int index, Expression **value) {
  if (array == NULL || index < 0 || index >= array->length()) return false;
  BasicType type = ArrayKlass::cast(array->klass())->element_type();
  if (type == T_OBJECT || type == T_ARRAY) {
    oop element = objArrayOop(array)->obj_at(index);
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
  *value = SharedFieldVersions::primitive_expression(type, bits);
  return *value != NULL;
}

} // anonymous namespace

std::string ConcolicMngr::getTrackedLocationVersions(jlong after_event_id,
                                                     jint max_bytes) {
  return SharedFieldVersions::tracked_locations(after_event_id, max_bytes);
}

jlong ConcolicMngr::armSharedPrimitiveFieldRead(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor, jlong value_bits) {
  if (!can_explicitly_symbolize() || ctx == NULL) {
    return SharedFieldVersions::REPLAY_READ_NO_CONTEXT;
  }
  if (owner.is_null()
      || declaring_class == NULL || declaring_class[0] == '\0'
      || field_name == NULL || field_name[0] == '\0'
      || descriptor == NULL || descriptor[0] == '\0') {
    return SharedFieldVersions::REPLAY_READ_MISSING_METADATA;
  }

  ResourceMark rm;
  fieldDescriptor field;
  SharedFieldVersions::Location location;
  oop carrier_owner = NULL;
  jlong status = 0;
  if (!resolve_field_location(owner(), declaring_class, field_name, descriptor,
                              &location, &field, &carrier_owner, &status)) {
    return SharedFieldVersions::REPLAY_READ_FIELD_NOT_FOUND;
  }
  BasicType type = field.field_type();
  if (location.kind != SharedFieldVersions::LOC_INSTANCE_FIELD
      || !(type == T_BOOLEAN || type == T_BYTE || type == T_CHAR
           || type == T_SHORT || type == T_INT || type == T_LONG)) {
    return SharedFieldVersions::REPLAY_READ_UNSUPPORTED;
  }
  SymInstance *shadow = ctx->find_sym_inst(carrier_owner);
  if (shadow == NULL) {
    return SharedFieldVersions::REPLAY_READ_NOT_SELECTED;
  }
  location.owner = shadow->get_sym_rid();
  return SharedFieldVersions::arm_primitive_read(
      ctx->get_context_id(), ctx->region_enter_event(), location, type,
      value_bits);
}

jlong ConcolicMngr::confirmSharedPrimitiveFieldRead(jlong token) {
  if (ctx == NULL) return SharedFieldVersions::REPLAY_READ_NO_CONTEXT;
  return SharedFieldVersions::confirm_primitive_read(
      ctx->get_context_id(), token);
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
  if (!observe_element(target, index, &initial)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  SharedFieldVersions::Location location(
      shadow->get_sym_rid(), index, SharedFieldVersions::LOC_ARRAY_ELEMENT);
  jlong version_id = SharedFieldVersions::select_carrier(location, initial);
  if (version_id == 0) {
    if (SharedFieldVersions::is_tracked(location)) {
      ctx->set_pc_admitted(true);
    }
    return SharedFieldVersions::SELECT_ALREADY_SELECTED;
  }
  ctx->set_pc_admitted(true);
  return version_id;
}

jlong ConcolicMngr::selectSharedMapCarrier(Handle map) {
  if (!can_explicitly_symbolize()) {
    return SharedFieldVersions::SELECT_NO_ACTIVE_CONTEXT;
  }
  if (map.is_null()) return SharedFieldVersions::SELECT_MISSING_METADATA;
  oop target = map();
  // Either whole-state algebra this location kind resolves over will do: an
  // indexed container's state answers APPEND/INSERT/WRITE/REMOVE/CLEAR
  // exactly as an associative one answers PUT/REMOVE/CLEAR, and both address
  // the one SLOT_WHOLE_STATE slot.  What is refused is a container whose
  // mutations no model intercepts, which would be selected and then silently
  // never versioned.
  if (!ContainerSupport::whole_state_selectable(target)) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }

  // Forcing the state root is what makes the container addressable at all: it
  // mints the container shadow the location's owner id is taken from, and it
  // is also the INITIAL version's value, so "the state this container started
  // in" is an ordinary candidate rather than a hole.  Built here, outside
  // every version lock, exactly as the scalar path builds its initial
  // expression.  The shape is the container's own, never a literal: rooting
  // an indexed container under the associative algebra would give it a state
  // no later mutation of it can extend.
  Expression *root = ctx->container_state(
      target, ContainerSupport::shape(target));
  if (root == NULL) return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;

  SharedFieldVersions::Location location =
      ContainerSupport::state_location(target);
  if (!location.is_valid()) {
    return SharedFieldVersions::SELECT_UNSUPPORTED_TARGET;
  }
  // What the INITIAL value says about the pre-selection contents.  The offer
  // that ran just before this selection is the authority: only it can tell a
  // container that held nothing from one whose content the bound refused, and
  // both of those from one whose recorded history was kept with no
  // recoverable base.  The state root left behind cannot tell them apart,
  // which is why the answer is recorded rather than inferred from it.
  SharedFieldVersions::InitialSnapshot snapshot;
  int answer = ConcolicMngr::SNAPSHOT_NOT_SELECTABLE;
  int noted_entries = -1;
  if (SharedFieldVersions::initial_snapshot_note(
          ctx->canonical_container_id(target), &answer, &noted_entries)) {
    switch (answer) {
      case ConcolicMngr::SNAPSHOT_INSTALLED:
      case ConcolicMngr::SNAPSHOT_REBASED_UNDER_HISTORY:
        snapshot.stated = true;
        snapshot.entries = noted_entries;
        break;
      case ConcolicMngr::SNAPSHOT_REFUSED_OVER_BOUND:
      case ConcolicMngr::SNAPSHOT_KEPT_EXISTING_HISTORY:
        snapshot.truncated = true;
        snapshot.entries = noted_entries;
        break;
      default:
        break;
    }
  } else {
    // No offer was recorded for this container.  The value itself still
    // answers when it stands on a base this recorder stated, and -1 -- not
    // zero -- is how it says it does not.
    int chain = ContainerSupport::snapshot_entry_count(root);
    if (chain >= 0) {
      snapshot.stated = true;
      snapshot.entries = chain;
    }
  }
  jlong version_id = SharedFieldVersions::select_carrier(
      location, root, snapshot);
  if (version_id == 0) {
    if (SharedFieldVersions::is_tracked(location)) {
      // Retention by value may have started this container's log before the
      // runtime reached here, in which case publish_state already wrote its
      // INITIAL base -- but only this offer knows what the container held
      // *before* tracking, so hand that fact to the version that exists.
      // Without it the base reads as "contents unknown" and a relation chain
      // standing on it cannot be closed, which is what happened to bug3's
      // allKeys base on laneVM4.
      SharedFieldVersions::adopt_initial_snapshot(location, snapshot);
      ctx->set_pc_admitted(true);
    }
    return SharedFieldVersions::SELECT_ALREADY_SELECTED;
  }
  ctx->set_pc_admitted(true);
  return version_id;
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
