#ifdef ENABLE_CONCOLIC

#include "concolic/eventLedger.hpp"

#include "concolic/concolicMngr.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/threadContext.hpp"
#include "webridge/utils/rapidjson/stringbuffer.h"
#include "webridge/utils/rapidjson/writer.h"

bool EventLedger::_open = false;
EventLedger::ReleaseStore EventLedger::_releases;
std::vector<EventLedger::Event> EventLedger::_events;
bool EventLedger::_events_truncated = false;
std::vector<EventLedger::Edge> EventLedger::_edges;
std::map<jlong, std::vector<jlong> > EventLedger::_successors;
std::vector<jlong> EventLedger::_event_ids;
bool EventLedger::_domain_saturated = false;
pthread_mutex_t EventLedger::_mutex = PTHREAD_MUTEX_INITIALIZER;

namespace {

class LedgerLock {
public:
  LedgerLock(pthread_mutex_t *mutex) : _mutex(mutex) {
    pthread_mutex_lock(_mutex);
  }
  ~LedgerLock() { pthread_mutex_unlock(_mutex); }
private:
  pthread_mutex_t *_mutex;
};

} // anonymous namespace

#define LEDGER_LOCK LedgerLock ledger_guard(&_mutex)

void EventLedger::open_session() {
  LEDGER_LOCK;
  _releases.clear();
  _events.clear();
  _events_truncated = false;
  _edges.clear();
  _successors.clear();
  _event_ids.clear();
  _domain_saturated = false;
  _open = true;
}

void EventLedger::close_session() {
  LEDGER_LOCK;
  _releases.clear();
  _events.clear();
  _events_truncated = false;
  _edges.clear();
  _successors.clear();
  _event_ids.clear();
  _domain_saturated = false;
  _open = false;
}

bool EventLedger::is_recording() {
  return _open && SharedFieldVersions::has_carriers();
}

jlong EventLedger::record(int kind, sym_rid_t object, int slot,
                          const char *detail) {
  if (ConcolicMngr::ctx == NULL) return 0;
  Event event;
  event.event_id = GlobalSymbolicSession::next_event_id();
  event.kind = kind;
  event.context_id = ConcolicMngr::ctx->get_context_id();
  event.java_thread_id = ConcolicMngr::ctx->get_owner_java_thread_id();
  event.step = ConcolicMngr::ctx->clock_step();
  event.object = object;
  event.slot = slot;
  event.region_id = ConcolicMngr::ctx->get_region_id();
  event.detail = detail == NULL ? "" : detail;
  // Read before the lock: it is this thread's own state.
  const jlong previous = ConcolicMngr::ctx->last_event_id();

  {
    LEDGER_LOCK;
    if (!_open) return 0;
    _events.push_back(event);
    _event_ids.push_back(event.event_id);
    if (_events.size() > MAX_EVENTS) {
      // Dropped in blocks rather than one at a time: erasing a single front
      // element of a full vector moves every remaining entry, which turns the
      // steady state into a per-event O(MAX_EVENTS) copy.  The id list is
      // trimmed with it, or it would grow without bound and keep answering
      // propose_order about events the log no longer holds.
      const size_t drop = MAX_EVENTS / 4;
      _events.erase(_events.begin(), _events.begin() + drop);
      _event_ids.erase(_event_ids.begin(), _event_ids.begin() + drop);
      _events_truncated = true;
    }
    // Program order is an edge of the same domain as every other channel,
    // not a separate implicit rule.  That is what lets a candidate order be
    // checked against it.
    if (previous != 0) {
      add_edge_locked(previous, event.event_id, EDGE_PROGRAM_ORDER);
    }
  }
  ConcolicMngr::ctx->set_last_event_id(event.event_id);
  return event.event_id;
}

jlong EventLedger::record_session_event(int kind, sym_rid_t object, int slot,
                                        const char *detail) {
  Event event;
  event.event_id = GlobalSymbolicSession::next_event_id();
  event.kind = kind;
  event.context_id = 0;
  event.java_thread_id = 0;
  event.step = 0;
  event.object = object;
  event.slot = slot;
  event.region_id = "";
  event.detail = detail == NULL ? "" : detail;

  LEDGER_LOCK;
  if (!_open) return 0;
  _events.push_back(event);
  _event_ids.push_back(event.event_id);
  if (_events.size() > MAX_EVENTS) {
    const size_t drop = MAX_EVENTS / 4;
    _events.erase(_events.begin(), _events.begin() + drop);
    _event_ids.erase(_event_ids.begin(), _event_ids.begin() + drop);
    _events_truncated = true;
  }
  return event.event_id;
}

void EventLedger::add_edge_locked(jlong before, jlong after, int kind) {
  if (before == 0 || after == 0 || before == after) return;
  if (_edges.size() >= MAX_EDGES) {
    _domain_saturated = true;
    return;
  }
  _edges.push_back(Edge(before, after, kind));
  _successors[before].push_back(after);
}

void EventLedger::add_observed_edge(jlong before, jlong after, int kind) {
  LEDGER_LOCK;
  if (!_open) return;
  add_edge_locked(before, after, kind);
}

bool EventLedger::known_event_locked(jlong event_id) {
  for (size_t index = 0; index < _event_ids.size(); ++index) {
    if (_event_ids[index] == event_id) return true;
  }
  return false;
}

bool EventLedger::reaches_locked(jlong from, jlong target) {
  std::vector<jlong> stack;
  std::map<jlong, bool> seen;
  stack.push_back(from);
  while (!stack.empty()) {
    jlong current = stack.back();
    stack.pop_back();
    if (current == target) return true;
    if (seen[current]) continue;
    seen[current] = true;
    std::map<jlong, std::vector<jlong> >::const_iterator next =
        _successors.find(current);
    if (next == _successors.end()) continue;
    for (size_t index = 0; index < next->second.size(); ++index) {
      stack.push_back(next->second[index]);
    }
  }
  return false;
}

int EventLedger::propose_order(jlong before, jlong after) {
  LEDGER_LOCK;
  if (!_open) return ORDER_NOT_OPEN;
  if (before == after) return ORDER_SELF_EDGE;
  if (!known_event_locked(before) || !known_event_locked(after)) {
    return ORDER_UNKNOWN_EVENT;
  }
  if (_domain_saturated || _edges.size() >= MAX_EDGES) {
    // Refusing is the only honest answer: an edge added past the budget would
    // not be checked, and an unchecked edge can hide a cycle.
    _domain_saturated = true;
    return ORDER_DOMAIN_SATURATED;
  }
  // `after` already reaching `before` means this edge would close a loop, and
  // a cyclic order describes no execution at all.
  if (reaches_locked(after, before)) return ORDER_CYCLIC;
  add_edge_locked(before, after, EDGE_CANDIDATE);
  return ORDER_OK;
}

bool EventLedger::is_acyclic() {
  LEDGER_LOCK;
  // Kahn's algorithm over the whole relation.  This answers "is the recorded
  // partial order still a partial order"; it does not produce or imply a
  // schedule, and no caller can ask for one.
  std::map<jlong, int> incoming;
  for (size_t index = 0; index < _event_ids.size(); ++index) {
    incoming[_event_ids[index]] = 0;
  }
  for (size_t index = 0; index < _edges.size(); ++index) {
    incoming[_edges[index].after]++;
    if (incoming.find(_edges[index].before) == incoming.end()) {
      incoming[_edges[index].before] = 0;
    }
  }
  std::vector<jlong> ready;
  for (std::map<jlong, int>::const_iterator it = incoming.begin();
       it != incoming.end(); ++it) {
    if (it->second == 0) ready.push_back(it->first);
  }
  size_t retired = 0;
  while (!ready.empty()) {
    jlong current = ready.back();
    ready.pop_back();
    ++retired;
    std::map<jlong, std::vector<jlong> >::const_iterator next =
        _successors.find(current);
    if (next == _successors.end()) continue;
    for (size_t index = 0; index < next->second.size(); ++index) {
      if (--incoming[next->second[index]] == 0) {
        ready.push_back(next->second[index]);
      }
    }
  }
  return retired == incoming.size();
}

void EventLedger::publish_release(sym_rid_t object, int slot, jlong context_id,
                                  jlong release_event_id,
                                  const VectorClock &clock) {
  if (object == NULL_SYM_RID) return;
  LEDGER_LOCK;
  if (!_open) return;
  // Join rather than replace. Multiple lifecycle releases may each contribute
  // order to the acquiring thread, and dropping one would silently narrow the
  // happens-before relation.
  ReleaseRecord &record = _releases[ReleaseKey(object, slot)];
  record.clock.join(clock);
  if (release_event_id != 0) {
    record.last_release_event[context_id] = release_event_id;
  }
}

bool EventLedger::acquire_into(sym_rid_t object, int slot, VectorClock *clock,
                               std::vector<jlong> *releasers) {
  if (object == NULL_SYM_RID || clock == NULL) return false;
  LEDGER_LOCK;
  if (!_open) return false;
  ReleaseStore::const_iterator found = _releases.find(ReleaseKey(object, slot));
  if (found == _releases.end()) return false;
  // Copied out, never handed out by reference: a reference would escape the
  // lock and outlive a concurrent release.
  *clock = found->second.clock;
  if (releasers != NULL) {
    for (std::map<jlong, jlong>::const_iterator it =
             found->second.last_release_event.begin();
         it != found->second.last_release_event.end(); ++it) {
      releasers->push_back(it->second);
    }
  }
  return true;
}

size_t EventLedger::event_count() {
  LEDGER_LOCK;
  return _events.size();
}

size_t EventLedger::edge_count() {
  LEDGER_LOCK;
  return _edges.size();
}

const char *EventLedger::event_kind_name(int kind) {
  switch (kind) {
    case EVENT_VOLATILE_READ:  return "VOLATILE_READ";
    case EVENT_VOLATILE_WRITE: return "VOLATILE_WRITE";
    case EVENT_THREAD_START:   return "THREAD_START";
    case EVENT_THREAD_JOIN:    return "THREAD_JOIN";
    case EVENT_ATOMIC_RMW:     return "ATOMIC_RMW";
    case EVENT_ATOMIC_CAS:     return "ATOMIC_CAS";
    case EVENT_FIELD_WRITE:    return "FIELD_WRITE";
    case EVENT_FIELD_READ:     return "FIELD_READ";
    case EVENT_REGION_ENTER:   return "REGION_ENTER";
    case EVENT_REGION_EXIT:    return "REGION_EXIT";
    case EVENT_HANDOFF_EXPORT: return "HANDOFF_EXPORT";
    case EVENT_HANDOFF_ATTACH: return "HANDOFF_ATTACH";
    default:                   return "UNKNOWN";
  }
}

const char *EventLedger::edge_kind_name(int kind) {
  switch (kind) {
    case EDGE_PROGRAM_ORDER:   return "PROGRAM_ORDER";
    case EDGE_SYNCHRONIZATION: return "SYNCHRONIZATION";
    case EDGE_FIELD_READ_FROM: return "FIELD_READ_FROM";
    case EDGE_VALUE_HANDOFF:   return "VALUE_HANDOFF";
    case EDGE_REGION:          return "REGION";
    case EDGE_CANDIDATE:       return "CANDIDATE";
    default:                   return "UNKNOWN";
  }
}

const char *EventLedger::order_status_name(int status) {
  switch (status) {
    case ORDER_OK:                return "OK";
    case ORDER_NOT_OPEN:          return "NOT_OPEN";
    case ORDER_UNKNOWN_EVENT:     return "UNKNOWN_EVENT";
    case ORDER_SELF_EDGE:         return "SELF_EDGE";
    case ORDER_CYCLIC:            return "CYCLIC";
    case ORDER_DOMAIN_SATURATED:  return "DOMAIN_SATURATED";
    default:                      return "UNKNOWN";
  }
}

std::string EventLedger::describe() {
  using namespace rapidjson;
  std::vector<Event> events;
  std::vector<Edge> edges;
  bool truncated;
  bool saturated;
  bool open;
  {
    LEDGER_LOCK;
    events = _events;
    edges = _edges;
    truncated = _events_truncated;
    saturated = _domain_saturated;
    open = _open;
  }
  const bool acyclic = is_acyclic();

  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("SESSION_EVENT_LEDGER");
  writer.Key("open");
  writer.Bool(open);
  writer.Key("recording");
  writer.Bool(is_recording());
  writer.Key("truncated");
  writer.Bool(truncated);
  writer.Key("domainSaturated");
  writer.Bool(saturated);
  // The relation is reported as a set of edges and is asserted to be a
  // partial order.  It is deliberately never linearized: a total schedule is
  // not something this engine constructs or enumerates.
  writer.Key("partialOrder");
  writer.Bool(true);
  writer.Key("acyclic");
  writer.Bool(acyclic);
  writer.Key("events");
  writer.StartArray();
  for (size_t index = 0; index < events.size(); ++index) {
    const Event &event = events[index];
    writer.StartObject();
    writer.Key("eventId");
    writer.Int64(event.event_id);
    writer.Key("eventKind");
    writer.String(event_kind_name(event.kind));
    writer.Key("contextId");
    writer.Int64(event.context_id);
    writer.Key("javaThreadId");
    writer.Int64(event.java_thread_id);
    writer.Key("step");
    writer.Int64(event.step);
    writer.Key("objectSymRid");
    writer.Int64((jlong) event.object);
    writer.Key("slot");
    writer.Int(event.slot);
    writer.Key("regionId");
    writer.String(event.region_id.c_str());
    writer.Key("detail");
    writer.String(event.detail.c_str());
    writer.EndObject();
  }
  writer.EndArray();

  writer.Key("order");
  writer.StartArray();
  for (size_t index = 0; index < edges.size(); ++index) {
    writer.StartObject();
    writer.Key("beforeEventId");
    writer.Int64(edges[index].before);
    writer.Key("afterEventId");
    writer.Int64(edges[index].after);
    writer.Key("edgeKind");
    writer.String(edge_kind_name(edges[index].kind));
    writer.EndObject();
  }
  writer.EndArray();
  writer.EndObject();
  return std::string(buffer.GetString(), buffer.GetLength());
}

// ---------------------------------------------------------------------------
// The interpreter-facing synchronization hooks.
// ---------------------------------------------------------------------------

void ConcolicMngr::publishThreadStartOrder(oop thread_object) {
  if (!EventLedger::is_recording() || !can_do_concolic()
      || thread_object == NULL) {
    return;
  }
  SymInstance *shadow = ctx->get_or_alloc_sym_inst(thread_object);
  if (shadow == NULL) return;
  ctx->tick_clock();
  jlong started = EventLedger::record(
      EventLedger::EVENT_THREAD_START, shadow->get_sym_rid(),
      EventLedger::SLOT_THREAD_LIFECYCLE, "START");
  // Everything this thread has done happens-before everything the started
  // thread will do.  The child joins this clock when it attaches.
  EventLedger::publish_release(shadow->get_sym_rid(),
                               EventLedger::SLOT_THREAD_LIFECYCLE,
                               ctx->get_context_id(), started, ctx->clock());
}

void ConcolicMngr::acquireThreadStartOrder(oop thread_object) {
  if (!EventLedger::is_recording() || ctx == NULL || thread_object == NULL) {
    return;
  }
  SymInstance *shadow = ctx->find_sym_inst(thread_object);
  if (shadow == NULL) return;
  VectorClock started;
  std::vector<jlong> releasers;
  if (!EventLedger::acquire_into(shadow->get_sym_rid(),
                                 EventLedger::SLOT_THREAD_LIFECYCLE,
                                 &started, &releasers)) {
    return;
  }
  ctx->acquire_clock(started);
  ctx->tick_clock();
  // The child's first event, so that the start edge has something on this
  // side to point at.
  jlong entered = EventLedger::record(
      EventLedger::EVENT_THREAD_START, shadow->get_sym_rid(),
      EventLedger::SLOT_THREAD_LIFECYCLE, "STARTED");
  for (size_t index = 0; index < releasers.size(); ++index) {
    EventLedger::add_observed_edge(releasers[index], entered,
                                   EventLedger::EDGE_SYNCHRONIZATION);
  }
}

void ConcolicMngr::publishThreadTerminationOrder(oop thread_object) {
  if (!EventLedger::is_recording() || ctx == NULL || thread_object == NULL) {
    return;
  }
  SymInstance *shadow = ctx->get_or_alloc_sym_inst(thread_object);
  if (shadow == NULL) return;
  ctx->tick_clock();
  jlong terminated = EventLedger::record(
      EventLedger::EVENT_THREAD_JOIN, shadow->get_sym_rid(),
      EventLedger::SLOT_THREAD_LIFECYCLE, "TERMINATING");
  // Termination releases into the same slot the start edge used.  Joining
  // rather than replacing is what keeps both edges: a joiner learns what the
  // starter knew and what the terminating thread went on to do.
  EventLedger::publish_release(shadow->get_sym_rid(),
                               EventLedger::SLOT_THREAD_LIFECYCLE,
                               ctx->get_context_id(), terminated,
                               ctx->clock());
}

void ConcolicMngr::acquireThreadTerminationOrder(oop thread_object) {
  if (!EventLedger::is_recording() || !can_do_concolic()
      || thread_object == NULL) {
    return;
  }
  // Only look the target up; observing that a thread is dead must not be the
  // operation that gives it a symbolic identity.
  SymInstance *shadow = ctx->find_sym_inst(thread_object);
  if (shadow == NULL) return;
  VectorClock terminated;
  std::vector<jlong> releasers;
  if (!EventLedger::acquire_into(shadow->get_sym_rid(),
                                 EventLedger::SLOT_THREAD_LIFECYCLE,
                                 &terminated, &releasers)) {
    return;
  }
  ctx->acquire_clock(terminated);
  ctx->tick_clock();
  jlong joined = EventLedger::record(
      EventLedger::EVENT_THREAD_JOIN, shadow->get_sym_rid(),
      EventLedger::SLOT_THREAD_LIFECYCLE, "JOIN");
  for (size_t index = 0; index < releasers.size(); ++index) {
    EventLedger::add_observed_edge(releasers[index], joined,
                                   EventLedger::EDGE_SYNCHRONIZATION);
  }
}

void ConcolicMngr::recordVolatileWrite(sym_rid_t owner, int slot) {
  if (!EventLedger::is_recording() || !can_do_concolic()
      || owner == NULL_SYM_RID) {
    return;
  }
  // Evidence only.  The order this write can create already travels on the
  // version it published, keyed to the value it stored, so there is nothing
  // to release into a per-location slot here.
  ctx->tick_clock();
  EventLedger::record(EventLedger::EVENT_VOLATILE_WRITE, owner, slot,
                      "RELEASE");
}

void ConcolicMngr::recordVolatileRead(sym_rid_t owner, int slot,
                                      const VectorClock &writer_clock,
                                      bool exact) {
  if (!EventLedger::is_recording() || !can_do_concolic()
      || owner == NULL_SYM_RID) {
    return;
  }
  if (exact) {
    // Only now is the pairing known, and only for the write this read
    // actually returned.  An ambiguous volatile read joins nothing: claiming
    // order from a write that may not even have executed yet would be an
    // invented happens-before, which is worse than no edge at all.
    ctx->acquire_clock(writer_clock);
  }
  ctx->tick_clock();
  EventLedger::record(EventLedger::EVENT_VOLATILE_READ, owner, slot,
                      exact ? "ACQUIRE" : "ACQUIRE_UNPAIRED");
}

std::string ConcolicMngr::getEventLedger() {
  return EventLedger::describe();
}

jint ConcolicMngr::proposeEventOrder(jlong before_event_id,
                                     jlong after_event_id) {
  return (jint) EventLedger::propose_order(before_event_id, after_event_id);
}

#endif // ENABLE_CONCOLIC
