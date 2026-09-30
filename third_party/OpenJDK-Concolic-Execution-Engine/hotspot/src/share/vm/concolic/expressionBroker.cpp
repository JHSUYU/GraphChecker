#include "concolic/expressionBroker.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/consumerBoundaryExpression.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "oops/klass.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/fieldDescriptor.hpp"
#include "runtime/os.hpp"
#include "utilities/ostream.hpp"
#include <string.h>

#ifdef ENABLE_CONCOLIC

jlong ExpressionBroker::_epoch = 0;
bool ExpressionBroker::_open = false;
jlong ExpressionBroker::_next_serial = 1;
ExpressionBroker::LeafStore ExpressionBroker::_leaves;
pthread_mutex_t ExpressionBroker::_mutex = PTHREAD_MUTEX_INITIALIZER;

namespace {

const jlong SERIAL_MASK = 0xffffffffLL;
const jlong MAX_EPOCH = 0x7fffffffLL;

class BrokerLock {
public:
  BrokerLock(pthread_mutex_t *mutex) : _mutex(mutex) {
    pthread_mutex_lock(_mutex);
  }
  ~BrokerLock() { pthread_mutex_unlock(_mutex); }
private:
  pthread_mutex_t *_mutex;
};

bool is_blank(const char *text) {
  return text == NULL || text[0] == '\0';
}

// An exact manual handoff leaf may be concrete in this replay even though it
// still has to cross the communication boundary as one value.  Preserve that
// lineage with a typed constant expression; unlike explicit symbolization,
// this adds no solver freedom.  References deliberately stay unsupported
// here: their existing "concrete" helpers allocate symbolic object identity,
// which would recreate the object-token fallback the live handle replaced.
Expression *exact_concrete_primitive(oop owner,
                                     const fieldDescriptor &field) {
  const int offset = field.offset();
  const BasicType type = field.field_type();
  jlong bits;
  switch (type) {
    case T_BOOLEAN:
      bits = SharedFieldVersions::raw_bits(
          (jboolean)(owner->bool_field(offset) ? 1 : 0));
      break;
    case T_BYTE:
      bits = SharedFieldVersions::raw_bits(owner->byte_field(offset));
      break;
    case T_CHAR:
      bits = SharedFieldVersions::raw_bits(owner->char_field(offset));
      break;
    case T_SHORT:
      bits = SharedFieldVersions::raw_bits(owner->short_field(offset));
      break;
    case T_INT:
      bits = SharedFieldVersions::raw_bits(owner->int_field(offset));
      break;
    case T_LONG:
      bits = SharedFieldVersions::raw_bits(owner->long_field(offset));
      break;
    case T_FLOAT:
      bits = SharedFieldVersions::raw_bits(owner->float_field(offset));
      break;
    case T_DOUBLE:
      bits = SharedFieldVersions::raw_bits(owner->double_field(offset));
      break;
    default:
      return NULL;
  }
  return SharedFieldVersions::primitive_expression(type, bits);
}

} // anonymous namespace

void ExpressionBroker::open_session(jlong session_id) {
  BrokerLock guard(&_mutex);
  guarantee(_leaves.empty(), "handoff table outlived its session");
  _leaves.clear();
  _next_serial = 1;

  // Deliberately not os::random(): HotSpot's global RNG also produces
  // identity hash codes, so drawing from it here would shift unrelated
  // program behaviour (hash iteration order, for one) purely because a
  // region was started.  Mix a local counter with the clock instead.
  static jlong session_sequence = 0;
  jlong salt = (jlong) os::javaTimeNanos();
  salt ^= (session_id + ++session_sequence) * (jlong) 0x9E3779B97F4A7C15ULL;
  salt ^= (jlong) (((julong) salt) >> 29);
  salt *= (jlong) 0xBF58476D1CE4E5B9ULL;
  salt ^= (jlong) (((julong) salt) >> 32);
  salt &= MAX_EPOCH;
  if (salt == 0) salt = 1;
  // Never repeat the previous session's salt.  Rejecting a predecessor's
  // token must be a guarantee, not a 1-in-2^31 probability.
  if (salt == _epoch) salt = (salt % MAX_EPOCH) + 1;
  _epoch = salt;
  _open = true;
}

void ExpressionBroker::close_session() {
  BrokerLock guard(&_mutex);
  _leaves.clear();
  _next_serial = 1;
  _open = false;
}

jlong ExpressionBroker::publish(
    Expression *expression, const std::string &descriptor,
    jlong export_event_id, LeafKind kind,
    const std::string &container_shape, const std::string &array_class,
    int array_length) {
  if (expression == NULL) return HANDOFF_NO_ACTIVE_REGION;

  BrokerLock guard(&_mutex);
  if (!_open) return HANDOFF_NO_ACTIVE_REGION;
  if (_next_serial > SERIAL_MASK) return HANDOFF_NO_ACTIVE_REGION;

  jlong serial = _next_serial++;
  Leaf leaf;
  leaf.expression = expression;
  leaf.descriptor = descriptor;
  leaf.kind = kind;
  leaf.container_shape = container_shape;
  leaf.array_class = array_class;
  leaf.array_length = array_length;
  leaf.export_event_id = export_event_id;
  _leaves.insert(std::make_pair(serial, leaf));
  return (_epoch << 32) | serial;
}

// Requires _mutex.  Splits token validation from what each caller does with
// the entry, so that validation and mutation stay in one critical section.
ExpressionBroker::HandoffStatus ExpressionBroker::find_locked(
    jlong handle, LeafStore::iterator *found) {
  if (!_open) return HANDOFF_NO_ACTIVE_REGION;
  if (handle <= 0) return HANDOFF_FOREIGN_HANDLE;
  if (((handle >> 32) & MAX_EPOCH) != _epoch) return HANDOFF_FOREIGN_HANDLE;

  jlong serial = handle & SERIAL_MASK;
  if (serial == 0 || serial >= _next_serial) return HANDOFF_UNKNOWN_HANDLE;

  LeafStore::iterator entry = _leaves.find(serial);
  if (entry == _leaves.end()) return HANDOFF_UNKNOWN_HANDLE;
  *found = entry;
  return HANDOFF_OK;
}

ExpressionBroker::HandoffStatus ExpressionBroker::resolve(jlong handle,
                                                          Leaf *leaf) {
  BrokerLock guard(&_mutex);
  LeafStore::iterator found;
  HandoffStatus status = find_locked(handle, &found);
  if (status != HANDOFF_OK) return status;
  if (leaf != NULL) *leaf = found->second;
  return HANDOFF_OK;
}

// ---------------------------------------------------------------------------
// ConcolicMngr facade
//
// These ConcolicMngr entry points are defined here, next to the broker
// they drive, so that the whole symbolic handoff -- addressing, validation,
// token table and serialization -- can be read as one unit.  Everything they
// The VM handoff is generic: an exact field, its descriptor, and an opaque
// live handle. Communication provenance remains in the application trace.
// ---------------------------------------------------------------------------

jlong ConcolicMngr::exportExpression(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor, jlong *export_event_out) {
  // CONTRACT-SPEC §1: the exporter is an endpoint of the VALUE_HANDOFF edge and
  // has to be able to name its own event, or its interaction row cannot say
  // which export it published and the Composer is left counting ports.
  if (export_event_out != NULL) *export_event_out = 0;
  int session_members = 0;
  bool workload_open = false;
  SessionState session_state = SESSION_CLOSED;
  jlong session_id = 0;
  session_snapshot(&session_members, &workload_open, &session_state,
                   &session_id);
  const bool local_context = has_active_context();
  // A selected sender records its local PC as before.  A non-selected sender
  // may only forward a value that already lives in the workload-owned session
  // heap; it gains no ThreadContext, stack shadow or path condition of its own.
  if ((!local_context && (!workload_open || session_state != SESSION_OPEN))
      || !GlobalSymbolicSession::is_open()
      || !ExpressionBroker::is_open()) {
    return ExpressionBroker::HANDOFF_NO_ACTIVE_REGION;
  }
  if (owner.is_null() || is_blank(declaring_class) || is_blank(field_name)
      || is_blank(descriptor)) {
    return ExpressionBroker::HANDOFF_MISSING_METADATA;
  }

  ResourceMark rm;
  fieldDescriptor field;
  Klass *declaring = OopUtils::get_local_fd_by_name(
      owner(), std::string(declaring_class), std::string(field_name),
      std::string(descriptor), field);
  if (declaring == NULL || field.is_static()) {
    return ExpressionBroker::HANDOFF_FIELD_NOT_FOUND;
  }

  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  SymInstance *instance = heap == NULL ? NULL : heap->find_sym_inst(owner());
  Expression *shadow = instance == NULL
      ? NULL : instance->get(field.offset());
  ExpressionBroker::LeafKind leaf_kind =
      ExpressionBroker::FIELD_EXPRESSION;
  std::string container_shape;
  std::string array_class;
  int array_length = -1;
  const BasicType field_type = field.field_type();
  if (field_type == T_OBJECT || field_type == T_ARRAY) {
    oop referent = owner()->obj_field(field.offset());
    const char *shape = referent == NULL
        ? NULL : ContainerSupport::shape(referent);
    if (shape != NULL) {
      // Container transport is contents/state transport.  It is deliberately
      // a pure lookup: no state means the selected producer did not build the
      // required lineage, so export must fail instead of snapshotting or
      // publishing object identity.
      shadow = heap == NULL || referent == NULL
          ? NULL : heap->find_container_state(referent);
      ContainerExpression *state = shadow == NULL
          ? NULL : shadow->as_container_expression();
      if (state == NULL || state->get_shape() != shape) {
        shadow = NULL;
      } else {
        leaf_kind = ExpressionBroker::CONTAINER_STATE;
        container_shape = shape;
        if (referent->is_array()) {
          array_class = referent->klass()->name()->as_C_string();
          array_length = ((arrayOop)referent)->length();
        }
      }
    }
  }
  // A concrete primitive is still the exact value this selected manual leaf
  // exports.  Publishing its typed constant preserves the live-handle and
  // VALUE_HANDOFF lineage without minting a solver variable.  Do not extend
  // this to references: their fallback representation is symbolic object
  // identity, not a concrete value term.
  if (shadow == NULL && field_type != T_OBJECT && field_type != T_ARRAY) {
    shadow = exact_concrete_primitive(owner(), field);
  }
  if (shadow == NULL) return ExpressionBroker::HANDOFF_NOT_SYMBOLIC;

  // A handoff endpoint needs a stable session-local identity for tracing and
  // boundary matching.  Its numeric order is deliberately not a schedule.
  jlong export_event = GlobalSymbolicSession::next_event_id();

  jlong handle = ExpressionBroker::publish(shadow, std::string(descriptor),
                                           export_event, leaf_kind,
                                           container_shape, array_class,
                                           array_length);
  if (handle > 0 && export_event_out != NULL) *export_event_out = export_event;
  return handle;
}

jlong ConcolicMngr::attachExpression(
    Handle owner, const char *declaring_class, const char *field_name,
    const char *descriptor, jlong handle, jlong *attach_event_out) {
  // VM §7: one export may be attached at several explicit receivers,
  // so the export id alone does not name *this* receive.  Both endpoints of
  // the handoff leave the VM together; nothing downstream may guess the
  // attach from the export id alone.
  if (attach_event_out != NULL) *attach_event_out = 0;
  if (!can_explicitly_symbolize() || !ExpressionBroker::is_open()) {
    return ExpressionBroker::HANDOFF_NO_ACTIVE_REGION;
  }
  if (owner.is_null() || is_blank(declaring_class) || is_blank(field_name)
      || is_blank(descriptor)) {
    return ExpressionBroker::HANDOFF_MISSING_METADATA;
  }

  // One atomic lookup under the table lock; no second identity is agreed on
  // afterwards because a live handle already names the expression. The same handle may be
  // attached at several explicit receivers; each attach records its own
  // VALUE_HANDOFF edge, and nothing is tallied.
  ExpressionBroker::Leaf leaf;
  ExpressionBroker::HandoffStatus status =
      ExpressionBroker::resolve(handle, &leaf);
  if (status != ExpressionBroker::HANDOFF_OK) return status;

  ResourceMark rm;
  fieldDescriptor field;
  Klass *declaring = OopUtils::get_local_fd_by_name(
      owner(), std::string(declaring_class), std::string(field_name),
      std::string(descriptor), field);
  if (declaring == NULL || field.is_static()) {
    return ExpressionBroker::HANDOFF_FIELD_NOT_FOUND;
  }

  // A destination of another sort cannot hold this expression. A caller that
  // widens or reinterprets gets a named gap and keeps its concrete value; it
  // never gets a silent binding.
  if (leaf.descriptor != descriptor) {
    return ExpressionBroker::HANDOFF_SORT_MISMATCH;
  }

  SymInstance *instance = ctx->get_or_alloc_sym_inst(owner());
  if (instance == NULL) return ExpressionBroker::HANDOFF_UNSUPPORTED_TARGET;

  oop destination = NULL;
  if (leaf.kind == ExpressionBroker::CONTAINER_STATE) {
    destination = owner()->obj_field(field.offset());
    const char *shape = destination == NULL
        ? NULL : ContainerSupport::shape(destination);
    if (shape == NULL) {
      return ExpressionBroker::HANDOFF_UNSUPPORTED_TARGET;
    }
    if (leaf.container_shape != shape) {
      return ExpressionBroker::HANDOFF_SORT_MISMATCH;
    }
    if (destination->is_array()) {
      std::string target_class(
          destination->klass()->name()->as_C_string());
      if (leaf.array_class != target_class
          || leaf.array_length != ((arrayOop)destination)->length()) {
        return ExpressionBroker::HANDOFF_SORT_MISMATCH;
      }
    } else if (!leaf.array_class.empty() || leaf.array_length >= 0) {
      return ExpressionBroker::HANDOFF_SORT_MISMATCH;
    }
  }

  // The attach id is also the transparent consumer boundary's identity.
  // Allocate it only after every fallible validation succeeds.
  jlong attach_event = GlobalSymbolicSession::next_event_id();
  if (attach_event <= 0) {
    return ExpressionBroker::HANDOFF_NO_ACTIVE_REGION;
  }
  Expression *attached = new ConsumerBoundaryExpression(
      leaf.expression, leaf.descriptor,
      ConsumerBoundaryExpression::RPC_ATTACH, attach_event);

  // Same contract as the other explicit input APIs: this VM operation is
  // valid inside a paused bookkeeping subtree, so lift the pause only while
  // the symbolic state is mutated and then restore the caller's depth.
  int pause_depth = ctx->path_condition_pause_depth();
  while (ctx->path_condition_pause_depth() > 0) {
    ctx->resume_path_condition_recording();
  }
  // A scalar/reference leaf lives in the exact destination field shadow.  A
  // container leaf instead names the contents of the reconstructed referent:
  // attach that state to the receiver's actual array/container oop so its
  // SIZE/READ/mutation bytecodes compose on the sender state.  Never copy the
  // sender oop or symbolic RID.
  if (leaf.kind == ExpressionBroker::CONTAINER_STATE) {
    // ConsumerBoundaryExpression delegates structural container inspection to
    // its payload.  Later operations still use `attached` as their receiver,
    // so the provenance marker remains in the container expression chain.
    ctx->set_container_state(destination, attached);
    // And it is a write of the container's whole state, published as one
    // (D7): a reader of a container whose log had already begun resolved to
    // the state before the attach.
    ContainerSupport::publish_attached_state(destination, attached);
  } else {
    instance->set_sym_exp(field.offset(), attached);
    instance->mark_semantic_expression();
    // An attach is a write of the message leaf to this location by the
    // attaching occurrence, so it is published as one.  The shadow alone was
    // not enough: a read of a location that has a log resolves over the log,
    // and a destination whose log had already been started -- a field the
    // receiver assigned before the attach, which is what every key-delivery
    // case does (`receiver.keyId = sender.keyId` here, and the DataNode key
    // fields in 11741/17897/17899) -- took the newest ordinary WRITE and
    // never consulted the shadow, so the attached expression was dropped and
    // the RPC lineage was cut at the attach hop.
    //
    // Published for every attach, not only for a location that already has a
    // log: publish_value() starts the log at the first symbolic value, so the
    // uniform rule needs no case analysis and cannot leave a hop stated in
    // one place for one destination and another place for the next.  The
    // version's own value is the RPC_ATTACH boundary, which is where this
    // version says where it came from; `Version::operation` renders only for
    // VERSION_STATE, and the consumer's version-kind vocabulary is closed.
    SharedFieldVersions::Location location(
        instance->get_sym_rid(), field.offset(),
        SharedFieldVersions::LOC_INSTANCE_FIELD);
    // Folded outside every engine lock, as the store's concurrency contract
    // requires; the same guard a putfield of this value would publish.
    Expression *guard = ctx->path_guard();
    // The attach names the value the field holds, so that word, read under
    // the location's stripe, is the one this version stored.
    SharedFieldVersions::publish_held(
        location,
        SharedFieldVersions::Cell(
            owner(), field.field_type(),
            SharedFieldVersions::wrapper_value_type(field.signature())
                != T_ILLEGAL),
        attached, guard, SharedFieldVersions::VERSION_WRITE);
  }
  ctx->set_pc_admitted(true);
  for (int index = 0; index < pause_depth; ++index) {
    ctx->pause_path_condition_recording();
  }
  if (attach_event_out != NULL) *attach_event_out = attach_event;
  return leaf.export_event_id;
}

#endif // ENABLE_CONCOLIC
