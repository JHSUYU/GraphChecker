#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "runtime/atomic.hpp"
#include "utilities/ostream.hpp"

#include <pthread.h>

#include <map>
#include <utility>

/**
 * The concrete-position WRITEs of one chain over a Java array's STATE root:
 * (position, ordinal) -> the value the WRITE with that ordinal stored.
 *
 * Every WRITE of the chain shares it, so a read at a position is one lookup
 * however many writes came before.  Only the node that extended it last may
 * extend it again: a chain that forks keeps its log on one branch, and a WRITE
 * on the other decides no read -- its reads build READs, as every read did.
 * The lock is a leaf: nothing under it builds a node or takes another lock.
 */
class ElementWrites {
 public:
  ElementWrites() : _newest(0) { pthread_mutex_init(&_mutex, NULL); }
  ~ElementWrites() { pthread_mutex_destroy(&_mutex); }

  // Records `value` stored at `position` by the state after the one with
  // `ordinal`, and returns the new state's ordinal; 0 when `ordinal` is not
  // the newest, which is a fork.
  uint extend(uint ordinal, jint position, Expression *value,
              const ElementWord &word) {
    pthread_mutex_lock(&_mutex);
    uint next = 0;
    if (ordinal == _newest) {
      next = ++_newest;
      _writes[std::make_pair(position, next)] = Entry(value, word);
    }
    pthread_mutex_unlock(&_mutex);
    return next;
  }

  // What the newest write at `position` no later than `ordinal` stored, and
  // the word it left, or NULL when none did.
  Expression *stored(uint ordinal, jint position, ElementWord *word) {
    pthread_mutex_lock(&_mutex);
    Expression *value = NULL;
    Writes::const_iterator write =
        _writes.upper_bound(std::make_pair(position, ordinal));
    if (write != _writes.begin()) {
      --write;
      if (write->first.first == position) {
        value = write->second.value;
        *word = write->second.word;
      }
    }
    pthread_mutex_unlock(&_mutex);
    return value;
  }

 private:
  struct Entry {
    Expression *value;
    ElementWord word;
    Entry() : value(NULL) {}
    Entry(Expression *stored, const ElementWord &left)
        : value(stored), word(left) {}
  };
  typedef std::map<std::pair<jint, uint>, Entry> Writes;
  pthread_mutex_t _mutex;
  uint _newest;
  Writes _writes;
};

namespace {

// An INDEXED STATE root carries an array's declared length as its one
// argument (a list's root carries none), and WRITE never changes a size.
bool constant_size(const std::string &shape, const std::string &operation,
                   Expression *receiver, const exp_list_t &arguments) {
  if (shape != "INDEXED") return false;
  if (operation == "STATE") {
    jint length = 0;
    return arguments.size() == 1
        && arguments[0]->concrete_int_value(&length);
  }
  ContainerExpression *base = receiver == NULL
      ? NULL : receiver->as_container_expression();
  return operation == "WRITE" && base != NULL && base->has_constant_size();
}

}  // namespace

ContainerExpression::ContainerExpression(
    const char *shape, const char *operation, Expression *receiver,
    const exp_list_t &arguments, BasicType result_type,
    const std::string &java_type, Expression *guard, Expression *owner,
    const ElementWord &word)
    : _shape(shape == NULL ? "" : shape),
      _operation(operation == NULL ? "" : operation),
      _receiver(receiver),
      _arguments(arguments),
      _java_type(java_type.empty()
                     ? std::string(1, type2char(result_type))
                     : java_type),
      _guard(guard),
      _owner(owner),
      _members(-1),
      _constant_size(constant_size(_shape, _operation, receiver,
                                   arguments)),
      _decides_reads(false),
      _ordinal(0),
      _writes(NULL),
      _answer(0) {
  if (_operation == "STATE") {
    // An array's root answers every read no WRITE above it answers: the
    // element is the root's.  Whether the root's elements are the heap's is
    // the array's to say (ContainerSupport::recorded_element).  A list's root
    // carries no length and decides nothing.
    _decides_reads = _constant_size;
    return;
  }
  // The receiver itself, not what a consumer boundary around it delegates
  // to: the boundary is the cross-process provenance of every element, and
  // a READ is what keeps it.
  ContainerExpression *base = receiver == NULL
      ? NULL : receiver->as_container_expression();
  jint position = 0;
  if (_shape != "INDEXED" || _operation != "WRITE" || base == NULL
      || base != receiver || !base->_decides_reads || _arguments.size() != 2
      || !_arguments[0]->concrete_int_value(&position)) {
    return;
  }
  _writes = base->_writes == NULL ? new ElementWrites() : base->_writes;
  _ordinal = _writes->extend(base->_ordinal, position, _arguments[1], word);
  if (_ordinal == 0) {
    _writes = NULL;
    return;
  }
  _decides_reads = true;
}

bool ContainerExpression::derived_container_value(Expression **owner) {
  if (_operation != "ENTRY_VIEW" && _operation != "KEY_VIEW"
      && _operation != "VALUE_VIEW" && _operation != "ITERATOR"
      && _operation != "NEXT" && _operation != "ENTRY") {
    return false;
  }
  *owner = _owner;
  return true;
}

ContainerExpression::~ContainerExpression() {
  if (_ordinal == 1) delete _writes;
}

volatile intptr_t ContainerExpression::answer_count = 0;

void ContainerExpression::state_returned(const ReturnedValue &returned) {
  if (returned.kind == ReturnedValue::UNSTATED) return;
  _returned = returned;
  _answer = (jlong) Atomic::add_ptr((intptr_t) 1, &answer_count);
}

bool ContainerExpression::stored_at(jint position, Expression **stored,
                                    ElementWord *word) const {
  if (!_decides_reads) return false;
  *word = ElementWord();
  *stored = _writes == NULL ? NULL
      : _writes->stored(_ordinal, position, word);
  return true;
}

void ContainerExpression::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ContainerRelation");
  writer.Key("shape");
  writer.String(_shape.c_str());
  writer.Key("operation");
  writer.String(_operation.c_str());
  writer.Key("_java_type");
  writer.String(_java_type.c_str());
  writer.Key("receiver");
  if (_receiver == NULL) {
    writer.Null();
  } else {
    _receiver->serialize(writer);
  }
  writer.Key("arguments");
  writer.StartArray();
  for (size_t index = 0; index < _arguments.size(); ++index) {
    if (_arguments[index] == NULL) {
      writer.Null();
    } else {
      _arguments[index]->serialize(writer);
    }
  }
  writer.EndArray();
  // Only a conditional mutation carries a guard.  Omitting the key entirely
  // for an unconditional one keeps every existing op's JSON byte-identical.
  if (_guard != NULL) {
    writer.Key("guard");
    _guard->serialize(writer);
  }
  if (_owner != NULL) {
    writer.Key("owner");
    _owner->serialize(writer);
  }
  if (!_order.empty()) {
    writer.Key("order");
    writer.String(_order.c_str());
  }
  if (_members >= 0) {
    writer.Key("members");
    writer.Int(_members);
  }
  if (_answer != 0) {
    _returned.serialize(writer);
    writer.Key("answer");
    writer.Int64(_answer);
  }
}

#endif  // ENABLE_CONCOLIC
