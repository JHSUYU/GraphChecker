#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/typeCastExpression.hpp"
#include "concolic/methodSymbolizer.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicMap.hpp"
#include "concolic/reference/symbolicStream.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/utils.hpp"
#include "runtime/jniHandles.hpp"

#include <string.h>

namespace {

const char *const PIPELINE = "java/util/stream/ReferencePipeline";
const char *const HEAD = "java/util/stream/ReferencePipeline$Head";
const char *const ABSTRACT_PIPELINE = "java/util/stream/AbstractPipeline";
const char *const COLLECTORS = "java/util/stream/Collectors";
// The one Collection whose own stream() is no Collection.stream(): it
// wraps its map's entry set.
const char *const UNMODIFIABLE_ENTRY_SET =
    "java/util/Collections$UnmodifiableMap$UnmodifiableEntrySet";

enum StageKind { FILTER, MAP, LIMIT, SORTED, DISTINCT, TEST, ACTION };

// The terminal a pipeline ends in.  TEST is a match's predicate, ACTION
// forEach's action: the last stage of their pipelines.
enum Terminal {
  NO_TERMINAL, TO_LIST, TO_SET, TO_ARRAY, COUNT, ANY_MATCH, ALL_MATCH,
  NONE_MATCH, FIND, FOR_EACH
};

enum CollectorKind { COLLECTOR_TO_LIST = 1, COLLECTOR_TO_SET = 2 };

bool named(const std::string &value, const char *name) {
  return value == name;
}

bool one_of(const std::string &method, const char *const *names) {
  for (; *names != NULL; ++names) {
    if (method == *names) return true;
  }
  return false;
}

// The intermediate calls a pipeline keeps as stages.
const char *const STAGES[] = {
  "filter", "map", "limit", "sorted", "distinct", "unordered", NULL
};
// The terminal calls a pipeline is stated by.
const char *const TERMINALS[] = {
  "collect", "toArray", "count", "anyMatch", "allMatch", "noneMatch",
  "findFirst", "findAny", "forEach", "forEachOrdered", NULL
};
// Everything else on a pipeline that would consume it, or change how it
// runs, ends its recording.
const char *const UNMODELED[] = {
  "skip", "peek", "flatMap", "flatMapToInt", "flatMapToLong",
  "flatMapToDouble", "mapToInt", "mapToLong", "mapToDouble", "iterator",
  "spliterator", "parallel", "reduce", "min", "max", NULL
};

Expression *conjunction(Expression *left, Expression *right) {
  if (left == NULL) return right;
  if (right == NULL) return left;
  return new OpSymExpression(left, right, op_land, true);
}

Expression *negation(Expression *condition) {
  Expression *flipped = condition->logical_negation();
  return flipped != NULL ? flipped
      : static_cast<Expression *>(new OpSymExpression(
            condition, new ConExpression((jboolean) false), op_eq, true));
}

Expression *relation(const char *shape, const char *operation,
                     Expression *receiver, const exp_list_t &arguments,
                     BasicType type = T_OBJECT, Expression *guard = NULL,
                     Expression *owner = NULL,
                     const std::string &java_type = std::string()) {
  return new ContainerExpression(shape, operation, receiver, arguments, type,
                                 java_type, guard, owner);
}

Expression *query(const char *shape, const char *operation,
                  Expression *receiver, BasicType type,
                  Expression *owner = NULL) {
  exp_list_t none;
  return relation(shape, operation, receiver, none, type, NULL, owner);
}

// The exact empty container a chain begins at: of `root`, the state of the
// object the chain is installed on, or of none for a chain no object holds
// (a count's, a match's).
ContainerExpression *empty_base(const char *shape, Expression *root) {
  exp_list_t none;
  return new ContainerExpression(shape, "SNAPSHOT_BASE", root, none);
}

// One more member under `guard` (NULL: always).
Expression *appended(Expression *chain, Expression *value, Expression *guard) {
  exp_list_t member;
  member.push_back(value);
  return relation("INDEXED", guard == NULL ? "APPEND" : "APPEND_IF", chain,
                  member, T_OBJECT, guard);
}

Expression *mark() { return new ConExpression((jboolean) true); }

// A chain of `count` unguarded members.
Expression *counted(int count) {
  Expression *chain = empty_base("INDEXED", NULL);
  for (int index = 0; index < count; ++index) {
    chain = appended(chain, mark(), NULL);
  }
  return chain;
}

struct Stage {
  StageKind kind;
  // The functional object called back (FILTER, MAP, TEST, ACTION, SORTED
  // with a comparator), by session id.
  sym_rid_t function;
  // LIMIT's maxSize when symbolic, and its value.
  Expression *bound;
  jlong concrete_bound;
  // The terminal's run of a LIMIT: how many elements the run let through,
  // and every world's arrivals past it as a chain, NULL while each passed
  // concretely.
  int passed;
  Expression *arrivals;

  explicit Stage(StageKind stage_kind)
      : kind(stage_kind), function(NULL_SYM_RID), bound(NULL),
        concrete_bound(0), passed(0), arrivals(NULL) {}
  bool calls_back() const {
    return kind == FILTER || kind == MAP || kind == TEST || kind == ACTION;
  }
  bool barrier() const { return kind == SORTED || kind == DISTINCT; }
  Expression *bound_expression() const {
    return bound != NULL ? bound
        : static_cast<Expression *>(new ConExpression(concrete_bound));
  }
  // How many elements are past this LIMIT in every world, so far.
  Expression *position() const {
    return arrivals == NULL
        ? static_cast<Expression *>(new ConExpression((jint) passed))
        : query("INDEXED", "SIZE", arrivals, T_INT);
  }
};

// An element on its way: the next stage it meets, what it is, where a
// stateful source holds it (`existence`, NULL: always), the conjunction of
// the decisions that let it this far (NULL: true), and whether the run
// pushed it (an element a symbolic filter dropped goes on unseen, in the
// worlds where that filter answers true).
struct Element {
  size_t stage;
  Expression *value;
  bool symbolic_value;
  Expression *existence;
  Expression *guard;
  bool in_run;
  Element()
      : stage(0), value(NULL), symbolic_value(false), existence(NULL),
        guard(NULL), in_run(true) {}
  // Where it is there at all: its existence and its decisions.
  Expression *whole() const { return conjunction(existence, guard); }
};

// One member of the stated result: its value and the condition it is
// there under.
struct Output {
  Expression *value;
  Expression *guard;
  bool in_run;
  Output(Expression *output_value, Expression *output_guard, bool run)
      : value(output_value), guard(output_guard), in_run(run) {}
};

const size_t NO_PENDING = (size_t) -1;
// A callback no stage makes (toArray's array generator).
const size_t IGNORED = (size_t) -2;

}  // namespace

class StreamPipeline {
public:
  StreamPipeline(SymMap::ViewKind view, const char *shape, Expression *owner,
                 jobject source, bool stateful)
      : _view(view), _shape(shape), _owner(owner), _source(source),
        _stateful(stateful), _state(NULL), _members(-1),
        _staged(FILTER), _has_staged(false),
        _terminal(NO_TERMINAL), _pending(NO_PENDING), _pending_argument(0),
        _live(false), _pulled(0), _symbolic(false), _pinned(NULL),
        _barrier_met(false), _seen_callback(false), _stopped(false),
        _over_bound(false), _deciding(NULL), _guarded_action(false) {}

  ~StreamPipeline() {
    if (_source != NULL) JNIHandles::destroy_weak_global(_source);
  }

  // ---- recording ----------------------------------------------------------

  // Something symbolic is in the pipeline before it runs: the source's
  // state or a LIMIT's bound.
  bool carries_symbolic() const {
    if (_stateful || _state != NULL) return true;
    for (size_t index = 0; index < _stages.size(); ++index) {
      if (_stages[index].bound != NULL) return true;
    }
    return false;
  }

  // The intermediate call's stage, kept until the call returns.
  void keep(const Stage &kept) {
    _staged = kept;
    _has_staged = true;
  }

  // The intermediate call's stage, once the call returned its stream.
  void commit() {
    if (_has_staged) _stages.push_back(_staged);
    _has_staged = false;
  }

  void cancel() { _has_staged = false; }

  // ---- the terminal's run -------------------------------------------------

  void begin(Terminal terminal, MethodSymbolizerHandle &handle) {
    _terminal = terminal;
    if (terminal == ANY_MATCH || terminal == ALL_MATCH
        || terminal == NONE_MATCH || terminal == FOR_EACH) {
      Stage last(terminal == FOR_EACH ? ACTION : TEST);
      last.function = ConcolicMngr::ctx->name_reference(
          handle.get_param<oop>(1));
      _stages.push_back(last);
    }
    for (size_t index = 0; index < _stages.size(); ++index) {
      if (_stages[index].function != NULL_SYM_RID) {
        handle.add_functional(_stages[index].function);
      }
    }
    bind(handle);
    _symbolic = carries_symbolic();
  }

  /**
   * A callback of `receiver` is entering with `argument`: places it, and
   * answers the seed of its parameter.
   */
  Expression *enter(sym_rid_t receiver, oop argument) {
    _pending = IGNORED;
    _pending_argument = (uintptr_t) argument;
    if (_pinned != NULL) return NULL;
    // The stage the element in flight waits at, when it calls this object;
    // else the first that does (one object may serve two stages).
    const size_t called = _live && _current.stage < _stages.size()
            && _stages[_current.stage].function == receiver
        ? _current.stage : stage_of(receiver);
    if (called == NO_PENDING) return NULL;
    _seen_callback = true;
    if (_stages[called].kind == SORTED) {
      // A comparator: no element of its own.
      _pending = called;
      return NULL;
    }
    if (!_live) start(called, argument);
    if (!_live || _current.stage != called) {
      // The callbacks are not the order this reconstruction expects.
      pin_all("PROGRESS");
      return NULL;
    }
    _pending = called;
    return seed(argument);
  }

  /**
   * The callback placed last returns `result` (an object result is
   * `returned`); `argument` is the object its frame holds as its first
   * argument now, the one it entered with when it is still that object.
   */
  void leave(const CallbackResult &result, oop returned, oop argument) {
    if (result.threw) return;
    fold(result, returned,
         (uintptr_t) argument == _pending_argument ? argument : (oop) NULL);
  }

  Expression *finish(MethodSymbolizerHandle &handle);

  // Whether a terminal unwinding now leaves something symbolic unstated.
  bool unwinds() const { return _symbolic; }

private:
  // The first stage that calls `receiver` back, or NO_PENDING.
  size_t stage_of(sym_rid_t receiver) const {
    if (receiver == NULL_SYM_RID) return NO_PENDING;
    for (size_t index = 0; index < _stages.size(); ++index) {
      if (_stages[index].function == receiver) return index;
    }
    return NO_PENDING;
  }

  bool callback_stage() const {
    for (size_t index = 0; index < _stages.size(); ++index) {
      if (_stages[index].calls_back()) return true;
    }
    return false;
  }

  // The barrier (sorted, distinct) nearest before stage `index`, or
  // NO_PENDING.
  size_t barrier_before(size_t index) const {
    for (size_t at = index; at > 0; --at) {
      if (_stages[at - 1].barrier()) return at - 1;
    }
    return NO_PENDING;
  }

  // The source's member at position `pull`, as `member` is: READ of a
  // list's state at it, a map view's entry or key (SymMap::
  // visited_member, whose key also bounds where it is), or what the
  // member carries itself.
  Expression *source_member(int pull, oop member, Expression **existence) {
    *existence = NULL;
    if (_state == NULL) return ContainerSupport::semantic_value(member);
    if (_view == SymMap::VIEW_VALUES) {
      // The key the map's iteration holds this value under (bind).
      if (pull >= (int) _value_keys.size()) {
        pin_all("PROGRESS");
        return NULL;
      }
      exp_list_t key;
      key.push_back(_value_keys[pull]);
      *existence = relation("ASSOCIATIVE", "CONTAINS", _state, key,
                            T_BOOLEAN, NULL, _owner);
      return relation("ASSOCIATIVE", "READ", _state, key,
                      ContainerSupport::result_type(member, T_OBJECT), NULL,
                      _owner, ContainerSupport::java_type(member, T_OBJECT));
    }
    if (_view == SymMap::VIEW_NONE) {
      exp_list_t at;
      at.push_back(new ConExpression((jint) pull));
      return relation("INDEXED", "READ", _state, at,
                      ContainerSupport::result_type(member, T_OBJECT), NULL,
                      _owner, ContainerSupport::java_type(member, T_OBJECT));
    }
    Expression *key = NULL;
    Expression *seed = SymMap::visited_member(_view, _state, _owner, member,
                                              &key);
    if (key != NULL) {
      exp_list_t wanted;
      wanted.push_back(key);
      *existence = relation("ASSOCIATIVE", "CONTAINS", _state, wanted,
                            T_BOOLEAN, NULL, _owner);
    }
    return seed;
  }

  // A new element, for the callback of stage `called`: the source's next
  // member, or -- past a barrier, whose output order this model does not
  // follow -- an element of the run's own values entering after it.
  void start(size_t called, oop member) {
    const size_t barrier = barrier_before(called);
    if (barrier == NO_PENDING) {
      pull(member);
      return;
    }
    // Members went into the barrier unseen: what entered it is symbolic
    // when the source's state or a bound ahead of it is, or the member
    // carries its own value.
    _barrier_met = true;
    bool bound_ahead = false;
    for (size_t index = 0; index < barrier; ++index) {
      bound_ahead = bound_ahead || _stages[index].bound != NULL;
    }
    if (_state != NULL || bound_ahead
        || ContainerSupport::semantic_value(member) != NULL) {
      pin_all(_stages[barrier].kind == SORTED ? "SORTED" : "DISTINCT");
      return;
    }
    _current = Element();
    _current.stage = barrier + 1;
    _live = true;
    advance();
  }

  // The source's next member, as `member` is.
  void pull(oop member) {
    _current = Element();
    _current.value = source_member(_pulled, member, &_current.existence);
    _current.symbolic_value = _current.value != NULL;
    if (_current.value != NULL) _symbolic = true;
    if (_current.existence != NULL) _present.push_back(_current.existence);
    ++_pulled;
    _live = _pinned == NULL;
    advance();
  }

  // The seed of the element's callback: what it is, when that is an
  // expression -- its own, or one its object carries.
  Expression *seed(oop argument) {
    if (_current.symbolic_value) return _current.value;
    Expression *own = argument == NULL ? NULL
        : ContainerSupport::semantic_value(argument);
    if (own != NULL) {
      _current.value = own;
      _current.symbolic_value = true;
      _symbolic = true;
    }
    return own;
  }

  // An element of the run's own value, named when a statement needs it:
  // what a set collects, or a member a symbolic filter dropped.  Never on
  // the way: a pipeline that stays concrete names nothing.
  void name_value(oop object) {
    if (_current.value == NULL && object != NULL) {
      _current.value = ContainerSupport::concrete_value(object);
    }
  }

  void fold(const CallbackResult &result, oop returned, oop argument) {
    const size_t at = _pending;
    _pending = NO_PENDING;
    if (at == NO_PENDING || at == IGNORED || _pinned != NULL) return;
    const Stage &called = _stages[at];
    if (called.kind == SORTED) {
      // A comparator's answer orders what a barrier holds, which no
      // relation states.
      if (result.symbolic || result.path != NULL) pin_all("SORTED");
      return;
    }
    if (called.kind == ACTION) {
      // The action ran, its effects hooked; under a symbolic decision it
      // would not have run in every world.  (Where the source holds the
      // element is no decision: the element is there or not.)
      if (_current.guard != NULL) _guarded_action = true;
      _live = false;
      return;
    }
    // What a callback's path decided besides its answer is in no relation:
    // a mapped value its path chose is the run's, and an answer's own
    // expression holds on its path.  Named, not pinned: the path holds the
    // models' concrete-answer conditions too, and pinning those would hold
    // every read inside the callback to the run's answer.
    if (result.path != NULL && (called.kind == MAP || result.symbolic)) {
      _pin_reasons.push_back(called.kind == MAP ? "MAP_PATH"
                                                : "CALLBACK_PATH");
    }
    if (called.kind == MAP) {
      Expression *own = result.symbolic ? result.result
          : ContainerSupport::semantic_value(returned);
      _current.value = own;
      _current.symbolic_value = own != NULL;
      if (own != NULL) _symbolic = true;
      // A list's members are named from the list it collected
      // (fill_values); a set's have no position to be read back by.
      if (_terminal == TO_SET) name_value(returned);
      ++_current.stage;
      advance();
      return;
    }
    if (result.undecided()) {
      // A false answer whose path has no complement: not stated.
      pin_all("UNNEGATABLE");
      return;
    }
    const bool held = (result.returned_int & 1) != 0;
    Expression *truth = result.truth();
    if (truth != NULL) _symbolic = true;
    if (called.kind == TEST) {
      answer(held, truth);
      _live = false;
      return;
    }
    if (held) {
      if (_terminal == TO_SET) name_value(argument);
      _current.guard = conjunction(_current.guard, truth);
      ++_current.stage;
      advance();
    } else {
      drop(truth, argument);
    }
  }

  // A filter answered false.  A symbolic answer lets the element on in the
  // worlds that flip it, as far as relations can follow it: through LIMITs
  // to the terminal.  Before anything that calls back or holds a barrier,
  // what it would have been is unknown, so the drop is pinned.
  void drop(Expression *truth, oop argument) {
    if (truth == NULL) {
      _live = false;
      return;
    }
    Expression *alive = conjunction(_current.guard, truth);
    Expression *there = conjunction(_current.existence, alive);
    bool stated = true;
    for (size_t later = _current.stage + 1; later < _stages.size(); ++later) {
      stated = stated && !_stages[later].calls_back()
          && !_stages[later].barrier();
    }
    if (stated) name_value(argument);
    if (!stated || _current.value == NULL) {
      // What it would have been past here is unknown (or, its frame no
      // longer holding the object it was called with, what it was).
      pin(negation(there), "DROPPED");
      _live = false;
      return;
    }
    _current.guard = alive;
    _current.in_run = false;
    ++_current.stage;
    advance();
  }

  // Moves the element through the stages that call nothing back, to the
  // next one that does, a barrier, or the terminal.
  void advance() {
    while (_live && _current.stage < _stages.size()) {
      Stage &next = _stages[_current.stage];
      if (next.calls_back()) {
        // An element no run pushed never meets one (drop() pinned it).
        if (!_current.in_run) _live = false;
        return;
      }
      if (next.barrier()) {
        if (_current.whole() != NULL || _current.symbolic_value) {
          pin_all(next.kind == SORTED ? "SORTED" : "DISTINCT");
        }
        _barrier_met = true;
        _live = false;
        return;
      }
      limit(next);
      ++_current.stage;
    }
    if (_live) {
      arrive();
      _live = false;
    }
  }

  // A LIMIT lets an element through while fewer than maxSize went before
  // it.  The run pulls no element past an exhausted one.
  void limit(Stage &cap) {
    const int before = cap.passed;
    // Where this element stands among the arrivals, in every world: built
    // only where some world differs from the run.
    Expression *position = cap.bound != NULL || cap.arrivals != NULL
        ? cap.position() : NULL;
    if (_current.in_run) {
      if ((jlong) before >= cap.concrete_bound) {
        pin_all("PROGRESS");
        return;
      }
      ++cap.passed;
    }
    if (position != NULL) {
      _current.guard = conjunction(_current.guard, new OpSymExpression(
          position, cap.bound_expression(), op_lt, true));
    }
    Expression *arrived = _current.whole();
    if (cap.arrivals != NULL || arrived != NULL) {
      if (before >= ConcolicMngr::initialSnapshotMaxEntries()) {
        // Past the bound no position is stated (as no member is).
        pin_all("OVER_BOUND");
        return;
      }
      cap.arrivals = appended(
          cap.arrivals != NULL ? cap.arrivals : counted(before), mark(),
          arrived);
    }
  }

  void arrive() {
    output(Output(_current.value, _current.whole(), _current.in_run));
    if (_terminal == FIND && _current.in_run) _stopped = true;
  }

  // One member of the result, up to the snapshot bound: past it no
  // statement is made (finish), so none is kept.
  void output(const Output &member) {
    if (_outputs.size() < (size_t) ConcolicMngr::initialSnapshotMaxEntries()) {
      _outputs.push_back(member);
    } else {
      _over_bound = true;
    }
  }

  // A match's predicate answered for an element: the element matches (or,
  // for allMatch, misses) where its guard and the answer hold.  The answer
  // that ends the stream decides it; what came after was never pulled.
  void answer(bool held, Expression *truth) {
    const bool all = _terminal == ALL_MATCH;
    const bool counts = all ? !held : held;
    Expression *condition = truth == NULL ? NULL
        : all ? negation(truth) : truth;
    if (condition != NULL || counts) {
      Expression *guard = conjunction(_current.whole(), condition);
      // A match's chain holds marks, made when it is stated.
      output(Output(NULL, guard, counts));
      if (counts) {
        _stopped = true;
        _deciding = guard;
      }
    }
  }

  // A condition the stated result holds under, in the run's polarity,
  // named by why (NULL: a precondition of the call itself).
  void pin(Expression *condition, const char *reason) {
    if (condition == NULL) return;
    _pins.push_back(condition);
    if (reason != NULL) _pin_reasons.push_back(reason);
  }

  void bind(MethodSymbolizerHandle &handle);
  void name_reasons() const {
    for (size_t index = 0; index < _pin_reasons.size(); ++index) {
      name(_pin_reasons[index].c_str());
    }
  }

  // The result is the run's own: nothing more is followed.
  void pin_all(const char *reason) {
    if (_pinned == NULL) _pinned = reason;
    _live = false;
  }

  void reconstruct(MethodSymbolizerHandle &handle, oop result);
  bool fill_values(oop result);
  void name(const char *reason) const {
    ConcolicMngr::ctx->note_model_gap(std::string("STREAM_PINNED:") + reason);
  }
  Expression *with_pins(const char *shape, Expression *chain) const {
    for (size_t index = 0; index < _pins.size(); ++index) {
      exp_list_t none;
      chain = relation(shape, "PIN", chain, none, T_OBJECT, _pins[index]);
    }
    return chain;
  }
  // The outputs as an INDEXED chain on `base`: their values, or -- a
  // count's, a match's -- one mark each.
  Expression *indexed_chain(Expression *base, bool values) const {
    Expression *chain = base;
    for (size_t index = 0; index < _outputs.size(); ++index) {
      chain = appended(chain, values ? _outputs[index].value : mark(),
                       _outputs[index].guard);
    }
    return with_pins("INDEXED", chain);
  }

  // The source, as stream() named it.
  SymMap::ViewKind _view;  // VIEW_NONE: a list's or a deque's positions
  const char *_shape;
  Expression *_owner;
  // A weak global handle of the source container, which this pipeline
  // owns; and whether the container carried state at stream().
  jobject _source;
  bool _stateful;
  // The source as the terminal bound it (streams bind late): its state,
  // its member count, and a values view's keys in the order it iterates.
  Expression *_state;
  int _members;
  std::vector<Expression *> _value_keys;
  std::vector<Stage> _stages;
  Stage _staged;
  bool _has_staged;
  // The terminal's run.
  Terminal _terminal;
  size_t _pending;
  // The address of the object the pending callback entered with: compared,
  // never dereferenced.
  uintptr_t _pending_argument;
  Element _current;
  bool _live;
  int _pulled;
  bool _symbolic;
  const char *_pinned;
  bool _barrier_met;
  bool _seen_callback;
  bool _stopped;
  bool _over_bound;
  Expression *_deciding;
  bool _guarded_action;
  std::vector<Output> _outputs;
  // Where a stateful source holds each member pulled.
  std::vector<Expression *> _present;
  std::vector<Expression *> _pins;
  std::vector<std::string> _pin_reasons;
  // The application method the body ran unhooked, or empty.
  std::string _muted;
};

// A pipeline no stage of which calls back: its elements are the result's
// members, in the order the source gave them (a list, an array), or are
// counted (count).
void StreamPipeline::reconstruct(MethodSymbolizerHandle &handle, oop result) {
  std::vector<oop> keys;
  std::vector<oop> members;
  int count = 0;
  if (_terminal == TO_LIST || _terminal == TO_ARRAY) {
    const char *unreadable = NULL;
    bool over_bound = false;
    if (!ContainerSupport::read_concrete_members(result, &keys, &members,
                                                 &unreadable, &over_bound)
        || over_bound) {
      pin_all("OVER_BOUND");
      return;
    }
    count = (int) members.size();
  } else if (_terminal == COUNT && (_state == NULL
                                    || _view == SymMap::VIEW_NONE)) {
    const jlong counted = handle.get_result<jlong>(T_LONG);
    if (counted > (jlong) ConcolicMngr::initialSnapshotMaxEntries()) {
      pin_all("OVER_BOUND");
      return;
    }
    count = (int) counted;
  } else {
    pin_all("UNSTATED_MEMBERS");
    return;
  }
  for (int index = 0; index < count && _pinned == NULL; ++index) {
    pull(index < (int) members.size() ? members[index] : (oop) NULL);
  }
}

// Streams bind late: the source's state, member count and (a values view
// of a stateful map) iteration keys are read when the terminal runs, and
// the source is the call's for MethodSymbolizer::reenters.
void StreamPipeline::bind(MethodSymbolizerHandle &handle) {
  oop container = _source == NULL ? (oop) NULL : JNIHandles::resolve(_source);
  if (container == NULL) return;
  handle.set_source(_source);
  _members = ContainerSupport::member_count(container);
  _state = ContainerSupport::observed_state(container);
  if (_view != SymMap::VIEW_VALUES || _state == NULL) return;
  std::vector<oop> keys;
  std::vector<oop> values;
  const char *unreadable = NULL;
  bool over_bound = false;
  if (!ContainerSupport::read_concrete_members(container, &keys, &values,
                                               &unreadable, &over_bound)
      || over_bound || keys.size() != values.size()) {
    // The values of a stateful map no walk names a key for.
    _state = NULL;
    _pin_reasons.push_back("VALUES");
    _symbolic = true;
    return;
  }
  for (size_t index = 0; index < keys.size(); ++index) {
    Expression *key = NULL;
    SymMap::visited_member(SymMap::VIEW_KEYS, NULL, NULL, keys[index], &key);
    _value_keys.push_back(key);
  }
}

// The values of the members the run collected that no callback named:
// the result's own, in order.
bool StreamPipeline::fill_values(oop result) {
  std::vector<oop> keys;
  std::vector<oop> members;
  const char *unreadable = NULL;
  bool over_bound = false;
  if (!ContainerSupport::read_concrete_members(result, &keys, &members,
                                               &unreadable, &over_bound)
      || over_bound) {
    return false;
  }
  size_t next = 0;
  for (size_t index = 0; index < _outputs.size(); ++index) {
    if (!_outputs[index].in_run) continue;
    if (next >= members.size()) return false;
    oop member = members[next++];
    if (_outputs[index].value == NULL) {
      Expression *own = ContainerSupport::semantic_value(member);
      _outputs[index].value = own != NULL ? own
          : ContainerSupport::concrete_value(member);
    }
  }
  return next == members.size();
}

Expression *StreamPipeline::finish(MethodSymbolizerHandle &handle) {
  if (_live) {
    // An element still waiting for a callback the body never made.
    if (_current.stage < _stages.size()
        && _stages[_current.stage].calls_back()) {
      pin_all("PROGRESS");
    } else {
      advance();
    }
  }
  if (handle.callback_refusal() != NULL) pin_all("CALLBACK_DEPTH");
  // A callback changed the source it ran over: no chain orders the two.
  if (handle.reentered()) pin_all("CALLBACK_MUTATES_SOURCE");
  // Application code the body ran unhooked (an element's compareTo, equals
  // or hashCode, a list's own get): a natural order it decided is unstated.
  _muted = handle.take_muted_application();
  if (!_muted.empty()) {
    for (size_t index = 0; index < _stages.size(); ++index) {
      if (_stages[index].kind == SORTED
          && _stages[index].function == NULL_SYM_RID) {
        pin_all("SORTED");
      }
    }
  }
  const BasicType type = handle.get_result_type();
  oop result = type == T_OBJECT || type == T_ARRAY
      ? handle.get_result<oop>(type) : (oop) NULL;
  if (_pinned == NULL && !_seen_callback && !callback_stage()) {
    reconstruct(handle, result);
  }
  // Members past a barrier no callback follows reach the terminal in an
  // order this model does not state.
  if (_barrier_met) {
    size_t last_barrier = 0;
    bool followed = false;
    for (size_t index = 0; index < _stages.size(); ++index) {
      if (_stages[index].barrier()) {
        last_barrier = index;
        followed = false;
      } else if (_stages[index].calls_back()) {
        followed = true;
      }
    }
    if (!followed && _symbolic) {
      pin_all(_stages[last_barrier].kind == SORTED ? "SORTED" : "DISTINCT");
    }
  }
  if (!_symbolic) return NULL;
  if (_over_bound) pin_all("OVER_BOUND");
  if (_pinned == NULL
      && (_terminal == TO_LIST || _terminal == TO_ARRAY)
      && !fill_values(result)) {
    pin_all("PROGRESS");
  }
  // What the run never pulled.
  bool exhausted = false;
  for (size_t index = 0; index < _stages.size(); ++index) {
    exhausted = exhausted || (_stages[index].kind == LIMIT
        && (jlong) _stages[index].passed >= _stages[index].concrete_bound);
  }
  const bool cut = (exhausted || _stopped)
      && (_members < 0 || _pulled < _members);
  for (size_t index = 0; cut && index < _stages.size(); ++index) {
    const Stage &cap = _stages[index];
    if (cap.kind == LIMIT && (jlong) cap.passed >= cap.concrete_bound
        && (cap.bound != NULL || cap.arrivals != NULL)) {
      pin(new OpSymExpression(cap.position(), cap.bound_expression(),
                              op_ge, true), "LIMIT_EXHAUSTED");
    }
  }
  if (cut && _stopped) pin(_deciding, "SHORT_CIRCUIT");
  if (!cut && _state != NULL && !_barrier_met) {
    // The source held exactly what the stream pulled: as many members as
    // pulled positions, or -- keyed -- as pulled keys it holds.
    Expression *held = new ConExpression((jint) _pulled);
    if (!_present.empty()) {
      Expression *present = empty_base("INDEXED", NULL);
      for (size_t index = 0; index < _present.size(); ++index) {
        present = appended(present, mark(), _present[index]);
      }
      held = query("INDEXED", "SIZE", present, T_INT);
    }
    pin(new OpSymExpression(query(_shape, "SIZE", _state, T_INT, _owner),
                            held, op_eq, true),
        "SOURCE_END");
  }
  for (size_t index = 0; index < _stages.size(); ++index) {
    if (_stages[index].bound != NULL) {
      // limit() throws for a negative maxSize.
      pin(new OpSymExpression(_stages[index].bound,
                              new ConExpression((jlong) 0), op_ge, true),
          NULL);
    }
  }
  if (!_muted.empty()) name(("MUTED_APPLICATION:" + _muted).c_str());
  if (_terminal == FIND) pin_all("FIND");
  if (_terminal == FOR_EACH) {
    // No chain holds what was pinned: each is named.
    if (_guarded_action) name("FOR_EACH");
    if (_pinned != NULL) name(_pinned);
    name_reasons();
    return NULL;
  }
  if (_pinned != NULL) {
    name(_pinned);
    return NULL;
  }
  name_reasons();
  switch (_terminal) {
    case TO_LIST:
    case TO_ARRAY: {
      if (result == NULL) return NULL;
      ContainerExpression *base = empty_base("INDEXED",
          ConcolicMngr::ctx->container_state(result, "INDEXED"));
      Expression *chain = indexed_chain(base, true);
      if (_terminal == TO_ARRAY) {
        // An array is no location: its loads read this state (as
        // SymList's toArray).
        ConcolicMngr::ctx->set_container_state(result, chain);
        return ContainerSupport::concrete_value(result);
      }
      ContainerSupport::publish_filled(result, base, chain, "COLLECT");
      return NULL;
    }
    case TO_SET: {
      if (result == NULL) return NULL;
      Expression *root =
          ConcolicMngr::ctx->container_state(result, "ASSOCIATIVE");
      ContainerExpression *base = empty_base("ASSOCIATIVE", root);
      base->state_members(ContainerSupport::iteration_order(result), 0);
      Expression *chain = base;
      for (size_t index = 0; index < _outputs.size(); ++index) {
        // A hash set's member maps to true (SymSet's add).
        exp_list_t put;
        put.push_back(_outputs[index].value);
        put.push_back(mark());
        chain = relation("ASSOCIATIVE",
                         _outputs[index].guard == NULL ? "PUT" : "PUT_IF",
                         chain, put, T_OBJECT, _outputs[index].guard);
      }
      ContainerSupport::publish_filled(result, base,
                                       with_pins("ASSOCIATIVE", chain),
                                       "COLLECT");
      return NULL;
    }
    case COUNT:
      return new TypeCastExpression(query("INDEXED", "SIZE",
          indexed_chain(empty_base("INDEXED", NULL), false), T_INT),
          "I", "J");
    case ANY_MATCH:
      return new OpSymExpression(query("INDEXED", "IS_EMPTY",
          indexed_chain(empty_base("INDEXED", NULL), false), T_BOOLEAN),
          new ConExpression((jboolean) false), op_eq, true);
    case ALL_MATCH:
    case NONE_MATCH:
      return query("INDEXED", "IS_EMPTY",
          indexed_chain(empty_base("INDEXED", NULL), false), T_BOOLEAN);
    default:
      return NULL;
  }
}

// ---------------------------------------------------------------------------
// StreamTable
// ---------------------------------------------------------------------------

StreamTable::~StreamTable() {
  for (std::map<sym_rid_t, StreamPipeline *>::iterator pipeline =
           _pipelines.begin();
       pipeline != _pipelines.end(); ++pipeline) {
    delete pipeline->second;
  }
}

StreamPipeline *StreamTable::find(sym_rid_t stream) const {
  if (stream == NULL_SYM_RID) return NULL;
  std::map<sym_rid_t, StreamPipeline *>::const_iterator found =
      _pipelines.find(stream);
  return found == _pipelines.end() ? NULL : found->second;
}

void StreamTable::put(sym_rid_t stream, StreamPipeline *pipeline) {
  StreamPipeline *&held = _pipelines[stream];
  if (held != NULL && held != pipeline) delete held;
  held = pipeline;
}

StreamPipeline *StreamTable::take(sym_rid_t stream) {
  std::map<sym_rid_t, StreamPipeline *>::iterator found =
      _pipelines.find(stream);
  if (found == _pipelines.end()) return NULL;
  StreamPipeline *pipeline = found->second;
  _pipelines.erase(found);
  return pipeline;
}

void StreamTable::name_collector(sym_rid_t accumulator, int kind) {
  if (accumulator != NULL_SYM_RID) _collectors[accumulator] = kind;
}

int StreamTable::collector(sym_rid_t accumulator) const {
  std::map<sym_rid_t, int>::const_iterator found =
      _collectors.find(accumulator);
  return found == _collectors.end() ? 0 : found->second;
}

// ---------------------------------------------------------------------------
// SymStream
// ---------------------------------------------------------------------------

namespace {

StreamPipeline *recorded(oop stream) {
  StreamTable *table = ConcolicMngr::ctx->streams(false);
  return table == NULL || stream == NULL ? NULL
      : table->find(stream->get_sym_rid());
}

// Ends a pipeline's recording on a call the model does not follow; the
// rest runs as bytecode.  Named when something symbolic was already in it.
void stop_recording(oop stream, const char *prefix,
                    const std::string &operation) {
  StreamPipeline *pipeline =
      ConcolicMngr::ctx->streams(false)->take(stream->get_sym_rid());
  if (pipeline == NULL) return;
  if (pipeline->carries_symbolic()) {
    ConcolicMngr::ctx->note_model_gap(std::string(prefix) + operation);
  }
  delete pipeline;
}

// A collector's accumulator.  Collectors.toList()/toSet() make a new
// collector per call around the one accumulator their non-capturing method
// reference (List::add, Set::add) always yields, so the accumulator names
// the kind: one entry per kind, and a collector kept in a field is known
// at every use.
oop accumulator_of(oop collector) {
  return collector == NULL ? (oop) NULL
      : OopUtils::obj_field_by_name(collector, "accumulator",
                                    "Ljava/util/function/BiConsumer;");
}

Terminal terminal_of(MethodSymbolizerHandle &handle) {
  const std::string &method = handle.get_callee_name();
  if (method == "count") return COUNT;
  if (method == "anyMatch") return ANY_MATCH;
  if (method == "allMatch") return ALL_MATCH;
  if (method == "noneMatch") return NONE_MATCH;
  if (method == "findFirst" || method == "findAny") return FIND;
  if (method == "forEach" || method == "forEachOrdered") return FOR_EACH;
  if (method == "toArray") return TO_ARRAY;
  if (method == "collect" && handle.get_callee_method()->size_of_parameters()
                                 == 2) {
    oop accumulator = accumulator_of(handle.get_param<oop>(1));
    const int kind = accumulator == NULL ? 0
        : ConcolicMngr::ctx->streams(true)->collector(
              accumulator->get_sym_rid());
    if (kind == COLLECTOR_TO_LIST) return TO_LIST;
    if (kind == COLLECTOR_TO_SET) return TO_SET;
  }
  return NO_TERMINAL;
}

}  // namespace

void SymStream::init_register_class(MethodSymbolizer *m_symbolizer) {
  static const char *const CLASSES[] = {
    PIPELINE, HEAD, ABSTRACT_PIPELINE, COLLECTORS, UNMODIFIABLE_ENTRY_SET,
    NULL
  };
  m_symbolizer->register_model(CLASSES, invoke_method_helper,
                               finish_method_helper);
}

bool SymStream::invoke_source(MethodSymbolizerHandle &handle) {
  // A parallel stream calls its stages back on other threads.
  if (handle.get_callee_name() != "stream") return false;
  return ContainerSupport::backing_container(handle.get_param<oop>(0))
      != NULL;
}

Expression *SymStream::finish_source(MethodSymbolizerHandle &handle) {
  oop source = handle.get_param<oop>(0);
  oop stream = handle.get_result<oop>(T_OBJECT);
  oop container = ContainerSupport::backing_container(source);
  if (stream == NULL || container == NULL) return NULL;
  SymMap::ViewKind view = SymMap::view_kind(source);
  const bool positional = view == SymMap::VIEW_NONE
      && ContainerSupport::capability(container)
             == ContainerSupport::CAPABILITY_INDEXED;
  if (!positional && view == SymMap::VIEW_NONE) return NULL;
  Expression *owner = ContainerSupport::receiver_owner(
      ConcolicMngr::ctx->find_stack_slot(
          handle.get_caller_stack_begin_offset()));
  // The state is read when the terminal runs (StreamPipeline::bind); here
  // only whether there is one, for an operation that ends the recording
  // before it.
  const bool stateful =
      ConcolicMngr::ctx->find_container_state(container) != NULL
      || SharedFieldVersions::is_tracked(
             ContainerSupport::state_location(container));
  Handle held(Thread::current(), container);
  ConcolicMngr::ctx->streams(true)->put(
      ConcolicMngr::ctx->name_reference(stream),
      new StreamPipeline(view, ContainerSupport::shape(container), owner,
                         JNIHandles::make_weak_global(held), stateful));
  return NULL;
}

bool SymStream::invoke_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &holder = handle.get_callee_holder_name();
  const std::string &method = handle.get_callee_name();
  if (named(holder, COLLECTORS)) {
    return method == "toList" || method == "toSet";
  }
  if (named(holder, UNMODIFIABLE_ENTRY_SET)) return invoke_source(handle);
  const bool stage = one_of(method, STAGES);
  const bool terminal = one_of(method, TERMINALS);
  if (!stage && !terminal && !one_of(method, UNMODELED)) return false;
  Method *callee = handle.get_callee_method();
  if (callee == NULL || callee->is_static()) return false;
  oop stream = handle.get_param<oop>(0);
  StreamPipeline *pipeline = recorded(stream);
  if (pipeline == NULL) return false;
  if (!stage && !terminal) {
    stop_recording(stream, "STREAM_OPERATION_UNMODELED:", method);
    return false;
  }
  if (stage) {
    if (method == "filter" || method == "map") {
      Stage kept(method == "filter" ? FILTER : MAP);
      kept.function = ConcolicMngr::ctx->name_reference(
          handle.get_param<oop>(1));
      pipeline->keep(kept);
    } else if (method == "limit") {
      Stage kept(LIMIT);
      // maxSize, a long, in locals 1-2.
      kept.bound = ConcolicMngr::ctx->find_stack_slot(
          handle.get_caller_stack_begin_offset() + 2);
      kept.concrete_bound = handle.get_param<jlong>(2);
      pipeline->keep(kept);
    } else if (method == "sorted") {
      Stage kept(SORTED);
      if (callee->size_of_parameters() == 2) {
        oop comparator = handle.get_param<oop>(1);
        if (comparator != NULL) {
          kept.function = ConcolicMngr::ctx->name_reference(comparator);
        }
      }
      pipeline->keep(kept);
    } else if (method == "distinct") {
      pipeline->keep(Stage(DISTINCT));
    } else {
      pipeline->cancel();  // unordered(): the sequential order stands
    }
    return true;
  }
  if (!ConcolicMngr::ctx->get_method_symbolizer().callbacks_available()) {
    // Its callbacks would run unlogged.
    stop_recording(stream, "STREAM_PINNED:", "CALLBACK_DEPTH");
    return false;
  }
  const Terminal kind = terminal_of(handle);
  if (kind == NO_TERMINAL) {
    stop_recording(stream, "STREAM_OPERATION_UNMODELED:", method);
    return false;
  }
  pipeline->begin(kind, handle);
  handle.set_seeder(seed_callback);
  handle.set_listener(fold_callback);
  handle.set_unwound(unwound);
  return true;
}

void SymStream::seed_callback(MethodSymbolizerHandle &call,
                              sym_rid_t receiver,
                              const std::vector<oop> &arguments,
                              exp_list_t *seeds, Expression **) {
  StreamPipeline *pipeline = recorded(call.get_param<oop>(0));
  if (pipeline == NULL) return;
  seeds->push_back(pipeline->enter(receiver, arguments.empty() ? (oop) NULL
                                                               : arguments[0]));
}

void SymStream::unwound(MethodSymbolizerHandle &call) {
  oop stream = call.get_param<oop>(0);
  StreamTable *table = ConcolicMngr::ctx->streams(false);
  StreamPipeline *pipeline = table == NULL || stream == NULL ? NULL
      : table->take(stream->get_sym_rid());
  if (pipeline == NULL) return;
  // What the body decided before the exception is stated nowhere.
  if (pipeline->unwinds()) {
    ConcolicMngr::ctx->note_model_gap("STREAM_PINNED:UNWOUND");
  }
  delete pipeline;
}

void SymStream::fold_callback(MethodSymbolizerHandle &call,
                              const CallbackResult &result, oop returned,
                              const std::vector<oop> &arguments) {
  StreamPipeline *pipeline = recorded(call.get_param<oop>(0));
  if (pipeline == NULL) return;
  pipeline->leave(result, returned,
                  arguments.empty() ? (oop) NULL : arguments[0]);
}

Expression *SymStream::finish_method_helper(MethodSymbolizerHandle &handle) {
  const std::string &holder = handle.get_callee_holder_name();
  const std::string &method = handle.get_callee_name();
  if (named(holder, COLLECTORS)) {
    oop accumulator = accumulator_of(handle.get_result<oop>(T_OBJECT));
    if (accumulator != NULL) {
      ConcolicMngr::ctx->streams(true)->name_collector(
          ConcolicMngr::ctx->name_reference(accumulator),
          method == "toList" ? COLLECTOR_TO_LIST : COLLECTOR_TO_SET);
    }
    return NULL;
  }
  if (named(holder, UNMODIFIABLE_ENTRY_SET)) return finish_source(handle);
  oop stream = handle.get_param<oop>(0);
  StreamTable *table = ConcolicMngr::ctx->streams(false);
  if (table == NULL || stream == NULL) return NULL;
  StreamPipeline *pipeline = table->take(stream->get_sym_rid());
  if (pipeline == NULL) return NULL;
  if (one_of(method, STAGES)) {
    // The pipeline moves to the stream the call returned.
    oop next = handle.get_result<oop>(T_OBJECT);
    if (next == NULL) {
      delete pipeline;
      return NULL;
    }
    pipeline->commit();
    table->put(ConcolicMngr::ctx->name_reference(next), pipeline);
    return NULL;
  }
  Expression *result = pipeline->finish(handle);
  delete pipeline;
  return result;
}

#endif // ENABLE_CONCOLIC
