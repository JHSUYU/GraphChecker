#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "runtime/atomic.inline.hpp"
#include "webridge/utils/rapidjson/document.h"
#include "utilities/ostream.hpp"
#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <set>
#include <string>
#include <vector>

// ---------------------------------------------------------------------------
// Iterative expression serialization
// ---------------------------------------------------------------------------

/**
 * One rendering of one expression DAG into JSON, with no native recursion.
 *
 * The walk runs in two passes over the nodes reachable from the root.
 *
 *   - discover() renders each distinct node's *own* JSON -- its members, with
 *     a bare `null` standing in wherever a child belongs -- and records the
 *     byte range each of those placeholders occupies.  A node's own text is
 *     bounded by the node itself, not by its subtree, so this pass costs
 *     O(nodes) and never needs the child's text to produce the parent's.
 *   - assemble() splices: it copies own text up to a placeholder, expands the
 *     child there, and continues.  The pending work is a std::vector of
 *     frames, so a chain thousands of nodes deep costs heap and not stack.
 *
 * Recording placeholders as byte ranges, rather than as a marker string to be
 * searched for later, is deliberate: JSON escaping would let a crafted Java
 * code position or symbol name imitate any marker, and a serializer that can
 * be confused about where a child ends is a worse failure than the crash this
 * replaces.
 *
 * The scope is created on the stack of the thread doing the serializing and is
 * reachable only through a thread-local pointer, so nothing here is shared
 * between threads and no publication protocol is needed.  That is also why the
 * per-child text caches the nodes used to keep are gone: they were published
 * once and lived for the session, which made a left-deep chain quadratic in
 * native memory -- every node retaining a private copy of the whole prefix
 * below it.  Each distinct node's local shape is still rendered once per
 * call, but shared subtrees are walked again at each use rather than cached as
 * expanded JSON: caching the expanded text turns a linear DAG such as
 * t[n+1] = t[n] + t[n] into exponentially growing native strings even though
 * the expression graph itself stays small.  The byte cap below bounds those
 * repeated walks without retaining subtree text.
 */
class SerializationScope {
public:
  // Beyond this many spliced nodes a single render gives up and says so.  This
  // is not what keeps the walk off the stack -- assemble() is iterative -- it
  // only stops one pathological DAG from producing JSON no consumer could
  // read.  Normal evidence is orders of magnitude below it.
  static const size_t MAX_EMITTED_NODES = 1000000;
  // A hard cap on one rendered expression.  Both unique-node and byte bounds
  // are necessary: a small shared DAG can have exponentially large tree text.
  // A bounded guarded read serializes every candidate in one root; normal
  // fixed-loop workloads can therefore exceed 8 MiB even though each arm and
  // the underlying DAG are modest.  Keep enough room for that bounded union
  // while retaining an explicit fail-closed ceiling for pathological trees.
  static const size_t MAX_RENDER_BYTES = 32u * 1024u * 1024u;
  // Discovery stores only each distinct node's local JSON and child slots,
  // but that work precedes assembly and therefore needs its own bounds.
  static const size_t MAX_DISCOVERED_NODES = 100000;
  static const size_t MAX_DISCOVERY_STORAGE_BYTES = 32u * 1024u * 1024u;
  // append_truncation uses a 256-byte stack buffer.  Reserving the whole
  // buffer for every pending child keeps the final JSON valid even when a
  // deeply nested expansion reaches the byte cap.
  static const size_t TRUNCATION_RESERVE = 256;
  // Width of the `null` a child's placeholder occupies.
  static const size_t NULL_LITERAL_LENGTH = 4;

  static SerializationScope *active() { return _active; }

  SerializationScope()
      : _previous(_active), _own_buffer(NULL), _own_writer(NULL),
        _own_slots(NULL), _emitted(0), _minimum_remaining(0),
        _discovered_storage_bytes(0) {
    _active = this;
  }

  ~SerializationScope() { _active = _previous; }

  // True when `writer` is the one this scope is currently filling with a
  // node's own text, which is the only writer whose byte offsets mean anything
  // to us.
  bool owns(rapidjson::Writer<rapidjson::StringBuffer> &writer) const {
    return _own_writer == &writer;
  }

  // Reserves a child's place in the parent's own text.  Writing a real `null`
  // keeps the JSON writer's own state -- comma placement, value counts --
  // exactly as it would have been had the child been written here.
  //
  // Only the four bytes of the literal are the child's place.  Writer::Null()
  // first emits whatever separator the enclosing object or array needs -- the
  // `:` after a key, or a `,` between elements -- and that separator belongs
  // to the parent's own text, not to the child.  Measuring back from the end
  // rather than forward from the start is what keeps it there.
  void record_child(rapidjson::Writer<rapidjson::StringBuffer> &writer,
                    Expression *child) {
    size_t before = _own_buffer->GetSize();
    writer.Null();
    size_t end = _own_buffer->GetSize();
    guarantee(end >= before + NULL_LITERAL_LENGTH,
              "a JSON null must be four bytes wide");
    _own_slots->push_back(
        ChildSlot(end - NULL_LITERAL_LENGTH, end, child));
  }

  void render(Expression *root,
              rapidjson::Writer<rapidjson::StringBuffer> &out);

private:
  struct ChildSlot {
    // Byte range of the placeholder inside the parent's own text.
    size_t start;
    size_t end;
    Expression *child;
    ChildSlot(size_t s, size_t e, Expression *c)
        : start(s), end(e), child(c) {}
  };

  struct NodeText {
    std::string own;
    std::vector<ChildSlot> slots;
    // min_remaining[i] is the conservative number of bytes needed to finish
    // this node when its next child is slots[i], replacing every remaining
    // child with a bounded TruncatedExpression.
    std::vector<size_t> min_remaining;
  };

  typedef std::map<Expression *, NodeText> node_map_t;

  struct Frame {
    Expression *node;
    NodeText *text;
    size_t slot;
    size_t cursor;
  };

  void discover(Expression *root);
  void render_own(Expression *node, NodeText &entry);
  void assemble(Expression *root, std::string &out);
  void push_frame(std::vector<Frame> &stack, Expression *node);
  static void append_truncation(std::string &dest, const char *kind,
                                Expression *node);

  static __thread SerializationScope *_active;

  SerializationScope *_previous;
  rapidjson::StringBuffer *_own_buffer;
  rapidjson::Writer<rapidjson::StringBuffer> *_own_writer;
  std::vector<ChildSlot> *_own_slots;
  node_map_t _nodes;
  std::set<Expression *> _on_path;
  size_t _emitted;
  size_t _minimum_remaining;
  size_t _discovered_storage_bytes;
};

__thread SerializationScope *SerializationScope::_active = NULL;

/**
 * A subtree the serializer refused to expand, named rather than dropped.
 *
 * Silently emitting a partial or truncated value would turn a structural
 * problem into wrong evidence, which is strictly worse than the crash this
 * code replaces: a crash is at least visible.  This object is visible in the
 * same way -- a consumer that does not know the type will fail to interpret
 * it, and one that does can record a coverage gap.
 */
void SerializationScope::append_truncation(std::string &dest, const char *kind,
                                           Expression *node) {
  char buf[256];
  int length = snprintf(
      buf, sizeof(buf),
      "{\"_type\":\"TruncatedExpression\",\"expressionAuthority\":"
      "\"VM_SERIALIZATION_TRUNCATION_V1\",\"truncationKind\":\"%s\","
      "\"expressionId\":%u}",
      kind, node == NULL ? 0u : node->get_unique_id());
  if (length > 0) {
    size_t available = sizeof(buf) - 1;
    size_t emitted = (size_t) length < available ? (size_t) length : available;
    dest.append(buf, emitted);
  }
}

void SerializationScope::render_own(Expression *node, NodeText &entry) {
  using namespace rapidjson;
  StringBuffer buffer;
  Writer<StringBuffer> writer(buffer);

  _own_buffer = &buffer;
  _own_writer = &writer;
  _own_slots = &entry.slots;

  writer.StartObject();
  const std::string &position = node->getJavaCodePosition();
  if (!position.empty()) {
    writer.Key("_code_position");
    writer.String(position.c_str());
  }
  node->serialize_internal(writer);
  writer.EndObject();

  _own_buffer = NULL;
  _own_writer = NULL;
  _own_slots = NULL;

  entry.own.assign(buffer.GetString(), buffer.GetSize());
}

void SerializationScope::discover(Expression *root) {
  std::vector<Expression *> pending;
  pending.push_back(root);
  while (!pending.empty()) {
    Expression *node = pending.back();
    pending.pop_back();
    if (_nodes.find(node) != _nodes.end()) {
      continue;
    }
    if (_nodes.size() >= MAX_DISCOVERED_NODES) {
      // Parents already contain slots for every undiscovered child.  Leaving
      // those children absent makes assemble() emit the explicit
      // EXPRESSION_NOT_DISCOVERED marker at the exact slot without retaining
      // the rest of the graph.
      break;
    }
    // Insert before rendering: a node reached again while its own text is
    // being produced must not be rendered twice.
    NodeText &entry = _nodes[node];
    render_own(node, entry);
    const size_t slot_count = entry.slots.size();
    const bool slots_overflow = slot_count > MAX_DISCOVERY_STORAGE_BYTES
        / sizeof(ChildSlot);
    const size_t slot_bytes = slots_overflow ? MAX_DISCOVERY_STORAGE_BYTES + 1
        : slot_count * sizeof(ChildSlot);
    const bool node_overflow = entry.own.size() > MAX_RENDER_BYTES
        || slots_overflow || entry.own.size() > MAX_DISCOVERY_STORAGE_BYTES
        || slot_bytes > MAX_DISCOVERY_STORAGE_BYTES - entry.own.size();
    const size_t node_bytes = node_overflow ? MAX_DISCOVERY_STORAGE_BYTES + 1
        : entry.own.size() + slot_bytes;
    if (node_overflow
        || _discovered_storage_bytes > MAX_DISCOVERY_STORAGE_BYTES
        || node_bytes > MAX_DISCOVERY_STORAGE_BYTES
            - _discovered_storage_bytes) {
      entry.own.clear();
      entry.slots.clear();
      append_truncation(entry.own, "EXPRESSION_DISCOVERY_LIMIT", node);
      break;
    }
    _discovered_storage_bytes += node_bytes;
    for (size_t index = 0; index < entry.slots.size(); ++index) {
      pending.push_back(entry.slots[index].child);
    }
  }

  // Pre-compute the minimum valid tail for every frame position.  Each child
  // reserves enough room for a TruncatedExpression, so assemble() can stop at
  // any child boundary without cutting JSON punctuation or leaving an object
  // unterminated.  Values above MAX_RENDER_BYTES only need to remain
  // distinguishable as "too large", hence the saturating addition.
  for (node_map_t::iterator it = _nodes.begin(); it != _nodes.end(); ++it) {
    NodeText &entry = it->second;
    const size_t count = entry.slots.size();
    entry.min_remaining.assign(count + 1, 0);
    const size_t last_cursor = count == 0 ? 0 : entry.slots[count - 1].end;
    entry.min_remaining[count] = entry.own.size() - last_cursor;
    for (size_t next = count; next > 0; --next) {
      const size_t index = next - 1;
      const size_t cursor = index == 0 ? 0 : entry.slots[index - 1].end;
      const size_t own_prefix = entry.slots[index].start - cursor;
      size_t required = entry.min_remaining[index + 1];
      if (own_prefix > MAX_RENDER_BYTES
          || required > MAX_RENDER_BYTES - own_prefix) {
        required = MAX_RENDER_BYTES + 1;
      } else {
        required += own_prefix;
        if (required > MAX_RENDER_BYTES - TRUNCATION_RESERVE) {
          required = MAX_RENDER_BYTES + 1;
        } else {
          required += TRUNCATION_RESERVE;
        }
      }
      entry.min_remaining[index] = required;
    }
  }
}

void SerializationScope::push_frame(std::vector<Frame> &stack,
                                    Expression *node) {
  Frame frame;
  frame.node = node;
  frame.text = &_nodes[node];
  frame.slot = 0;
  frame.cursor = 0;
  stack.push_back(frame);
  _on_path.insert(node);
}

void SerializationScope::assemble(Expression *root, std::string &out) {
  std::vector<Frame> stack;
  NodeText &root_text = _nodes[root];
  if (root_text.min_remaining.empty()
      || root_text.min_remaining[0] > MAX_RENDER_BYTES) {
    append_truncation(out, "EXPRESSION_BYTE_LIMIT", root);
    return;
  }
  _minimum_remaining = root_text.min_remaining[0];
  push_frame(stack, root);

  while (!stack.empty()) {
    Frame &frame = stack.back();
    NodeText &text = *frame.text;

    if (frame.slot >= text.slots.size()) {
      const size_t suffix = text.own.size() - frame.cursor;
      guarantee(_minimum_remaining >= suffix,
                "expression byte reservation underflow");
      guarantee(suffix <= MAX_RENDER_BYTES
                    && out.size() <= MAX_RENDER_BYTES - suffix,
                "expression byte reservation overflow");
      out.append(text.own, frame.cursor, suffix);
      _minimum_remaining -= suffix;
      Expression *node = frame.node;
      _on_path.erase(node);
      stack.pop_back();
      continue;
    }

    const ChildSlot slot = text.slots[frame.slot];
    const size_t prefix = slot.start - frame.cursor;
    guarantee(prefix <= _minimum_remaining
                  && _minimum_remaining - prefix >= TRUNCATION_RESERVE,
              "expression child reservation underflow");
    guarantee(prefix <= MAX_RENDER_BYTES
                  && out.size() <= MAX_RENDER_BYTES - prefix,
              "expression byte reservation overflow");
    out.append(text.own, frame.cursor, prefix);
    _minimum_remaining -= prefix;
    frame.cursor = slot.end;
    frame.slot++;
    // Anything below may push, which invalidates `frame` and `text`.

    Expression *child = slot.child;

    // A back edge, checked before anything else: expanding a node still on the
    // path would not terminate.  Expression nodes are built bottom-up in the
    // normal case, but malformed/cyclic evidence must remain bounded too.
    if (_on_path.find(child) != _on_path.end()) {
      append_truncation(out, "EXPRESSION_CYCLE", child);
      _minimum_remaining -= TRUNCATION_RESERVE;
      continue;
    }

    node_map_t::iterator found = _nodes.find(child);
    if (found == _nodes.end()) {
      // discover() reaches every slot child, so this cannot happen; say so
      // rather than splicing in nothing and emitting malformed JSON.
      append_truncation(out, "EXPRESSION_NOT_DISCOVERED", child);
      _minimum_remaining -= TRUNCATION_RESERVE;
      continue;
    }
    NodeText &child_text = found->second;

    if (++_emitted > MAX_EMITTED_NODES) {
      append_truncation(out, "EXPRESSION_SIZE_LIMIT", child);
      _minimum_remaining -= TRUNCATION_RESERVE;
      continue;
    }

    const size_t child_minimum = child_text.min_remaining.empty()
        ? MAX_RENDER_BYTES + 1 : child_text.min_remaining[0];
    const size_t without_placeholder =
        _minimum_remaining - TRUNCATION_RESERVE;
    guarantee(out.size() <= MAX_RENDER_BYTES
                  && without_placeholder <= MAX_RENDER_BYTES - out.size(),
              "expression minimum tail exceeds byte budget");
    const size_t available =
        MAX_RENDER_BYTES - out.size() - without_placeholder;
    if (child_minimum > MAX_RENDER_BYTES
        || child_minimum > available) {
      append_truncation(out, "EXPRESSION_BYTE_LIMIT", child);
      _minimum_remaining = without_placeholder;
      continue;
    }
    _minimum_remaining = without_placeholder + child_minimum;
    push_frame(stack, child);
  }
  guarantee(_minimum_remaining == 0,
            "expression byte reservations must be consumed");
}

void SerializationScope::render(Expression *root,
                                rapidjson::Writer<rapidjson::StringBuffer> &out) {
  discover(root);
  std::string text;
  assemble(root, text);
  out.RawValue(text.data(), text.size(), rapidjson::kObjectType);
}

// ---------------------------------------------------------------------------
// Session-local expression DAG artifacts
// ---------------------------------------------------------------------------

__thread VmExpressionArtifactScope *VmExpressionArtifactScope::_active = NULL;

namespace {

// The fixed JSON around one definition ("_type", "sessionId", "expressionId",
// "expression" and their punctuation) and around the table itself.  Both are
// deliberate over-estimates: a size budget that under-counts its own envelope
// is the bug this accounting exists to close.
static const size_t DEFINITION_ENVELOPE_BYTES = 128;
static const size_t TABLE_ENVELOPE_BYTES = 256;

} // anonymous namespace

VmExpressionArtifactScope::VmExpressionArtifactScope()
    : _previous(_active),
      _session_id(GlobalSymbolicSession::session_id()),
      _next_pending(0), _definition_bytes(0), _table_written(false) {
  _active = this;
}

VmExpressionArtifactScope::~VmExpressionArtifactScope() {
  guarantee(_table_written || _expressions.empty(),
            "a VM expression artifact omitted its expression table");
  guarantee(_active == this,
            "VM expression artifact scopes must close in stack order");
  _active = _previous;
}

void VmExpressionArtifactScope::record(Expression *expression) {
  guarantee(expression != NULL,
            "a VM expression reference requires an expression");
  guarantee(!_table_written,
            "an expression cannot be added after its artifact table");
  guarantee(_session_id != 0 && GlobalSymbolicSession::is_open()
                && GlobalSymbolicSession::session_id() == _session_id,
            "a VM expression reference cannot cross symbolic sessions");

  const uint id = expression->get_unique_id();
  std::pair<expression_map_t::iterator, bool> inserted =
      _expressions.insert(std::make_pair(id, expression));
  guarantee(inserted.second || inserted.first->second == expression,
            "two expressions share one session-local expression id");
  if (inserted.second) {
    _pending.push_back(expression);
  }
}

void VmExpressionArtifactScope::write_reference(
    rapidjson::Writer<rapidjson::StringBuffer> &writer,
    Expression *expression, bool record_definition) {
  if (record_definition) {
    record(expression);
  }
  writer.StartObject();
  writer.Key("_type");
  writer.String("VmExpressionReference");
  writer.Key("sessionId");
  writer.Int64(_session_id);
  writer.Key("expressionId");
  writer.Uint(expression->get_unique_id());
  writer.EndObject();
}

size_t VmExpressionArtifactScope::reference_size(Expression *expression) {
  guarantee(expression != NULL,
            "a VM expression reference requires an expression");
  guarantee(_session_id != 0 && GlobalSymbolicSession::is_open()
                && GlobalSymbolicSession::session_id() == _session_id,
            "a VM expression reference cannot cross symbolic sessions");
  rapidjson::StringBuffer buffer;
  rapidjson::Writer<rapidjson::StringBuffer> writer(buffer);
  write_reference(writer, expression, false);
  return buffer.GetSize();
}

void VmExpressionArtifactScope::render_definition(Expression *expression) {
  rapidjson::StringBuffer buffer;
  rapidjson::Writer<rapidjson::StringBuffer> writer(buffer);
  writer.StartObject();
  const std::string &position = expression->getJavaCodePosition();
  if (!position.empty()) {
    writer.Key("_code_position");
    writer.String(position.c_str());
  }
  // Child calls to Expression::serialize() observe this explicit artifact
  // scope, write references and extend `_pending`; no native recursion and no
  // expanded subtree text is involved.
  expression->serialize_internal(writer);
  writer.EndObject();

  std::pair<definition_map_t::iterator, bool> inserted =
      _definitions.insert(std::make_pair(
          expression->get_unique_id(),
          std::string(buffer.GetString(), buffer.GetSize())));
  guarantee(inserted.second,
            "a VM expression node was defined more than once");
  _definition_bytes += buffer.GetSize() + DEFINITION_ENVELOPE_BYTES;
}

size_t VmExpressionArtifactScope::pending_table_size() {
  if (_table_written) return 0;
  // The same drain write_table() performs.  Rendering one node may discover
  // children, so the vector grows during the loop.
  while (_next_pending < _pending.size()) {
    render_definition(_pending[_next_pending++]);
  }
  return _definition_bytes + TABLE_ENVELOPE_BYTES;
}

void VmExpressionArtifactScope::write_table(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  guarantee(!_table_written,
            "a VM expression artifact table may be written only once");
  guarantee(_active == this,
            "only the active VM expression artifact may write its table");

  // Rendering one local node shape may discover children.  The vector grows
  // during this loop, so every transitively reachable node is eventually
  // rendered once.  Definitions are emitted from the id-keyed map afterwards
  // to make artifact order independent of root order.
  while (_next_pending < _pending.size()) {
    Expression *expression = _pending[_next_pending++];
    render_definition(expression);
  }
  guarantee(_definitions.size() == _expressions.size(),
            "every VM expression reference requires one definition");
  _table_written = true;

  writer.Key("vmExpressionTable");
  writer.StartObject();
  writer.Key("schemaVersion");
  writer.Int(1);
  writer.Key("kind");
  writer.String("VM_EXPRESSION_TABLE");
  writer.Key("authority");
  writer.String("VM_SESSION_EXPRESSION_ID_V1");
  writer.Key("sessionId");
  writer.Int64(_session_id);
  writer.Key("definitionCount");
  writer.Int64((jlong)_definitions.size());
  writer.Key("definitions");
  writer.StartArray();
  for (definition_map_t::const_iterator it = _definitions.begin();
       it != _definitions.end(); ++it) {
    writer.StartObject();
    writer.Key("_type");
    writer.String("VmExpressionDefinition");
    writer.Key("sessionId");
    writer.Int64(_session_id);
    writer.Key("expressionId");
    writer.Uint(it->first);
    writer.Key("expression");
    writer.RawValue(it->second.data(), it->second.size(),
                    rapidjson::kObjectType);
    writer.EndObject();
  }
  writer.EndArray();
  writer.EndObject();
}

void Expression::serialize(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  VmExpressionArtifactScope *artifact = VmExpressionArtifactScope::active();
  if (artifact != NULL) {
    artifact->serialize_reference(writer, this);
    return;
  }
  SerializationScope *scope = SerializationScope::active();
  if (scope != NULL && scope->owns(writer)) {
    // A child, reached from its parent's serialize_internal.  Leave a slot and
    // return: the driver expands it without growing the native stack.
    scope->record_child(writer, this);
    return;
  }
  // A root, or a caller serializing into a buffer of its own.  Either way this
  // is an independent render.
  SerializationScope fresh;
  fresh.render(this, writer);
}

Expression::Expression()
    : _unique_id(GlobalSymbolicSession::next_expression_id()) {
  // The arena takes ownership here, before any caller can see the node.  From
  // this point nothing else may delete it.
  GlobalSymbolicSession::record_expression(this);
}

void Expression::set_java_code_position(const std::string &javaCodePosition) {
  _java_code_position = javaCodePosition;
}

const std::string &Expression::getJavaCodePosition() const {
  return _java_code_position;
}


std::string Expression::get_name() {
  rapidjson::StringBuffer s;
  rapidjson::Writer<rapidjson::StringBuffer> writer(s);
  serialize(writer);
  rapidjson::Document doc;
  // Iteratively: rapidjson's default parser is recursive descent, one native
  // frame per level of nesting, and what it is being handed here is the
  // serialized form of an expression DAG -- exactly the thing whose nesting is
  // bounded only by the workload.  Making the walk that produced this text
  // iterative would achieve nothing if reading it back overflowed the stack
  // instead.
  doc.Parse<rapidjson::kParseIterativeFlag>(s.GetString());
  if (doc.HasMember("_exp")) {
    return doc["_exp"].GetString();
  } else {
    guarantee(false, (std::string("Not implemented expression get_name:") + s.GetString()).c_str());
  }
}

OpSymExpression::OpSymExpression(Expression *l, Expression *r, SymbolicOp op,
                                 bool cmp)
    : _left(l), _right(r), _op(cmp ? op : NotSymbolicOp[op]) {
}

OpSymExpression::OpSymExpression(Expression *r, SymbolicOp op)
    : _left(NULL), _right(r), _op(op) {
}

void OpSymExpression::serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  using namespace rapidjson;
  writer.Key("_type");
  writer.String("BinaryExpression");

  writer.Key("_left");
  if (_left) {
    _left->serialize(writer);
  } else {
    writer.Null();
  }

  writer.Key("_op");
  writer.String(SymbolicOpStr[(int) _op]);

  // JVM lcmp/fcmp*/dcmp* instructions produce an int trichotomy even when
  // their operands are long/float/double.  Make that result type explicit so
  // external consumers do not have to recover it from stack shape.
  if (_op == op_cmp || _op == op_cmpl || _op == op_cmpg) {
    writer.Key("_java_type");
    writer.String("I");
  }

  writer.Key("_right");
  if (_right) {
    _right->serialize(writer);
  } else {
    writer.Null();
  }
}

std::string OpSymExpression::get_name() {
  std::string name = "";
  if (_left) {
    name = _left->get_name();
  } else {
    name = "null";
  }
  name = name + SymbolicOpStr[_op];
  if (_right) {
    name = name + _right->get_name();
  } else {
    name = name + "null";
  }
  return name;
}

bool OpSymExpression::is_boolean_expression() {
  return _op == op_lt || _op == op_gt || _op == op_le || _op == op_ge
      || _op == op_eq || _op == op_ne || _op == op_land || _op == op_lor;
}

Expression *OpSymExpression::logical_negation() {
  // Only the six relational comparisons have a total complement expressible as
  // another comparison; NotSymbolicOp maps exactly those and leaves the rest
  // op_null.  op_land/op_lor could be pushed through De Morgan, but a recorded
  // branch predicate is a single comparison, so refusing the compound case is
  // enough and keeps the negation a leaf-simple flip.
  SymbolicOp complement = NotSymbolicOp[_op];
  if (complement == op_null) {
    return NULL;
  }
  // cmp=true keeps `op` as given rather than re-negating it.
  return new OpSymExpression(_left, _right, complement, true);
}

ConExpression::ConExpression(jboolean z) {
  _type = type2char(T_BOOLEAN);
  int ret = sprintf(_str, "Y_Z_%u", z);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jbyte b) {
  _type = type2char(T_BYTE);
  int ret = sprintf(_str, "Y_B_%d", b);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jchar b) {
  _type = type2char(T_CHAR);
  int ret = sprintf(_str, "Y_C_%u", (unsigned int)b);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jint i) {
  _type = type2char(T_INT);
  int ret = sprintf(_str, "Y_I_%d", i);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jshort s) {
  _type = type2char(T_SHORT);
  int ret = sprintf(_str, "Y_S_%d", s);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jlong l) {
  _type = type2char(T_LONG);
  int ret = sprintf(_str, "Y_J_" JLONG_FORMAT, l);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jfloat f) {
  _type = type2char(T_FLOAT);
  int ret = sprintf(_str, "Y_F_%.9e", f);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

ConExpression::ConExpression(jdouble d) {
  _type = type2char(T_DOUBLE);
  int ret = sprintf(_str, "Y_D_%.17e", d);
  assert(ret <= EXP_NAME_LENGTH, "SYM_NAME_LENGTH exceeded!");
}

bool ConExpression::is_boolean_expression() {
  return _type.size() == 1 && _type[0] == type2char(T_BOOLEAN);
}

// The constant is kept as the text the serializer emits, so reading it back
// re-parses that text rather than keeping a second copy of the value that
// could drift from it.  Only T_INT answers: a long, a char or a boolean
// position is not a position the indexed algebra records.
bool ConExpression::concrete_int_value(jint *value) {
  if (value == NULL) return false;
  if (_type.size() != 1 || _type[0] != type2char(T_INT)) return false;
  const char *digits = strchr(_str, '_');
  if (digits == NULL) return false;
  digits = strchr(digits + 1, '_');
  if (digits == NULL) return false;
  ++digits;
  char *tail = NULL;
  errno = 0;
  long parsed = strtol(digits, &tail, 10);
  if (errno != 0 || tail == digits || tail == NULL || *tail != '\0') {
    return false;
  }
  if (parsed < (long)min_jint || parsed > (long)max_jint) return false;
  *value = (jint)parsed;
  return true;
}

void ConExpression::serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ConstExpr");
  writer.Key("_java_type");
  writer.String(_type.c_str());
  writer.Key("_exp");
  writer.String(_str);
}

void ReturnedValue::serialize(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) const {
  // Absent, not null, when nothing is stated: null is a value.
  switch (kind) {
    case CONSTANT:
      writer.Key("concreteValue");
      constant->serialize(writer);
      break;
    case NULL_REFERENCE:
      writer.Key("concreteValue");
      writer.Null();
      break;
    case STRING:
      writer.Key("concreteValue");
      writer.String(content.c_str(), (rapidjson::SizeType) content.size());
      break;
    case UNSTATED:
      break;
  }
}

#endif
