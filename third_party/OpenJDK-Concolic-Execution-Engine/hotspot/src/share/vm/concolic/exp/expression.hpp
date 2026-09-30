#ifndef SHARE_VM_CONCOLIC_EXP_EXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_EXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/SymbolicOp.hpp"
#include "concolic/defs.hpp"
#include "oops/oop.inline.hpp"
#include "utilities/debug.hpp"
#include "utilities/ostream.hpp"
#include "webridge/utils/rapidjson/writer.h"

#include <map>
#include <cstdio>
#include <vector>

class ContainerExpression;
// One iterative rendering of an expression DAG into JSON.  Defined entirely in
// expression.cpp: nothing outside the serializer needs its shape.
class SerializationScope;
class VmExpressionArtifactScope;

/**
 * An expression node is immutable once constructed and is owned by the
 * GlobalSymbolicSession arena, never by whatever names it.
 *
 * Two rules follow, and every consumer in the engine depends on both:
 *
 *   - nothing deletes an Expression.  A shadow slot, field shadow, path
 *     condition entry, container state, broker leaf or parent node that stops
 *     naming a node simply stops naming it;
 *   - a parent node does not own its children, so a subtree may be shared
 *     freely, including between threads attached to the same session.
 *
 * Session teardown frees every node at once.  See globalSymbolicSession.hpp
 * for why this replaced per-node reference counting.
 */
class Expression {
  // The serializer drives serialize_internal directly, one node at a time,
  // instead of letting nodes call each other.
  friend class SerializationScope;
  friend class VmExpressionArtifactScope;

private:
  // Session-scoped identity.  Allocated from one atomic counter so that
  // concurrently built nodes cannot share an id.
  uint _unique_id;
  std::string _java_code_position;

public:
  virtual ~Expression() {}
  virtual bool is_op_str_expression() { return false; }
  // JVM booleans occupy int-shaped operand-stack slots, but their symbolic
  // semantics must remain Boolean.  Consumers use this bit to choose a
  // Boolean constant (rather than an integer 0/1) and to preserve Java
  // boolean &, | and ^ when the bytecode is shared with integer operations.
  virtual bool is_boolean_expression() { return false; }
  // Container algebra is the one place a shadow value has to be read back
  // structurally rather than only serialized, and HotSpot is built without
  // RTTI, so the downcast is declared here instead of guessed at.
  virtual ContainerExpression *as_container_expression() { return NULL; }

  // True for the value of a read through a *reference-typed* selected shared
  // location: a choice between the object identities the recorded writers
  // installed, rather than between scalars.  A dependent field read on such
  // a receiver is not a read of the concrete object the run happened to
  // land on -- it is a read of whichever object the selected writer put
  // there -- so getfield asks this before deciding whose field it names.
  // Declared here, and not answered by RTTI, because HotSpot is built
  // without it.
  virtual bool is_guarded_reference_read() { return false; }

  // The exact jint this node denotes, written to `value`, or false when it
  // denotes anything else.  Undoing a recorded INSERT to recover the content
  // a container held before it needs the position the insert happened at, and
  // a position that is itself symbolic is not one this engine can subtract.
  virtual bool concrete_int_value(jint *value) { return false; }

  // Consumer-boundary nodes are semantic identities.  Pointer identity is
  // still authoritative for every ordinary expression, but a field/version
  // check that already accepted `value` must also accept any chain of
  // consumer boundaries wrapped directly around that same value.  Keeping
  // this operation virtual avoids RTTI (HotSpot is built without it) and,
  // unlike stripping every identity node from both operands, cannot collapse
  // two independently produced expressions that merely share an ancestor.
  virtual bool is_or_wraps_consumer_value(Expression *value) {
    return this == value;
  }

  // The boolean negation of this predicate as a *new* node, or NULL when this
  // node is not a negatable relational comparison.  A conditional container
  // removal recorded on the branch that skipped it needs the branch's other
  // arm -- the removal condition -- and a relational comparison negates
  // exactly by flipping its operator (< <-> >=, == <-> !=), which keeps the
  // result a comparison the SMT codec already lowers rather than introducing a
  // unary `not` it might not.
  virtual Expression *logical_negation() { return NULL; }

  void set_java_code_position(const std::string &javaCodePosition);

  const std::string &getJavaCodePosition() const;

  inline uint get_unique_id() const { return _unique_id; }

protected:
  Expression();

protected:
  /**
   * Writes this node's own JSON members.  A node reaches its children the
   * only way it ever did, by calling serialize() on them, but that call no
   * longer descends: see serialize() below.
   */
  virtual void serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer) = 0;

public:
  /**
   * Renders the DAG rooted at this node as one JSON object when no explicit
   * VmExpressionArtifactScope is active.  An artifact scope writes a compact
   * session/id reference here and emits the node definitions at envelope end.
   *
   * The walk is iterative.  It used to be one native frame per node -- two,
   * with serialize_internal -- which put the depth of a traced workload's
   * expressions directly on the native stack: a path-condition conjunction is
   * one op_land node per branch the thread took, so a region that does string
   * or container work builds a left-deep chain thousands of nodes long and
   * overflowed the stack with a SIGSEGV that produced no hs_err file at all.
   * Depth is now a heap-allocated worklist, so it costs memory rather than
   * stack, and a node is rendered once per call rather than once per path that
   * reaches it.
   *
   * A nested call -- this same method, on a child, from inside
   * serialize_internal -- does not recurse.  It records the child as a slot in
   * the parent's own text and returns, and the driver splices the child in
   * afterwards.  A call that targets some other writer, which is how the few
   * callers that serialize into a buffer of their own behave, starts an
   * independent render instead.
   */
  void serialize(rapidjson::Writer<rapidjson::StringBuffer> &writer);

  virtual std::string get_name();
};

/**
 * One explicit artifact envelope whose expression values are references into
 * a session-local DAG table.
 *
 * Expression::serialize() deliberately keeps its historical tree encoding
 * unless a caller creates this scope.  While the scope is live, every call to
 * serialize() writes only a VmExpressionReference.  write_table() then emits
 * the transitive definitions once, with child expressions represented by the
 * same references.  The pair (sessionId, expressionId) is the raw identity;
 * portable/content-addressed identity is assigned by the artifact importer.
 *
 * A scope owns no Expression.  All pointers remain owned by the open
 * GlobalSymbolicSession arena.
 */
class VmExpressionArtifactScope {
private:
  typedef std::map<uint, Expression *> expression_map_t;
  typedef std::map<uint, std::string> definition_map_t;

  static __thread VmExpressionArtifactScope *_active;

  VmExpressionArtifactScope *_previous;
  jlong _session_id;
  expression_map_t _expressions;
  std::vector<Expression *> _pending;
  definition_map_t _definitions;
  size_t _next_pending;
  // Running total of rendered definition bytes, so the size question above is
  // answered without re-walking the map on every call.
  size_t _definition_bytes;
  bool _table_written;

  void record(Expression *expression);
  void render_definition(Expression *expression);
  void write_reference(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      Expression *expression, bool record_definition);

  // A scope is stack state.  Copying it would install two owners of the same
  // thread-local activation and make destruction order ambiguous.
  VmExpressionArtifactScope(const VmExpressionArtifactScope &);
  VmExpressionArtifactScope &operator=(const VmExpressionArtifactScope &);

public:
  VmExpressionArtifactScope();
  ~VmExpressionArtifactScope();

  static VmExpressionArtifactScope *active() { return _active; }

  /** Exact JSON byte length of one reference, without retaining its node. */
  size_t reference_size(Expression *expression);

  /**
   * Bytes the table will add to the envelope for everything recorded so far.
   *
   * While a scope is active, serialize() leaves only a short reference in the
   * caller's buffer and the whole DAG goes to the table, so a caller that
   * bounds its envelope by buffer size alone bounds almost nothing.  This
   * renders every definition discovered so far -- exactly the work write_table
   * would do at the end -- and reports the total, so a byte budget can be
   * checked against what has actually been committed to.
   *
   * Rendering is done once per node: write_table() resumes where this left
   * off and still emits each definition exactly once.
   */
  size_t pending_table_size();

  /** Writes the `vmExpressionTable` member of the currently open object. */
  void write_table(rapidjson::Writer<rapidjson::StringBuffer> &writer);

  // Called only by Expression::serialize().
  void serialize_reference(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      Expression *expression) {
    write_reference(writer, expression, true);
  }
};

class OpSymExpression : public Expression {
private:
  Expression *_left;
  Expression *_right;
  SymbolicOp _op;

public:
  OpSymExpression(Expression *l, Expression *r, SymbolicOp op, bool cmp = true);
  OpSymExpression(Expression *r, SymbolicOp op);
  virtual std::string get_name();
  virtual bool is_boolean_expression();
  virtual Expression *logical_negation();

protected:
  void serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

class ConExpression : public Expression {
  static const int EXP_NAME_LENGTH = 32;

private:
  char _str[EXP_NAME_LENGTH];
  std::string _type;

public:
  ConExpression(jboolean b);
  ConExpression(jbyte c);
  ConExpression(jchar b);
  ConExpression(jint i);
  ConExpression(jshort s);
  ConExpression(jlong l);
  ConExpression(jfloat f);
  ConExpression(jdouble d);

public:
  virtual bool is_boolean_expression();
  virtual bool concrete_int_value(jint *value);

  void serialize_internal(rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

/**
 * What a read or a call returned, when it is a value rather than an
 * identity: a primitive's constant, null, or a String's content.  Any other
 * object is an identity no formula can pin, and stays unstated.
 *
 * A node whose own formula may not decide its value states it, so that the
 * composer can pin the node to what the run saw: a read whose observed write
 * does not lower (ReadFromExpression), the result of a call the VM does not
 * model (MethodReturnSymbolExp).  Both spell it one way, as `concreteValue`.
 */
struct ReturnedValue {
  // TRUNCATED_STRING: a String longer than the VM states, spelled as a
  // `TruncatedValue` object with its UTF-8 length; a consumer reads it as
  // unstated, never as a prefix.
  enum Kind { UNSTATED, CONSTANT, NULL_REFERENCE, STRING, TRUNCATED_STRING };
  Kind kind;
  Expression *constant;
  std::string content;
  int length;
  ReturnedValue() : kind(UNSTATED), constant(NULL), length(0) {}

  // Writes the `concreteValue` member of the node being serialized.
  void serialize(rapidjson::Writer<rapidjson::StringBuffer> &writer) const;
};

typedef std::vector<Expression *> exp_list_t;
typedef std::map<int, Expression *> exp_map_t;

#endif

#endif // SHARE_VM_CONCOLIC_EXP_EXPRESSION_HPP
