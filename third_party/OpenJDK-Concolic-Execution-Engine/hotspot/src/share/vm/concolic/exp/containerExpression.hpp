#ifndef SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <string>

class ElementWrites;

/**
 * What one INDEXED WRITE left in the heap, so a read that the chain decides
 * can check that the element still holds it: a primitive's raw bits, or a
 * reference's session id (0 for null).  A write no hook saw -- JNI, a muted
 * store -- makes the log stale; the word is how a read finds out.
 * `symbolic` says the stored value was an expression rather than the
 * concrete word itself, which a read then returns as concrete.
 * Unstated for a writer that knows no word: its value is taken as recorded.
 */
struct ElementWord {
  bool symbolic;
  bool stated;
  jlong bits;
  ElementWord() : symbolic(true), stated(false), bits(0) {}
  ElementWord(bool is_symbolic, jlong word_bits)
      : symbolic(is_symbolic), stated(true), bits(word_bits) {}
};

/**
 * One operation in an activation-local shadow container.
 *
 * The VM records Java semantics, not SMT syntax.  Nested expressions form the
 * state transformer consumed by GraphChecker's single ContainerSmtCodec.
 */
class ContainerExpression : public Expression {
 private:
  std::string _shape;
  std::string _operation;
  Expression *_receiver;
  exp_list_t _arguments;
  std::string _java_type;
  // The control-flow predicate a conditionally-recorded mutation fired under,
  // or NULL for an unconditional one.  Today only ASSOCIATIVE/REMOVE_IF carries
  // it: the removeExpiredKeys `if (expiry < now)` branch, recorded so that an
  // external solver may flip the removal (the flippable-removal story).  The
  // guard is oriented as the *removal condition* (true => the key is gone),
  // independent of which way the concrete run branched.
  Expression *_guard;
  // The reference the receiver was read through, when the call's receiver
  // slot carried a guarded reference read (a tracked reference field, an
  // AtomicReference, a container READ result): which object that read
  // chose survives, while `_receiver` stays the observed object's state.
  // Views, iterators and entries inherit it.  NULL otherwise, and then not
  // serialized, so every other node's JSON is unchanged.
  Expression *_owner;
  // See has_constant_size().
  bool _constant_size;
  // See stored_at().  `_writes` is the log this chain's WRITEs share, and
  // `_ordinal` this node's place in it; the WRITE whose ordinal is 1 made
  // the log and frees it.
  bool _decides_reads;
  uint _ordinal;
  ElementWrites *_writes;

 public:
  ContainerExpression(const char *shape, const char *operation,
                      Expression *receiver, const exp_list_t &arguments,
                      BasicType result_type = T_OBJECT,
                      const std::string &java_type = std::string(),
                      Expression *guard = NULL,
                      Expression *owner = NULL,
                      const ElementWord &word = ElementWord());
  virtual ~ContainerExpression();

  virtual ContainerExpression *as_container_expression() { return this; }
  virtual bool derived_container_value(Expression **owner);

  // Whether SIZE of this state is a constant: the STATE root of a Java array
  // allocated with a concrete length, and every WRITE over one, which
  // replaces an element in place.  Decided at construction from the
  // receiver's answer, so asking costs nothing however long the chain is.
  bool has_constant_size() const { return _constant_size; }

  // What a read at the concrete `position` of this state returns, when the
  // chain alone decides it: the state is a Java array's STATE root with a
  // constant length, or a WRITE at a concrete position over such a state.
  // `*stored` is then the value the newest WRITE at `position` stored, and
  // `*word` what it left in the heap, or NULL when none did and the element
  // is the root's.  A WRITE at a symbolic position may have replaced any
  // element, so no state above one decides.  Decided at construction and
  // answered from the one log the chain's WRITEs share, so a read never
  // walks the chain however long it is.
  bool stored_at(jint position, Expression **stored, ElementWord *word) const;

  const std::string &get_operation() const { return _operation; }
  const std::string &get_shape() const { return _shape; }
  Expression *get_receiver() const { return _receiver; }
  Expression *get_guard() const { return _guard; }
  Expression *get_owner() const { return _owner; }
  const exp_list_t &get_arguments() const { return _arguments; }

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);

 private:
  // A copy would share the log and free it twice.
  ContainerExpression(const ContainerExpression &);
  ContainerExpression &operator=(const ContainerExpression &);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
