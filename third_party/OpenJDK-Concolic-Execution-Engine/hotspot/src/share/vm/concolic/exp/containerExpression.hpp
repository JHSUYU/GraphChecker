#ifndef SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/expression.hpp"

#include <string>

class ElementWrites;

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
                      Expression *guard = NULL);
  virtual ~ContainerExpression();

  // STATE names a container; every other operation is one the recorder
  // watched happen to it.
  virtual bool is_recorded_container_mutation() {
    return _operation != "STATE";
  }

  virtual ContainerExpression *as_container_expression() { return this; }

  // Whether SIZE of this state is a constant: the STATE root of a Java array
  // allocated with a concrete length, and every WRITE over one, which
  // replaces an element in place.  Decided at construction from the
  // receiver's answer, so asking costs nothing however long the chain is.
  bool has_constant_size() const { return _constant_size; }

  // What a read at the concrete `position` of this state returns, when the
  // chain alone decides it: the state is a Java array's STATE root with a
  // constant length, or a WRITE at a concrete position over such a state.
  // `*stored` is then the value the newest WRITE at `position` stored, or
  // NULL when none did and the element is the root's.  A WRITE at a symbolic
  // position may have replaced any element, so no state above one decides.
  // Decided at construction and answered from the one log the chain's WRITEs
  // share, so a read never walks the chain however long it is.
  bool stored_at(jint position, Expression **stored) const;

  const std::string &get_operation() const { return _operation; }
  const std::string &get_shape() const { return _shape; }
  Expression *get_receiver() const { return _receiver; }
  Expression *get_guard() const { return _guard; }
  const exp_list_t &get_arguments() const { return _arguments; }

  // This same relation, applied to a different receiver.
  //
  // An expression node is immutable once constructed (see expression.hpp), so
  // re-rooting a recorded mutation history onto a stated base rebuilds the
  // chain rather than editing it.  Everything but the receiver is copied,
  // including the guard: a conditionally recorded removal is still
  // conditional when it stands on a different base.
  ContainerExpression *rebuilt_on(Expression *receiver) const;

  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);
};

#endif  // ENABLE_CONCOLIC
#endif  // SHARE_VM_CONCOLIC_EXP_CONTAINEREXPRESSION_HPP
