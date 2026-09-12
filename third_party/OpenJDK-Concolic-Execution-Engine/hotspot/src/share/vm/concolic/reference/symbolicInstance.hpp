#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICINSTANCE_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICINSTANCE_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/reference/symbolicReference.hpp"
#include "oops/oop.inline.hpp"
#include "utilities/debug.hpp"

#include <pthread.h>

#include <map>
#include <set>
#include <stdio.h>

class SymInstance : public SymRef {
private:
  bool _demand_symbolic_fields;
  bool _semantic_expression;
  std::set<int> _written_fields;

protected:
  /**
   * Guards this shadow's per-instance field containers: _written_fields here,
   * SymObj::_exps and SymBigDecimal::_internal_fields in the subclasses.  See
   * the field-shadow write policy in sessionSymbolicHeap.hpp -- the policy is
   * last-writer-wins, and this lock is what makes that literally true rather
   * than a description of undefined behaviour.
   *
   * It is a leaf lock in every sense that matters: nothing that can block runs
   * inside it, no Expression is constructed under it, and it is never held
   * while the session heap lock is taken.  Order, when both are involved, is
   * heap -> instance -> arena.
   */
  mutable pthread_mutex_t _field_mutex;

  class FieldLock {
  public:
    FieldLock(const SymInstance *owner) : _owner(owner) {
      pthread_mutex_lock(&_owner->_field_mutex);
    }
    ~FieldLock() { pthread_mutex_unlock(&_owner->_field_mutex); }
  private:
    const SymInstance *_owner;
  };

public:
  SymInstance(sym_rid_t sym_rid)
      : SymRef(sym_rid), _demand_symbolic_fields(false),
        _semantic_expression(false) {
    pthread_mutex_init(&_field_mutex, NULL);
  }
  virtual ~SymInstance() { pthread_mutex_destroy(&_field_mutex); }

  inline void enable_demand_symbolic_fields() {
    _demand_symbolic_fields = true;
  }

  inline bool demand_symbolic_fields_enabled() const {
    return _demand_symbolic_fields;
  }

  // An allocated shadow only gives the VM a place to store identity and
  // field metadata.  It does not by itself make every call receiving that
  // object symbolic.  Explicit inputs and derived results mark the attached
  // expression as semantic; default InstanceSymbolExp identities do not.
  inline void mark_semantic_expression() {
    _semantic_expression = true;
  }

  inline void clear_semantic_expression() {
    _semantic_expression = false;
  }

  inline bool has_semantic_expression() const {
    return _semantic_expression;
  }

  inline void mark_field_written(int field_offset) {
    FieldLock guard(this);
    _written_fields.insert(field_offset);
  }

  inline bool field_written(int field_offset) const {
    FieldLock guard(this);
    return _written_fields.find(field_offset) != _written_fields.end();
  }

  virtual Expression *get(int field_offset) { return NULL; }
  virtual Expression *create_ref_exp(oop obj) {
    return new InstanceSymbolExp(obj);
  }
  virtual Expression *get_or_create_ref_exp(oop obj) {
    Expression *exp = get_ref_exp();
    if (exp == NULL) {
      bool was_semantic = has_semantic_expression();
      exp = create_ref_exp(obj);
      set_ref_exp(exp);
      if (!was_semantic) clear_semantic_expression();
    }
    return exp;
  }
  virtual Expression *get_ref_exp() = 0;

  virtual void set_ref_exp(Expression *) { ShouldNotCallThis(); }

  virtual void init_sym_exp(int field_offset, Expression *exp) {
    ShouldNotCallThis();
  }
  virtual void set_sym_exp(int field_offset, Expression *exp) = 0;
  // True when this shadow already carries an expression for the field.  The
  // field symbolizer asks this before minting a fresh symbol: an expression
  // that reached the field by propagation is never overwritten by one.
  virtual bool has_sym_exp(int field_offset) = 0;

  virtual bool need_recursive() { return true; }

  inline void init_sym_exp(int field_offset, BasicType type) {
    return init_sym_exp(field_offset, new FieldSymbolExp(this->get_sym_rid(),
                                                         field_offset, type));
  }

  inline void init_sym_exp(int field_offset, BasicType type, std::string name) {
    return init_sym_exp(field_offset, new FieldSymbolExp(this->get_sym_rid(),
                                                         name, type));
  }

  static Expression* get_exp_of(oop obj);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICINSTANCE_HPP
