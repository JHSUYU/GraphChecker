#ifdef ENABLE_CONCOLIC

#include "concolic/concolicMngr.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "concolic/reference/containerSupport.hpp"

Expression *MethodSymbolizerHandle::get_primitive_exp(int offset, BasicType type) {
  Expression *exp;
  offset += type2size[type] - 1;
  exp = ConcolicMngr::ctx->get_stack_slot(this->get_caller_stack_begin_offset() + offset);
  if (!exp) {
    switch (type) {
      case T_BYTE:
        exp = new ConExpression(this->get_param<jbyte>(offset));
        break;
      case T_BOOLEAN:
        exp = new ConExpression(this->get_param<jboolean>(offset));
        break;
      case T_INT:
        exp = new ConExpression(this->get_param<jint>(offset));
        break;
      case T_SHORT:
        exp = new ConExpression(this->get_param<jshort>(offset));
        break;
      case T_LONG:
        exp = new ConExpression(this->get_param<jlong>(offset));
        break;
      case T_FLOAT:
        exp = new ConExpression(this->get_param<jfloat>(offset));
        break;
      case T_DOUBLE:
        exp = new ConExpression(this->get_param<jdouble>(offset));
        break;
      case T_CHAR:
        exp = new ConExpression(this->get_param<jchar>(offset));
        break;
      default:
        ShouldNotReachHere();
    }
  }
  return exp;
}

Expression *MethodSymbolizerHandle::get_reference_exp(int offset, oop obj) {
  Expression *exp = ConcolicMngr::ctx->find_stack_slot(
      this->get_caller_stack_begin_offset() + offset);
  if (exp != NULL || obj == NULL || obj->is_array()) return exp;

  SymInstance *sym_inst = ConcolicMngr::ctx->find_sym_inst(obj);
  return sym_inst == NULL ? NULL : sym_inst->get_or_create_ref_exp(obj);
}


void MethodSymbolizerHandle::general_prepare_param(int max_param_num) {
  Method *callee_method = this->get_callee_method();
  int offset = this->get_callee_local_begin_offset();

  if (!callee_method->is_static()) {
    this->general_prepare_param_helper(T_OBJECT, offset, true);
    ++offset;
  }
  // handle this

  ResourceMark rm;
  SignatureStream ss(callee_method->signature());
  while (!ss.at_return_type() && offset < max_param_num) {
    offset = this->general_prepare_param_helper(ss.type(), offset, false);
    ss.next();
    ++offset;
  }
}

int __attribute__((optimize("O0"))) MethodSymbolizerHandle::general_prepare_param_helper(BasicType type,
                                                         int locals_offset, bool is_this) {
  Expression *exp = NULL;
  if (is_java_primitive(type)) {
    exp = this->get_primitive_exp(locals_offset, type);
    locals_offset += type2size[type] - 1;
  } else if (type == T_OBJECT || type == T_ARRAY) {
    oop obj = this->get_param<oop>(locals_offset);
    if (obj != NULL) {
      exp = this->get_reference_exp(locals_offset, obj);
      if (exp != NULL) {
        // Prefer the alias-specific expression propagated by getfield.  This
        // is essential when the concrete receiver is an interned String that
        // intentionally cannot carry a symbolic id in its shared oop header.
      } else if (obj->is_array()) {
        // An array names itself.  It has no SymInstance to ask -- asking
        // read a SymArr through SymInstance's layout and dispatched off the
        // end of its vtable -- and its contents reach a callee through the
        // container state rather than through this operand.  An array with
        // no shadow yet keeps the untracked placeholder the general case
        // below gives it, so observing an argument still allocates nothing.
        exp = obj->is_symbolic() ? ContainerSupport::concrete_value(obj)
                                 : SymInstance::get_exp_of(obj);
      } else if (obj->is_symbolic()) {
        SymInstance *sym_inst = ConcolicMngr::ctx->get_sym_inst(obj);
        exp = sym_inst->get_or_create_ref_exp(obj);
      } else if (is_this) {
        SymInstance *sym_inst = ConcolicMngr::ctx->alloc_sym_inst(obj);
        if (sym_inst != NULL) {
          exp = sym_inst->get_or_create_ref_exp(obj);
        }
      } else {
        exp = ContainerSupport::result_type(obj, T_OBJECT) == T_OBJECT
            ? SymInstance::get_exp_of(obj)
            : ContainerSupport::concrete_value(obj);
      }
    }
  } else {
    tty->print_cr("un_handled type %c", type2char(type));
    ShouldNotCallThis();
  }

  this->get_param_list().push_back(exp);
  return locals_offset;
}

bool MethodSymbolizerHandle::general_check_param_symbolized() {
  Method *callee_method = this->get_callee_method();
  int offset = this->get_callee_local_begin_offset();
  bool recording = false;

  if (!callee_method->is_static()) {
    recording |= this->general_check_param_symbolized_helper(T_OBJECT, offset);
    ++offset;
  }
  ResourceMark rm;
  SignatureStream ss(callee_method->signature());
  // Only when this or key object is symbolized, we symbolize Map
  while (!ss.at_return_type()) {
    recording |= this->general_check_param_symbolized_helper(ss.type(), offset);
    ss.next();
    ++offset;
  }
  return recording;
}

bool MethodSymbolizerHandle::general_check_param_symbolized_helper(BasicType type, int &locals_offset) {
  bool recording = false;
  if (is_java_primitive(type)) {
    locals_offset += type2size[type] - 1;
    Expression *exp = ConcolicMngr::ctx->get_stack_slot(this->get_caller_stack_begin_offset() + locals_offset);
    if (exp != NULL) {
      recording = true;
    }
  } else if (type == T_OBJECT || type == T_ARRAY) {
    oop obj = this->get_param<oop>(locals_offset);
    // Admission must use an expression carried by this invocation, not the
    // mere existence of a SymInstance.  General parameter preparation and
    // identity observation may allocate an instance shadow for an otherwise
    // concrete object; get_reference_exp() would turn that bookkeeping into
    // a fresh InstanceSymbolExp and make unrelated library calls symbolic.
    // A tracked container remains authoritative even when its identity is
    // not present in the current operand-stack slot.
    Expression *exp = ConcolicMngr::ctx->find_stack_slot(
        this->get_caller_stack_begin_offset() + locals_offset);
    SymInstance *instance = obj == NULL || obj->is_array()
        ? NULL : ConcolicMngr::ctx->find_sym_inst(obj);
    SymArr *array = obj != NULL && obj->is_array()
        ? ConcolicMngr::ctx->find_sym_array((arrayOop)obj) : NULL;
    const bool carried =
        (instance != NULL && instance->has_semantic_expression())
        || (array != NULL && array->has_semantic_expression());
    if (exp != NULL || carried || (obj != NULL
        && ConcolicMngr::ctx->find_container_state(obj) != NULL)) {
      recording = true;
    }
    // An operand that carries its own expression is a symbolic value this
    // thread's code reads here -- a String or a box a decode minted outside
    // every region (System.mintLeaf), a container READ's result -- so, as a
    // getfield that yields an expression does, it opens the path-condition
    // gate (by value).  Without it a region whose first symbolic read is
    // such an operand recorded none of its decisions.  A container's state
    // does not open it: a query of it opens the gate through its own read.
    if (carried) ConcolicMngr::ctx->set_pc_admitted(true);
  } else {
    ShouldNotCallThis();
  }

  return recording;
}

#endif
