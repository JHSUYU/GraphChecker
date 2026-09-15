#ifdef ENABLE_CONCOLIC

#include "concolic/fieldTraverser.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "oops/klass.hpp"
#include "utilities/ostream.hpp"
#include "concolic/utils.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "concolic/exp/fieldAccessExpression.hpp"

#include <sstream>

void FieldTraverser::do_recursive() {
  this->_target_depth = 5; // TODO: unlimited
  this->do_recursive_helper();
}

void FieldTraverser::do_once() {
  this->_target_depth = 1;
  this->do_recursive_helper();
}

void FieldTraverser::do_recursive_helper() {
  // Null object-array elements and null object fields are concrete terminal
  // values, not objects to traverse.  Object-array symbolization previously
  // dereferenced them here and crashed the VM.
  if (_obj == NULL) return;
  if (_obj->is_instance()) {
    if (this->before_instance_helper()) {
      InstanceKlass *instanceKlass = (InstanceKlass *)_obj->klass();
      /**
       * Currently, we do not consider static fields
       */
      // instanceKlass->do_local_static_fields(this);
      instanceKlass->do_nonstatic_fields(this);
      this->after_instance_helper();
    }
  } else if (_obj->is_array()) {
    if (this->before_array_helper()) {
      do_array_elements(this);
      this->after_array_helper();
    }
  } else {
    assert(false, "unhandled");
  }
}

void FieldTraverser::do_field(fieldDescriptor *fd) {
  // FIXME: for some object may refer to it self, resulting endless symbolizing.
  if (_depth > _target_depth) {
    return;
  }

  bool need_recursive;
  oop obj;
  {
    ResourceMark rm;
    InstanceKlass *ik = InstanceKlass::cast(this->_obj->klass());

    if (fd->is_static()) { // check if static field
      // tty->print("static ");
      obj =
          ik->java_mirror(); // TODO: check whether we should use `java_mirror`
    } else {
      obj = this->_obj;
    }
    need_recursive = this->do_field_helper(fd, obj);
  }

  if (need_recursive) {
    unsigned offset = fd->offset();

    _depth += 1;
    oop parent_obj = this->_obj;
    this->_obj = obj->obj_field(offset);

    this->do_recursive_helper();
    this->after_field_helper(offset, parent_obj);

    this->_obj = parent_obj;
    _depth -= 1;
  }
}

void FieldTraverser::do_array_elements(FieldTraverser *field_traverser) {
  assert(this->_obj->is_array(), "should be array");
  arrayOop array = (arrayOop)(this->_obj);
  int length = array->length();
  for (int index = 0; index < length; index++) {
    field_traverser->do_array_element(index);
  }
}

void FieldTraverser::do_array_element(int index) {
  // FIXME: for some object may refer to it self, resulting endless symbolizing.
  if (_depth > _target_depth)
    return;

  bool need_recursive;
  arrayOop array_obj = (arrayOop)_obj;
  need_recursive = this->do_element_helper(index, array_obj);

  if (need_recursive) {
    if (_obj->is_objArray()) {
      _depth += 1;
      oop parent_obj = this->_obj;
      this->_obj = ((objArrayOop)_obj)->obj_at(index);

      this->do_recursive_helper();
      this->after_element_helper(index, parent_obj);

      this->_obj = parent_obj;
      _depth -= 1;
    } else {
      assert(false, "non-objarray won't be recursively done for now");
    }
  }
}

void FieldTraverser::print_indent() {
  for (int i = 0; i < _depth; i++) {
    tty->print("    ");
  }
}

/**************************************************
 * FieldSymbolizer
 */

std::string FieldSymbolizer::concatCurrentSymbolicName(fieldDescriptor* fd) {
  ResourceMark rm;
  std::string name = _prefix_lst.back() + "_" + std::string(fd->name()->as_C_string());
  StringUtils::replaceAll(name, "/", "_");
  StringUtils::replaceAll(name, ":", "_");
  StringUtils::replaceAll(name, "$", "__");
  return name;
}

bool FieldSymbolizer::do_field_helper(fieldDescriptor *fd, oop obj) {
  // print_indent();
  // tty->print("---- %d\n", fd->offset());

  ResourceMark rm;
  if (!_selected_field.empty()
      && _selected_field != fd->name()->as_C_string()) {
    return false;
  }
  if (!_selected_holder.empty()
      && (_selected_holder != fd->field_holder()->external_name()
          || _selected_descriptor != fd->signature()->as_C_string())) {
    return false;
  }

  // TODO: directly transfer SymInstance*
  SymInstance *sym_inst;
  SymArr *sym_arr;

  BasicType type = fd->field_type();
  std::string symbolic_name = _selected_field.empty()
      ? concatCurrentSymbolicName(fd) : _prefix_lst.back();
  switch (type) {
  case T_OBJECT: {
    oop fld_oop = obj->obj_field(fd->offset());
    if (fld_oop == NULL) {
      // A selected nullable reference is still a symbolic input when its
      // concrete seed happens to be null.  Keep its field expression on the
      // owner; getfield will propagate that expression to ifnull/ifnonnull.
      // Recursive whole-object symbolization remains unchanged: it cannot
      // traverse a missing child and does not invent one.
      if (!_selected_field.empty()) {
        sym_inst = this->_ctx.find_sym_inst(obj);
        if (sym_inst != NULL) {
          assert(sym_inst == (SymInstance *)this->_sym_refs.back(),
                 "should be equal");
          // Invariant: a field that already carries a symbolic expression is
          // never overwritten by a fresh symbol, and no equation is recorded.
          if (sym_inst->has_sym_exp(fd->offset())) return false;
          Expression *symbol = new FieldSymbolExp(
              sym_inst->get_sym_rid(), symbolic_name, T_OBJECT);
          sym_inst->set_sym_exp(fd->offset(), symbol);
          _ctx.record_path_condition(new OpSymExpression(
              new FieldAccessExpression(
                  sym_inst->get_or_create_ref_exp(obj),
                  obj->klass()->name()->as_C_string(), fd->offset(),
                  T_OBJECT),
              symbol, op_eq, true));
        }
      }
      return false;
    }
    if (fld_oop->klass()->name() == vmSymbols::java_lang_String()) {
      // A String field is an alias, not ownership of the referenced String.
      // In particular, a literal refers to a VM-global intern-table entry.
      // Bind the symbolic String expression to this owner/field edge and let
      // getfield carry it on the operand shadow stack.  This preserves Java
      // identity/content and does not contaminate other aliases.
      sym_inst = this->_ctx.find_sym_inst(obj);
      if (sym_inst == NULL) {
        tty->print_cr("Warning: String field owner has no symbolic shadow");
        return false;
      }
      assert(sym_inst == (SymInstance *)this->_sym_refs.back(),
             "should be equal");
      // Invariant: a field that already carries a symbolic expression is
      // never overwritten by a fresh symbol, and no equation is recorded.
      if (sym_inst->has_sym_exp(fd->offset())) return false;
      Expression *symbol = new StringSymbolExp(
          sym_inst->get_sym_rid(), symbolic_name);
      sym_inst->set_sym_exp(fd->offset(), symbol);
      _ctx.record_path_condition(new OpSymExpression(
          new FieldAccessExpression(
              sym_inst->get_or_create_ref_exp(obj),
              obj->klass()->name()->as_C_string(), fd->offset(), T_OBJECT,
              "Ljava/lang/String;"),
          symbol, op_eq, true));
      return false;
    }
    if (!_selected_field.empty()) {
      sym_inst = this->_ctx.find_sym_inst(obj);
      if (sym_inst == NULL) {
        tty->print_cr("Warning: object field owner has no symbolic shadow");
        return false;
      }
      assert(sym_inst == (SymInstance *)this->_sym_refs.back(),
             "should be equal");
      // Invariant: a field that already carries a symbolic expression is
      // never overwritten by a fresh symbol; the child keeps its own
      // reference expression, and no equation is recorded.
      if (sym_inst->has_sym_exp(fd->offset())) return false;
      SymInstance *field_instance = this->_ctx.get_or_alloc_sym_inst(fld_oop);
      if (field_instance != NULL) {
        Expression *symbol = new FieldSymbolExp(
            field_instance->get_sym_rid(), symbolic_name, T_OBJECT);
        field_instance->set_ref_exp(symbol);
        sym_inst->set_sym_exp(fd->offset(),
            field_instance->get_or_create_ref_exp(fld_oop));
        _ctx.record_path_condition(new OpSymExpression(
            new FieldAccessExpression(
                sym_inst->get_or_create_ref_exp(obj),
                obj->klass()->name()->as_C_string(), fd->offset(),
                T_OBJECT),
            symbol, op_eq, true));
      }
      return false;
    }
    return true;
  }
  case T_ARRAY: {
    arrayOop array_obj = (arrayOop)(obj->obj_field(fd->offset()));
    if (array_obj != NULL) {
      sym_arr = this->_ctx.get_or_alloc_sym_array(array_obj);
    }
    return false;
  }
  default:
    sym_inst = this->_ctx.find_sym_inst(obj);
    if (sym_inst == NULL) {
      tty->print_cr("Warning: primitive field owner has no symbolic shadow");
      return false;
    }
    assert(sym_inst == (SymInstance *)this->_sym_refs.back(),
           "should be equal");
    // Invariant for the recursive and by-name symbolizers: a field that
    // already carries a symbolic expression is never overwritten by a fresh
    // symbol, and no equation is recorded.
    //
    // The exact symbolizer (holder + name + descriptor) is the one explicit
    // mint API, and its caller has already asked getSymbolicFieldExpression
    // whether the field carries an expression of its own: it calls here only
    // when the answer was "no root inside".  What the field holds then is a
    // propagated tree over constants -- typically the value an application
    // write just computed from carrier reads whose every candidate is a
    // recorded constant -- and keeping it would leave the declared source
    // concrete forever, because nothing later can ask again.  So the exact
    // form replaces the shadow.  A field that is a selected shared carrier
    // also publishes the symbol as a version: a later getfield of a carrier
    // resolves over the version store, not over the owner shadow, and the
    // mint has to be the writer that read observes.
    const bool exact = !_selected_holder.empty();
    if (!exact && sym_inst->has_sym_exp(fd->offset())) return false;
    Expression *symbol = new FieldSymbolExp(
        sym_inst->get_sym_rid(), symbolic_name, type);
    sym_inst->set_sym_exp(fd->offset(), symbol);
    // Publish before the equation is built, so the equation can name the
    // version it defines.  The mint is a write: the version published here
    // *is* this symbol, and the projection on the left of the equation is a
    // view of exactly that version.  Ordering is free -- publish reads
    // path_guard(), the region's branch conjunction, while
    // record_path_condition appends to the frame's auxiliary conditions, and
    // neither reads the other.
    // A mint is a symbolic write, whichever symbolizer performed it: it is
    // kept by value and starts this field's log when it is the first symbolic
    // value to reach it.  This used to run only for the exact
    // (holder+name+descriptor) form, which left the by-name and whole-object
    // symbolizers minting values no version named -- so a projection of one
    // of those fields could say nothing about which write it read, which is
    // the whole point of the member below.  laneVM4 showed the shape of that
    // hole: ten FIELD[Long@24] / FIELD[Boolean@24] views of boxed region
    // inputs, every one of them unstamped.
    SharedFieldVersions::Location location(
        sym_inst->get_sym_rid(), fd->offset(),
        SharedFieldVersions::LOC_INSTANCE_FIELD);
    // Folded outside every engine lock, as the store's concurrency contract
    // requires; the same guard a putfield would publish.
    Expression *guard = _ctx.path_guard();
    jlong minted_version = SharedFieldVersions::publish_value(
        location, symbol, guard, true, SharedFieldVersions::VERSION_WRITE);
    std::string minted_version_kind;
    if (minted_version > 0) {
      minted_version_kind = SharedFieldVersions::version_kind_name(
          SharedFieldVersions::VERSION_WRITE);
    }
    _ctx.record_path_condition(new OpSymExpression(
        new FieldAccessExpression(
            sym_inst->get_or_create_ref_exp(obj),
            obj->klass()->name()->as_C_string(), fd->offset(), type,
            std::string(), NULL, NULL, minted_version, minted_version_kind),
        symbol, op_eq, true));
    return false;
  }
}

void FieldSymbolizer::after_field_helper(unsigned offset, oop parent_obj) {
  assert(parent_obj->is_symbolic(), "should be");
  assert(this->_obj->is_symbolic(), "should be");
}

bool FieldSymbolizer::before_instance_helper() {
  if (this->_obj->is_symbolic()) {
    // Selective materialization is intentionally incremental: a region may
    // first symbolize identifier.expiryDate and then identifier.keyId on the
    // same carrier object.  The original early return made every call after
    // the first one a no-op.
    if (!_selected_field.empty()) {
      SymInstance *sym_inst = this->_ctx.get_sym_inst(this->_obj);
      if (sym_inst == NULL)
        return false;
      _sym_refs.push_back(sym_inst);
      ResourceMark rm;
      char *clz_name = this->_obj->klass()->name()->as_C_string();
      tty->inc();
      if (!_prefix_lst.empty()) {
        _prefix_lst.push_back(_prefix_lst.back() + "_" + clz_name);
      } else {
        _prefix_lst.push_back(clz_name);
      }
      return true;
    }
    return false;
  }
  ResourceMark rm;
  SymInstance *sym_inst = this->_ctx.alloc_sym_inst(this->_obj);
  if (sym_inst && sym_inst->need_recursive()) {
    _sym_refs.push_back(sym_inst);

    char * clz_name = this->_obj->klass()->name()->as_C_string();
    tty->inc();
    if (!_prefix_lst.empty()) {
      _prefix_lst.push_back(_prefix_lst.back() + "_" + clz_name);
    } else {
      _prefix_lst.push_back(clz_name);
    }
    return true;
  } else if (sym_inst != NULL
             && this->_obj->klass()->name()
                    == vmSymbols::java_lang_String()) {
    // rename plain String symbolic expressions
    SymString* sym_str_inst = reinterpret_cast<SymString *>(sym_inst);
    if (!_prefix_lst.empty()) {
      sym_str_inst->set_ref_exp(new StringSymbolExp(sym_inst->get_sym_rid(), _prefix_lst.back()));
    }
    return false;
  } else {
    return false;
  }
}

void FieldSymbolizer::after_instance_helper() {
    _sym_refs.pop_back();
    tty->dec();
    _prefix_lst.pop_back();
}

bool FieldSymbolizer::do_element_helper(int index, arrayOop array_obj) {
  ArrayKlass *array_klass = ArrayKlass::cast(array_obj->klass());

  SymArr *sym_arr;
  BasicType element_type;
  element_type = array_klass->element_type();

  switch (element_type) {
  case T_ARRAY:
    // element won't be array(it will be object)
    ShouldNotCallThis();
  case T_OBJECT:
    return true;
  default:
    // the element_type is primitives
    sym_arr = this->_ctx.get_sym_array(array_obj);
    assert(sym_arr == (SymArr *)this->_sym_refs.back(), "should be equal");
    return false;
  }
}

void FieldSymbolizer::after_element_helper(int index, oop parent_obj) {
  /**
   * TODO:
   */
}

bool FieldSymbolizer::before_array_helper() {
  if (this->_obj->is_symbolic())
    return false;

  arrayOop array_obj = (arrayOop)this->_obj;
  SymArr *sym_arr = this->_ctx.alloc_sym_array(array_obj);

  BasicType type = ArrayKlass::cast((array_obj)->klass())->element_type();
  if (!_prefix_lst.empty()) {
    sym_arr->set_ref_exp(new FieldSymbolExp(
        sym_arr->get_sym_rid(), _prefix_lst.back(), T_ARRAY));
  }

  _sym_refs.push_back(sym_arr);
  ResourceMark rm;
  char * arr_clz_name = array_obj->klass()->name()->as_C_string();
  if (!_prefix_lst.empty()) {
    _prefix_lst.push_back(_prefix_lst.back() + arr_clz_name);
  } else {
    _prefix_lst.push_back(arr_clz_name);
  }
  tty->inc();
  return true;
}

void FieldSymbolizer::after_array_helper() {
    _sym_refs.pop_back();
    tty->dec();
    _prefix_lst.pop_back();
}

#endif
