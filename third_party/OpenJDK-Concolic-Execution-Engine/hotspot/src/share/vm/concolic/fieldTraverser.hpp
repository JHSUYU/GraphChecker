#ifndef SHARE_VM_CONCOLIC_FIELDTRAVERSER_HPP
#define SHARE_VM_CONCOLIC_FIELDTRAVERSER_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/threadContext.hpp"
#include "memory/resourceArea.hpp"
#include "oops/instanceKlass.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/fieldDescriptor.hpp"
#include "runtime/handles.hpp"
#include "utilities/debug.hpp"

#include <stdio.h>
#include <vector>

class FieldTraverser : public FieldClosure {
private:
  int _depth, _target_depth;

protected:
  oop _obj;

  FieldTraverser(oop obj) : _obj(obj), _depth(1) {}
  void print_indent();

public:
  // recursive functions
  void do_recursive();
  void do_once();

private:
  // A traverser that declares no interest in fields or elements descends into
  // neither.  These have to say so: falling off the end of a bool function is
  // undefined, and a compiler that turns that into a trap aborts the VM at the
  // first traversal rather than at the first subclass that forgot to override.
  virtual bool do_field_helper(fieldDescriptor *fd, oop obj) { return false; }
  virtual bool do_element_helper(int index, arrayOop array_obj) { return false; }
  virtual void after_field_helper(unsigned offset, oop temp_obj) {}
  virtual void after_element_helper(int index, oop temp_obj) {}
  virtual bool before_instance_helper() { return true; }
  virtual void after_instance_helper() {}
  virtual bool before_array_helper() { return true; }
  virtual void after_array_helper() {}

  void do_field(fieldDescriptor *fd);
  void do_array_element(int index);
  void do_recursive_helper();
  void do_array_elements(FieldTraverser *field_traverser);
};

class FieldSymbolizer : public FieldTraverser {
private:
  ThreadContext &_ctx;
  std::vector<SymRef *> _sym_refs;
  std::vector<std::string> _prefix_lst;
  std::string _selected_holder;
  std::string _selected_field;
  std::string _selected_descriptor;

public:
  FieldSymbolizer(oop obj, ThreadContext &ctx)
      : FieldTraverser(obj), _ctx(ctx) {}
  FieldSymbolizer(oop obj, ThreadContext &ctx, std::string prefix)
      : FieldTraverser(obj), _ctx(ctx) {
    _prefix_lst.push_back(prefix);
  }
  FieldSymbolizer(oop obj, ThreadContext &ctx, std::string prefix,
                  std::string selected_field)
      : FieldTraverser(obj), _ctx(ctx), _selected_field(selected_field) {
    _prefix_lst.push_back(prefix);
  }
  FieldSymbolizer(
      oop obj, ThreadContext &ctx, std::string prefix,
      std::string selected_holder, std::string selected_field,
      std::string selected_descriptor)
      : FieldTraverser(obj), _ctx(ctx),
        _selected_holder(selected_holder), _selected_field(selected_field),
        _selected_descriptor(selected_descriptor) {
    _prefix_lst.push_back(prefix);
  }
protected:
  bool do_field_helper(fieldDescriptor *fd, oop obj);
  bool do_element_helper(int index, arrayOop array_obj);
  void after_field_helper(unsigned offset, oop tem_obj);
  void after_element_helper(int index, oop tem_obj);
  virtual bool before_instance_helper();
  virtual void after_instance_helper();
  virtual bool before_array_helper();
  virtual void after_array_helper();

  std::string concatCurrentSymbolicName(fieldDescriptor* fd);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_FIELDTRAVERSER_HPP
