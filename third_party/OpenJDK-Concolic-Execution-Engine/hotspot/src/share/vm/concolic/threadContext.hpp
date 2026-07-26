#ifndef SHARE_VM_CONCOLIC_THREADCONTEXT_HPP
#define SHARE_VM_CONCOLIC_THREADCONTEXT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/jdbc/jdbcMngr.hpp"
#include "concolic/methodSymbolizer.hpp"
#include "concolic/pathCondition.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/reference/array/arrayInternal.hpp"
#include "concolic/shadow/shadowStack.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/handles.hpp"
#include "runtime/jniHandles.hpp"

#include <map>
#include <string>
#include <vector>

class ThreadContext {
  /**
   * TODO: make this hashtable!
   */
  typedef std::map<sym_rid_t, SymRef *> SymStore;
  typedef std::vector<Expression *> SymTmpExpStore;
  // Global JNI handles are stable across moving GC while resolving to the
  // current oop.  Raw arrayOop keys become stale at the first safepoint and
  // cannot safely back concrete-array shadows.
  typedef std::map<jobject, ArrayInternal *> ArrayStore;
  // Some VM-managed objects, most notably interned Strings, must never have
  // their shared oop header marked symbolic.  Keep their per-region symbolic
  // identity behind a GC-stable handle instead.  SymStore remains the sole
  // owner of the SymInstance; this map is only an identity lookup index.
  typedef std::map<jobject, SymInstance *> DetachedObjectStore;
  typedef std::map<sym_rid_t, Expression *> ContainerStateStore;
  typedef std::map<sym_rid_t, int> ContainerPositionStore;

  struct BranchEvent {
    jlong event_id;
    jlong context_id;
    jlong owner_java_thread_id;
    jlong owner_os_thread_id;
    std::string region_id;
    std::string activation_id;
    std::string site_id;
    int occurrence;
    bool outcome;
    int opcode;
    std::string code_position;
    std::vector<int> condition_indices;
  };

private:
  JavaThread *_thread;
  ShadowStack _s_stack;
  SymStore _sym_refs;
  SymTmpExpStore _sym_tmp_exps;
  PathCondition _path_condition;
  MethodSymbolizer _method_symbolizer;
  JdbcMngr _jdbc_mngr;
  ArrayStore _array_store;
  DetachedObjectStore _detached_object_store;
  ContainerStateStore _container_states;
  ContainerPositionStore _container_positions;

  sym_rid_t _sym_rid_counter;
  sym_tmp_id_t _sym_tmp_id_counter;

  bool _path_condition_enabled;
  int _path_condition_pause_depth;
  // Once the Java stack that existed at region start has completely
  // unwound, there is no sound caller frame onto which symbolic values can
  // be rebased.  Keep the context allocated only long enough for a caller to
  // query/finish it (or for JavaThread::exit to release it), but make every
  // symbolic operation fail closed.
  bool _aborted;
  std::string _abort_reason;
  std::string _region_id;
  std::string _activation_id;
  jlong _context_id;
  jlong _owner_java_thread_id;
  jlong _owner_os_thread_id;
  jlong _branch_sequence;
  bool _pending_branch_active;
  jlong _pending_branch_event_id;
  const ZeroFrame *_pending_branch_owner_frame;
  std::string _pending_branch_site_id;
  int _pending_branch_occurrence;
  std::vector<BranchEvent> _branch_events;
//  std::set<oop> _allocated_objs;
public:
  ThreadContext(JavaThread *jt, jlong context_id);
  ~ThreadContext();

  inline JavaThread *get_thread() { return _thread; }

  inline void symbolize(Handle handle) { this->symbolize_recursive(handle()); }
  inline void symbolize(Handle handle, std::string prefix) { this->symbolize_recursive(handle(), prefix); }
  void symbolize_field(Handle handle, std::string field_name,
                       std::string prefix);
  inline void symbolize_method(const char *class_name,
                               const char *method_name) {
    _method_symbolizer.add_method(class_name, method_name);
  }
  inline void record_stmt_obj(oop stmt, oop obj) {
    _jdbc_mngr.record_stmt_obj_pair(stmt, obj);
  }
  inline void record_persistent_obj(oop obj) {
    _jdbc_mngr.record_persistent_obj(obj);
  }

  PathCondition &get_path_condition();

  inline void set_region_metadata(const char *region_id,
                                  const char *activation_id) {
    _region_id = region_id == NULL ? "" : region_id;
    _activation_id = activation_id == NULL ? "" : activation_id;
  }

  inline const std::string &get_region_id() const { return _region_id; }
  inline const std::string &get_activation_id() const {
    return _activation_id;
  }

  inline jlong get_context_id() const { return _context_id; }

  inline bool is_aborted() const { return _aborted; }
  inline const std::string &get_abort_reason() const { return _abort_reason; }
  void abort_symbolic_execution(const char *reason);

  // The Soot hook reserves an activation-local event immediately before the
  // original conditional bytecode.  The Zero interpreter finalizes that
  // exact event when the bytecode executes, so Java never has to guess from
  // method names or expression shape.
  jlong mark_branch(const char *site_id, int occurrence);
  void record_branch_condition(Expression *expression, bool outcome,
                               int opcode);
  void record_branch_conditions(const exp_list_t &expressions, bool outcome,
                                int opcode);
  std::string get_branch_events() const;

  void set_pc_enabled(bool pathConditionEnabled);
  int pause_path_condition_recording();
  int resume_path_condition_recording();
  inline int path_condition_pause_depth() const {
    return _path_condition_pause_depth;
  }

public:
  void __attribute__((optimize("O0"))) printSymExp(oop obj) {
    obj->print();
    SymInstance *sym_inst = this->find_sym_inst(obj);
    tty->print_cr("is symbolic: %d", sym_inst == NULL ? 0 : 1);
    if (sym_inst != NULL) {
      sym_inst->print();
    }
  }

  inline JdbcMngr &get_jdbc_mngr() { return _jdbc_mngr; }

  inline MethodSymbolizer &get_method_symbolizer() {
    return _method_symbolizer;
  }

  inline bool is_symbolizing_method() {
    return _method_symbolizer.is_symbolizing_method();
  }

  inline bool symbolic_tracking_enabled() const {
    return _s_stack.symbolic_tracking_enabled();
  }

  inline const ArrayStore &get_array_store() const {
    return _array_store;
  }

  inline bool has_callback() const {
    return _method_symbolizer.has_callback();
  }

public:
  std::string get_current_code_pos();
  std::string get_code_pos_for_first(const std::string &str);

public:
  SymInstance *get_or_alloc_sym_inst(oop obj);
  SymInstance *alloc_sym_inst(oop obj);
  inline SymInstance *get_sym_inst(oop obj) {
    if (obj != NULL && obj->is_array() && obj->is_symbolic()) {
      return get_sym_inst(obj->get_sym_rid());
    }
    SymInstance *instance = find_sym_inst(obj);
    guarantee(instance != NULL,
              "Unexpected null symbolic object lookup");
    return instance;
  }

  SymInstance *get_sym_inst(sym_rid_t sym_rid);
  SymInstance *find_sym_inst(oop obj) const;
  bool requires_detached_object_shadow(oop obj) const;

  SymArr *get_or_alloc_sym_array(arrayOop array, Expression *length_exp = NULL);
  SymArr *alloc_sym_array(arrayOop array, Expression *length_exp = NULL);
  SymArr *get_sym_array(sym_rid_t sym_rid);
  inline SymArr *get_sym_array(arrayOop array_obj) {
    return get_sym_array(array_obj->get_sym_rid());
  }
  SymArr *find_sym_array(arrayOop array_obj) const;

  sym_tmp_id_t get_next_sym_tmp_id(Expression *sym_exp);
  void detach_tmp_exp(sym_tmp_id_t sym_tmp_id);

  inline void __attribute__((optimize("O0"))) record_path_condition(Expression *sym_exp) {
    if (_aborted || !_path_condition_enabled
        || _path_condition_pause_depth > 0) {
      return;
    }

    _path_condition.add(sym_exp);
  }

  ArrayInternal* get_or_create_array_internal(arrayOop oop);
  ArrayInternal* find_array_internal(arrayOop oop) const;
  void store_array_element_shadow(arrayOop array, int index,
                                  Expression *expression,
                                  const char *provenance);
  void prepare_arraycopy_shadow(arrayOop destination);
  void arraycopy_shadow(arrayOop source, int source_pos,
                        arrayOop destination, int destination_pos,
                        int length);
  void invalidate_arraycopy_shadow(arrayOop destination,
                                   int destination_pos, int length);
  Expression *container_state(oop container, const char *shape);
  Expression *find_container_state(oop container) const;
  void set_container_state(oop container, Expression *state);
  int next_container_position(oop cursor);
public:
  inline ShadowStack &get_shadow_stack() { return _s_stack; }
  /**
   * this will generate a new tmp_id; use it when `sym_exp` is newly
   * calculated, which doesn't have `sym_rid` and `index`
   */
  void set_stack_slot(int offset, Expression *sym_exp);
  void set_stack_slot_if_possible(int offset, Expression *sym_exp);
  void set_stack_value_if_possible(int anchor_offset, int slot_count,
                                   Expression *sym_exp);
  void set_stack_slot(int offset, Expression *sym_exp, sym_rid_t sym_rid,
                      int index);

  inline Expression *get_stack_slot(int offset) {
    return this->get_stack_entry(offset).exp;
  }

  inline Expression *find_stack_slot(int offset) {
    return offset < 0 || offset >= this->get_last_stack().size()
        ? NULL : this->get_stack_entry(offset).exp;
  }

  inline Expression *get_and_detach_stack_slot(int offset) {
    return this->get_and_detach_stack_entry(offset).exp;
  }

  inline Expression *get_local_slot(int offset) {
    return this->get_last_local().get_slot(offset);
  }

  inline void set_local_slot(int offset, Expression *exp) {
    this->get_last_local().set_slot(offset, exp);
  }

  /**
   * TODO: document when to clear the stack
   */
  void clear_stack_slot(int offset);
  void clear_stack_words(int first_offset, int slot_count);
  // A category-1 value owns its anchor only.  A category-2 value owns the
  // anchor plus the immediately preceding NULL companion word.  These APIs
  // make that layout explicit for every value-producing/consuming bytecode.
  void clear_stack_value(int anchor_offset, int slot_count);
  void set_stack_value(int anchor_offset, int slot_count, Expression *exp);
  void set_stack_value(int anchor_offset, int slot_count, Expression *exp,
                       sym_rid_t sym_rid, int index);
  void clear_operand_stack();
  void copy_local_value_to_stack(int local_anchor_offset,
                                 int stack_anchor_offset, int slot_count);
  void move_stack_value_to_local(int stack_anchor_offset,
                                 int local_anchor_offset, int slot_count);
  void copy_stack_slot(int src_off, int dst_off, int size);
  void swap_two_stack_slot(int off1, int off2);
  void copy_entry_from_local_to_stack(int local_offset, int stack_offset);
  void copy_entry_from_stack_to_local(int stack_offset, int local_offset);
  void symbolize_recursive(oop obj);
  void symbolize_recursive(oop obj, std::string prefix);
  void cancel_pending_branch();
  void cancel_pending_branch_for_frame(const ZeroFrame *owner_frame);

private:
  inline ShadowTable &get_last_stack() {
    return this->get_shadow_stack().get_last_frame().get_opr_stack();
  }

  inline ShadowTable &get_last_local() {
    return this->get_shadow_stack().get_last_frame().get_local_tbl();
  }

  inline ShadowTable::Entry &get_stack_entry(int offset) {
    return this->get_last_stack().get_entry(offset);
  }

  inline ShadowTable::Entry &get_local_entry(int offset) {
    return this->get_last_local().get_entry(offset);
  }

  inline ShadowTable::Entry &get_and_detach_stack_entry(int offset) {
    ShadowTable::Entry &entry = this->get_last_stack().get_entry(offset);
    if (entry.exp) {
      if (entry.sym_rid == NULL_SYM_RID) {
        this->detach_tmp_exp(entry.index);
      }
    }
    return entry;
  }

private:

  void set_sym_ref(sym_rid_t sym_rid, SymRef *sym_ref) {
    _sym_refs.insert(std::make_pair(sym_rid, sym_ref));
  }

  sym_rid_t get_next_sym_rid() {
    sym_rid_t ret = _sym_rid_counter++;
    guarantee(ret < MAX_SYM_RID, "sym_rid limitted");
    return ret;
  }

  inline void init_sym_rid_counter() { _sym_rid_counter = 1; }
  inline void init_sym_tmp_id_counter() {
    /**
     * tmp_id start from 1.
     * Therefore, we push a placeholder.
     */
    _sym_tmp_exps.push_back(NULL);
    _sym_tmp_id_counter = 1;
  }

public:
  void print();
  void print_stack_trace();
  static void memory_leak_check();
};

#endif

#endif // SHARE_VM_CONCOLIC_THREADCONTEXT_HPP
