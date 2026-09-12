#ifndef SHARE_VM_CONCOLIC_THREADCONTEXT_HPP
#define SHARE_VM_CONCOLIC_THREADCONTEXT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/methodSymbolizer.hpp"
#include "concolic/pathCondition.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/shadow/shadowStack.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/handles.hpp"
#include "runtime/jniHandles.hpp"

#include <map>
#include <string>
#include <vector>

class SessionSymbolicHeap;

/**
 * One Java thread's symbolic execution state: its shadow frames, operand
 * stack, locals, path condition, branch events and region stack.
 *
 * Everything here describes how *this* thread reached a value.  What a value
 * *is* -- object shadows, container states, expressions, ids -- belongs to the
 * session, and this class reaches it through heap() rather than owning it.
 * That is what makes a region exit release only this thread's execution state.
 *
 * Regions form a stack, not a scalar.  A thread that is already attached can
 * open another region inside the one it is running -- a producer region inside
 * a driver region, a handler region inside an RPC region -- and the identity
 * that labels branch events and summaries is the innermost one.  Only the
 * outermost exit ends this thread's participation in the session.
 *
 * The complete path condition stays singular and thread-scoped so its indices
 * remain stable across nested regions.  Each region frame separately owns the
 * Condition wrappers for its selected branch guard, auxiliary constraints and
 * branch events.  A nested summary therefore serializes only the nested work;
 * after it is popped, the enclosing summary contains only enclosing work.
 */
class ThreadContext {
private:
  struct BranchEvent {
    jlong event_id;
    std::string site_id;
    int occurrence;
    bool outcome;
    int opcode;
    std::string code_position;
    std::vector<int> condition_indices;
  };

  struct RegionFrame {
    std::string region_id;
    std::string task_id;
    // Stable session-local identity of this region occurrence.  It is used to
    // associate a published writer with its local case; it carries no order.
    jlong enter_event_id;
    // Region-local wrappers around session-owned expressions.  The complete
    // thread path below remains the authority for their stable global indices.
    PathCondition branch_path_condition;
    PathCondition auxiliary_path_condition;
    std::vector<int> auxiliary_path_condition_indices;
    std::vector<BranchEvent> branch_events;

    RegionFrame() : enter_event_id(0) {}
    ~RegionFrame() {
      branch_path_condition.gc();
      auxiliary_path_condition.gc();
    }
  };

private:
  JavaThread *_thread;
  ShadowStack _s_stack;
  // Complete, monotonically indexed history for range queries.  RegionFrame
  // stores the selected local views used by summaries and shared-write guards.
  PathCondition _path_condition;
  MethodSymbolizer _method_symbolizer;

  // The session's shadow heap.  Fails closed if the session that owns this
  // context has already been torn down.
  SessionSymbolicHeap &heap() const;


  bool _path_condition_enabled;
  // Region capture begins only after the first selected input is
  // materialized.  This authority is independent of the Webridge pruner,
  // which temporarily toggles _path_condition_enabled around library code.
  bool _path_condition_admitted;
  int _path_condition_pause_depth;
  // Once the Java stack that existed at region start has completely
  // unwound, there is no sound caller frame onto which symbolic values can
  // be rebased.  Keep the context allocated only long enough for a caller to
  // query/finish it (or for JavaThread::exit to release it), but make every
  // symbolic operation fail closed.
  bool _aborted;
  std::string _abort_reason;
  std::vector<RegionFrame *> _region_stack;
  jlong _context_id;
  jlong _owner_java_thread_id;
  jlong _owner_os_thread_id;
  jlong _branch_sequence;
  bool _pending_branch_active;
  jlong _pending_branch_event_id;
  const ZeroFrame *_pending_branch_owner_frame;
  std::string _pending_branch_site_id;
  int _pending_branch_occurrence;
//  std::set<oop> _allocated_objs;

  // One in-flight conditional container removal, assembled across one
  // iterator step:
  //   it.next() names the element being visited (its map key);
  //   a marked symbolic branch records the controlling predicate;
  //   the element is disposed either by it.remove() (the removal fired: the
  //     guard is recorded as-is, concretely true) or by the following
  //     it.hasNext()/it.next() (it did not: the guard is recorded negated,
  //     concretely false) -- so the guard's concrete truth always equals
  //     whether the key is concretely gone, which keeps replay sound.
  // Only a *marked* branch arms it, so an ordinary iterator remove with no
  // controlling symbolic branch still records an unconditional REMOVE_AT.
  // Expressions are session-arena owned, never GC-managed oops, so holding
  // them across the Java calls of one loop iteration is safe.
  struct PendingConditionalRemoval {
    bool active;
    Expression *key;    // the entry's key (the map key, not the ordinal)
    Expression *guard;  // the marked branch predicate, or NULL until it fires
    PendingConditionalRemoval() : active(false), key(NULL), guard(NULL) {}
  };
  PendingConditionalRemoval _pending_conditional_removal;

public:
  ThreadContext(JavaThread *jt, jlong context_id);
  ~ThreadContext();

  inline JavaThread *get_thread() { return _thread; }

  inline void symbolize(Handle handle) { this->symbolize_recursive(handle()); }
  inline void symbolize(Handle handle, std::string prefix) { this->symbolize_recursive(handle(), prefix); }
  void symbolize_field(Handle handle, std::string field_name,
                       std::string prefix);
  void symbolize_exact_field(
      Handle owner, std::string declaring_class, std::string field_name,
      std::string descriptor, std::string prefix);
  PathCondition &get_path_condition();

  // Opens a region on this thread.  The first push is the thread's outermost
  // region; every later one nests inside the region that is currently
  // innermost.
  void push_region(const char *region_id, const char *task_id);
  // Closes the innermost region and returns the remaining depth.  Zero means
  // this thread has left every region and its membership can be released.
  int pop_region();
  inline int region_depth() const { return (int) _region_stack.size(); }

  // The innermost region's identity, or empty when this thread is in none.
  const std::string &get_region_id() const;
  const std::string &get_task_id() const;
  void set_region_enter_event(jlong event_id);
  jlong region_enter_event() const;

  /**
   * One half-open index range of this thread's path condition, as its
   * conditions -- the CONCOLIC_PATH_CONDITION_RANGE envelope.
   *
   * The window's conjunction is not inlined beside them.  It is the left fold
   * of `conditions` in index order and nothing else, so a second copy of it in
   * the same document restated every condition of the window twice.
   * `conditionCount` gives the window's exact length, so an empty window is
   * distinguishable from an omitted one without fetching anything.
   *
   * A NULL context is the "nothing is attached to this thread" answer and is
   * written by this same function rather than by a hand-kept literal
   * elsewhere: the two used to disagree about which members exist, so a
   * reader had to special-case the shape it got.
   */
  static std::string serialize_path_condition_range(ThreadContext *context,
                                                    int start, int end);
  std::string get_path_condition_range(int start, int end) {
    return serialize_path_condition_range(this, start, end);
  }

  /**
   * Every admitted non-branch solver constraint of the current region frame,
   * paired with its position in the thread's full path condition.  This is the
   * case-level counterpart of path_guard(): versions carry only the current
   * region's control guard, while its result carries these relations once.
   */
  std::string get_auxiliary_path_conditions();

  inline jlong get_context_id() const { return _context_id; }
  inline jlong get_owner_java_thread_id() const {
    return _owner_java_thread_id;
  }

  // The conjunction of the current region frame's instrumented, taken branch
  // predicates, or NULL for `true`.  This deliberately excludes auxiliary
  // solver constraints retained in get_path_condition(); the region case
  // carries those once, while a shared version needs only its control guard.
  // Folded here so that a caller can obtain it before taking any engine lock.
  Expression *path_guard();

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
  /** The CONCOLIC_THREAD_BRANCH_EVENTS envelope; NULL means no context. */
  static std::string serialize_branch_events(const ThreadContext *context);
  std::string get_branch_events() const {
    return serialize_branch_events(this);
  }

  void set_pc_admitted(bool pathConditionAdmitted);
  int pause_path_condition_recording();
  int resume_path_condition_recording();
  inline int path_condition_pause_depth() const {
    return _path_condition_pause_depth;
  }

public:
  inline MethodSymbolizer &get_method_symbolizer() {
    return _method_symbolizer;
  }

  inline bool is_symbolizing_method() {
    return _method_symbolizer.is_symbolizing_method();
  }

  inline bool symbolic_tracking_enabled() const {
    return _s_stack.symbolic_tracking_enabled();
  }

public:
  std::string get_current_code_pos();
  std::string get_code_pos_for_first(const std::string &str);

public:
  SymInstance *get_or_alloc_sym_inst(oop obj);
  SymInstance *alloc_sym_inst(oop obj);
  inline SymInstance *get_sym_inst(oop obj) {
    // An array's shadow is a SymArr, which shares only SymRef with
    // SymInstance.  Handing one back here reads one object through the
    // other's layout, and the first virtual call walks off the end of
    // SymArr's four-entry vtable into whatever the linker put after it --
    // a jump into an unrelated member function, on the shadow of a live
    // array.  Every allocator here already refuses arrays
    // (alloc_sym_inst, find_sym_inst); this is the one accessor that did
    // not, so say so rather than return something that only looks like an
    // instance.
    guarantee(obj == NULL || !obj->is_array(),
              "An array has no symbolic instance; ask for its SymArr");
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

  inline void __attribute__((optimize("O0"))) record_path_condition(Expression *sym_exp) {
    if (_aborted || !_path_condition_enabled || !_path_condition_admitted
        || _path_condition_pause_depth > 0 || _region_stack.empty()) {
      return;
    }

    const int full_index = _path_condition.add(sym_exp);
    RegionFrame *frame = _region_stack.back();
    frame->auxiliary_path_condition.add(sym_exp);
    frame->auxiliary_path_condition_indices.push_back(full_index);
  }

  void write_array_element(arrayOop array, int index,
                           Expression *expression);
  Expression *track_container(oop container, const char *shape,
                              const std::string &prefix);
  Expression *container_state(oop container, const char *shape);
  // The one id naming this container and every view of it; NULL_SYM_RID when
  // it has no shadow.  Allocates nothing.
  sym_rid_t canonical_container_id(oop container) const;
  Expression *find_container_state(oop container) const;
  void set_container_state(oop container, Expression *state);
  void alias_container(oop derived, oop owner);
  int next_container_position(oop cursor);
  int current_container_position(oop cursor);
  int current_container_index(oop cursor);
  int next_container_removal_position(oop cursor);

  // Begins tracking the element an iterator just returned as a candidate for
  // conditional removal.  Any previously tracked element must already have
  // been disposed by the caller.
  void begin_conditional_removal(Expression *key) {
    _pending_conditional_removal.active = true;
    _pending_conditional_removal.key = key;
    _pending_conditional_removal.guard = NULL;
  }
  // Records the controlling predicate of the tracked element.  Only the first
  // marked branch after it.next() is taken, and a NULL/unmodeled predicate
  // leaves the element unguarded (so it stays an unconditional REMOVE_AT).
  void note_conditional_removal_guard(Expression *guard) {
    if (_pending_conditional_removal.active
        && _pending_conditional_removal.guard == NULL && guard != NULL) {
      _pending_conditional_removal.guard = guard;
    }
  }
  bool conditional_removal_active() const {
    return _pending_conditional_removal.active;
  }
  bool conditional_removal_is_guarded() const {
    return _pending_conditional_removal.active
        && _pending_conditional_removal.guard != NULL;
  }
  Expression *conditional_removal_key() const {
    return _pending_conditional_removal.key;
  }
  Expression *conditional_removal_guard() const {
    return _pending_conditional_removal.guard;
  }
  void clear_conditional_removal() {
    _pending_conditional_removal.active = false;
    _pending_conditional_removal.key = NULL;
    _pending_conditional_removal.guard = NULL;
  }

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

public:
};

#endif

#endif // SHARE_VM_CONCOLIC_THREADCONTEXT_HPP
