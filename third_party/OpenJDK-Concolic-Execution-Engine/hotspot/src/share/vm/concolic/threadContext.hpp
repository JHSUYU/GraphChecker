#ifndef SHARE_VM_CONCOLIC_THREADCONTEXT_HPP
#define SHARE_VM_CONCOLIC_THREADCONTEXT_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/exp/containerExpression.hpp"
#include "concolic/methodSymbolizer.hpp"
#include "concolic/pathCondition.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicInstance.hpp"
#include "concolic/shadow/shadowStack.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/handles.hpp"
#include "runtime/jniHandles.hpp"

#include <map>
#include <set>
#include <string>
#include <vector>

class SessionSymbolicHeap;
class StreamTable;

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
 * Condition wrappers for its selected branch guard and branch events.  A nested summary therefore serializes only the nested work;
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
    // System.forceNextConcolicBranch forced this branch: it took `outcome`
    // in place of what its operands decide, `concrete` (1 or 0).
    bool forced;
    jlong concrete;
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
    std::vector<BranchEvent> branch_events;
    // How many of branch_events a read has returned: the runtime reads after
    // every decision, and a whole-frame read each time is quadratic in them.
    size_t branch_events_read;
    // What a model ran on the run's own values though symbolic content
    // reached it, by name and the site of the call (note_model_gap); the
    // region's summary states them and the runtime files each as a
    // DIAGNOSTIC gap.
    std::vector<std::pair<std::string, std::string> > model_gaps;

    RegionFrame() : enter_event_id(0), branch_events_read(0) {}
    ~RegionFrame() {
      branch_path_condition.gc();
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
  bool _pending_branch_active;
  // Drawn from GlobalSymbolicSession::next_event_id(), the one session clock.
  // A decision is ordered against a shared write by comparing this id with
  // that write's fieldVersionId, so the two must be minted by one counter; a
  // per-thread sequence made the comparison meaningless across threads and
  // silently answered "the oldest write" when it was attempted.
  jlong _pending_branch_event_id;
  const ZeroFrame *_pending_branch_owner_frame;
  std::string _pending_branch_site_id;
  int _pending_branch_occurrence;
  // What System.forceNextConcolicBranch asked of the next marker
  // (_next_force), and what that marker binds to its branch
  // (_pending_force): FORCE_NONE, or the arm, 1 jumping and 0 falling
  // through; and, once the branch took it, the concrete answer it overrode.
  int _next_force;
  int _pending_force;
  std::set<sym_rid_t> _switch_maps;
  bool _pending_forced;
  jlong _pending_concrete;
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
  // What an Iterator.remove() names -- a map key, or a list index -- read at
  // the call boundary.
  //
  // The JDK's iterators clear their own record of the element inside remove()
  // (LinkedHashIterator sets `current = null`, ArrayList$Itr sets
  // `lastRet = -1`) before removing it, so by the time the finish hook
  // publishes the mutation the element is already gone.  It is therefore read
  // before the body runs and consumed once by the publisher.
  Expression *_pending_view_removal_argument;
  // The stream pipelines this thread recorded (SymStream), made on first
  // use.
  StreamTable *_streams;

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

  inline jlong get_context_id() const { return _context_id; }
  inline jlong get_owner_java_thread_id() const {
    return _owner_java_thread_id;
  }

  // The conjunction of the current region frame's instrumented, taken branch
  // predicates, or NULL for `true`: a shared version's control guard.
  // Folded here so that a caller can obtain it before taking any engine lock.
  Expression *path_guard();

  // Whether that conjunction is non-empty: at least one instrumented branch
  // has been taken in the CURRENT region frame, so anything this thread does
  // from here is control-dependent on a symbolic decision.  The same notion
  // path_guard() folds, asked without folding it -- this runs on every
  // modelled container call, and no Expression may be built to answer a
  // question about whether one is needed.
  bool path_guarded() const;

  // Whether one branch SITE was a symbolic decision on the current region's
  // path.  A marked branch reaches branch_events only when its predicates are
  // symbolic, admitted and owned by the marking frame, so membership is
  // exactly "that site decided control flow here" -- which is the dynamic
  // half of control dependence.  Site ids are the woven spelling the runtime
  // passes to markConcolicBranch.
  bool branch_site_decided(const std::string &site_id) const;

  inline bool is_aborted() const { return _aborted; }
  inline const std::string &get_abort_reason() const { return _abort_reason; }
  void abort_symbolic_execution(const char *reason);

  // The Soot hook reserves an activation-local event immediately before the
  // original conditional bytecode.  The Zero interpreter finalizes that
  // exact event when the bytecode executes, so Java never has to guess from
  // method names or expression shape.
  jlong mark_branch(const char *site_id, int occurrence);

  // Forcing (System.forceNextConcolicBranch): the runtime asks it of the
  // next marker; the marked conditional bytecode then asks forced_outcome,
  // which answers the forced arm instead of the concrete one only for a
  // pending marker of the current frame whose branch is recorded (`recorded`:
  // the interpreter records it, ConcolicMngr::can_do_concolic), and
  // remembers the concrete answer for the branch's event.  A switch is never
  // forced.
  enum { FORCE_NONE = -1 };
  void force_next_branch(bool jump);
  // A forcing never outlives the marker it was asked of, nor one refused.
  void drop_next_force();
  inline bool forcing() const { return _pending_force != FORCE_NONE; }
  bool forced_outcome(bool concrete, bool recorded);
  // The switch maps (javac's $SwitchMap$, ecj's $SWITCH_TABLE$ arrays) this
  // thread loaded, by session id (SymEnum::loaded_static, table_read).
  void note_switch_map(sym_rid_t array) { _switch_maps.insert(array); }
  bool switch_map(oop array) const {
    return array != NULL && array->get_sym_rid() != NULL_SYM_RID
        && _switch_maps.count(array->get_sym_rid()) > 0;
  }
  // Whether a marked branch executing now records its event and
  // conditions: recording live, admitted, unpaused, in a region.
  bool recording_branches() const;
  void record_branch_condition(Expression *expression, bool outcome,
                               int opcode);
  void record_branch_conditions(const exp_list_t &expressions, bool outcome,
                                int opcode);
  /** The CONCOLIC_THREAD_BRANCH_EVENTS envelope of every event of the
   *  current frame; NULL means no context. */
  static std::string serialize_branch_events(const ThreadContext *context);
  /** The same envelope of the events no read has returned yet, which it
   *  marks read. */
  static std::string serialize_unread_branch_events(ThreadContext *context);
  static std::string serialize_branch_events_from(
      const ThreadContext *context, size_t first);

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

  // This thread's stream pipelines (SymStream); NULL until one is made,
  // unless `create`.
  StreamTable *streams(bool create);

  /**
   * Names a model's statement the region could not have -- a library call
   * run on the run's own values though symbolic content reached it -- at
   * the current call site, once per name and site.  Nothing outside a
   * region.
   */
  void note_model_gap(const std::string &name);
  /** The innermost region's named model gaps, as a JSON array. */
  std::string serialize_model_gaps() const;

  inline bool is_symbolizing_method() {
    return _method_symbolizer.is_symbolizing_method();
  }

  inline bool symbolic_tracking_enabled() const {
    return _s_stack.symbolic_tracking_enabled();
  }

public:
  std::string get_current_code_pos();

  /**
   * One bytecode site, in the JVM's own components.
   *
   * The holder's internal class name, the method's name and descriptor, and
   * the bci -- not a rendered string.  A consumer's site id has its own
   * spelling for the method part, and there has to be exactly one place that
   * renders it; get_current_code_pos() renders a human-readable form for
   * diagnostics and is deliberately not that place.
   */
  struct CodeSite {
    std::string class_name;
    std::string method_name;
    std::string method_descriptor;
    int bci;
    CodeSite() : bci(-1) {}
    bool stated() const { return !class_name.empty(); }
  };

  /**
   * Where this thread stands right now, or false when it cannot be said --
   * no shadow frame (an event published from a VM entry rather than from a
   * bytecode) or no interpreter frame under it.  An unstated site is left
   * absent by every record that carries one: "this event names no site" and
   * "this event happened at bci 0" are different claims.
   */
  bool current_code_site(CodeSite *site);

public:
  /** This object's session identity, naming it if it has none; never
   *  makes it symbolic.  See SessionSymbolicHeap::name_reference. */
  sym_rid_t name_reference(oop obj);

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

  SymArr *get_or_alloc_sym_array(arrayOop array, Expression *length_exp = NULL,
                                 bool named = false);
  SymArr *alloc_sym_array(arrayOop array, Expression *length_exp = NULL);
  SymArr *get_sym_array(sym_rid_t sym_rid);
  inline SymArr *get_sym_array(arrayOop array_obj) {
    return get_sym_array(array_obj->get_sym_rid());
  }
  SymArr *find_sym_array(arrayOop array_obj) const;

  void write_array_element(arrayOop array, int index,
                           Expression *expression,
                           const ElementWord &word = ElementWord());
  Expression *track_container(oop container, const char *shape,
                              const std::string &prefix);
  Expression *container_state(oop container, const char *shape);
  // The one id naming this container and every view of it; NULL_SYM_RID when
  // it has no shadow.  Allocates nothing.
  sym_rid_t canonical_container_id(oop container) const;
  Expression *find_container_state(oop container) const;
  void set_container_state(oop container, Expression *state);
  void forget_container_state(oop container);
  void alias_container(oop derived, oop owner);
  int next_container_position(oop cursor);
  int current_container_position(oop cursor);
  int current_container_index(oop cursor);
  int next_container_removal_position(oop cursor);

  // Begins tracking the element an iterator just returned as a candidate for
  // conditional removal.  Any previously tracked element must already have
  // been disposed by the caller.
  void note_view_removal_argument(Expression *argument) {
    _pending_view_removal_argument = argument;
  }
  Expression *take_view_removal_argument() {
    Expression *argument = _pending_view_removal_argument;
    _pending_view_removal_argument = NULL;
    return argument;
  }

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
