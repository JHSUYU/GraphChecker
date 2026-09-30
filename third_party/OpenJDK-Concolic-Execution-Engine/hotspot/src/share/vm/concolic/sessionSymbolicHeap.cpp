#ifdef ENABLE_CONCOLIC

#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/symbolicBigDecimal.hpp"
#include "concolic/reference/symbolicObject.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicString.hpp"
#include "concolic/reference/symbolicStringBuilder.hpp"
#include "concolic/utils.hpp"
#include "runtime/handles.hpp"
#include "runtime/jniHandles.hpp"
#include "runtime/thread.hpp"
#include "utilities/ostream.hpp"

SessionSymbolicHeap::SessionSymbolicHeap() {
  pthread_mutex_init(&_mutex, NULL);
}

SessionSymbolicHeap::~SessionSymbolicHeap() {
  // Deliberately unlocked.  The session tears down only after its last member
  // has detached, so nothing else can reach these containers; and
  // JNIHandles::destroy_global below takes a HotSpot Mutex, which rule 2 of
  // the concurrency contract forbids inside a critical section.
  _container_states.clear();

  // DetachedObjectStore does not own its SymInstance values.  Release its GC
  // roots before deleting the instances from SymStore so no stale oop can be
  // resolved during the remaining teardown.
  DetachedObjectStore::iterator detached_it;
  for (detached_it = _detached_object_store.begin();
       detached_it != _detached_object_store.end(); ++detached_it) {
    guarantee(detached_it->second != NULL,
              "Detached symbolic object should not be null");
    JNIHandles::destroy_global(detached_it->first);
  }
  _detached_object_store.clear();

  for (SymStore::iterator iter = _sym_refs.begin(); iter != _sym_refs.end();
       ++iter) {
    guarantee(iter->second != NULL, "Sym instance should not be null");
    delete iter->second;
  }
  _sym_refs.clear();
  pthread_mutex_destroy(&_mutex);
}

sym_rid_t SessionSymbolicHeap::get_next_sym_rid() {
  return GlobalSymbolicSession::next_sym_rid();
}

sym_rid_t SessionSymbolicHeap::name_reference(oop obj) {
  if (obj == NULL) return NULL_SYM_RID;
  sym_rid_t existing = obj->get_sym_rid();
  if (existing != NULL_SYM_RID) return existing;
  // Minted outside the lock, as the shadow allocators do: next_sym_rid takes
  // no engine lock, and an id lost to a race costs one id, not correctness.
  sym_rid_t sym_rid = get_next_sym_rid();
  HeapLock guard(this);
  // Under the same lock the allocators publish a header id under, so a
  // concurrent allocation either sees this id and reuses it or wins the race
  // and this thread reads its id back here.
  existing = obj->get_sym_rid();
  if (existing != NULL_SYM_RID) return existing;
  obj->set_named_sym_rid(sym_rid);
  return sym_rid;
}

sym_rid_t SessionSymbolicHeap::canonical_container_id_locked(
    sym_rid_t id) const {
  ContainerOwnerStore::const_iterator owner = _container_owners.find(id);
  return owner == _container_owners.end() ? id : owner->second;
}

Expression *SessionSymbolicHeap::track_container(
    oop container, const char *shape, const std::string &prefix) {
  if (container == NULL || shape == NULL || prefix.empty()) return NULL;
  Expression *existing = find_container_state(container);
  if (existing != NULL) return existing;

  if (container->is_array()) {
    SymArr *array = get_or_alloc_sym_array((arrayOop)container);
    if (array == NULL) return NULL;
    array->set_ref_exp(new FieldSymbolExp(
        array->get_sym_rid(), prefix, T_ARRAY));
  } else {
    SymInstance *instance = get_or_alloc_sym_inst(container);
    if (instance == NULL) return NULL;
    instance->set_ref_exp(new FieldSymbolExp(
        instance->get_sym_rid(), prefix, T_OBJECT));
  }
  return container_state(container, shape);
}

Expression *SessionSymbolicHeap::container_state(oop container,
                                           const char *shape) {
  if (container == NULL) return NULL;

  // Phase 1, unlocked: obtain the container's shadow and, for an object, its
  // identity expression.  Both may allocate -- a shadow, a GC root, an
  // Expression -- so neither may happen with _mutex held.  An array's shadow
  // caches no identity, so it is built in phase 3, only for a root: built
  // here, it made every access to a rooted array a new node (one per bucket
  // of hdfs-17960's inode-map scan).
  sym_rid_t id;
  Expression *identity = NULL;
  SymArr *array = NULL;
  if (container->is_array()) {
    array = get_or_alloc_sym_array((arrayOop)container);
    if (array == NULL) return NULL;
    id = array->get_sym_rid();
  } else {
    SymInstance *instance = get_or_alloc_sym_inst(container);
    if (instance == NULL) return NULL;
    id = instance->get_sym_rid();
    identity = instance->get_or_create_ref_exp(container);
  }

  // Phase 2, locked: canonicalize the id and answer from the store if the
  // state already exists.  An aliased container with no state of its own
  // deliberately reports none rather than minting a second root for the same
  // logical container.
  bool aliased;
  {
    HeapLock guard(this);
    sym_rid_t canonical = canonical_container_id_locked(id);
    aliased = canonical != id;
    id = canonical;
    ContainerStateStore::iterator existing = _container_states.find(id);
    if (existing != _container_states.end()) return existing->second;
    if (aliased) return NULL;
  }

  // Phase 3, unlocked: build the state root.
  exp_list_t state_arguments;
  if (container->is_array()) {
    identity = array->get_ref_exp();
    if (identity == NULL) {
      identity = new ArraySymbolExp(array->get_sym_rid(),
                                    array->get_version(), T_OBJECT);
    }
    Expression *declared_length = array->get_length_exp();
    state_arguments.push_back(declared_length == NULL
        ? (Expression *)new ConExpression(
            (jint)((arrayOop)container)->length())
        : declared_length);
  }
  Expression *state = new ContainerExpression(shape, "STATE",
      identity, state_arguments);

  // Phase 4, locked: publish, unless another thread rooted the same container
  // first.  The loser's node stays in the arena and is freed with the session,
  // so discarding it here is exactly a decision not to name it.
  HeapLock guard(this);
  ContainerStateStore::iterator existing = _container_states.find(id);
  if (existing != _container_states.end()) return existing->second;
  _container_states[id] = state;
  return state;
}

sym_rid_t SessionSymbolicHeap::canonical_container_id(oop container) const {
  if (container == NULL) return NULL_SYM_RID;
  // One critical section covers the whole answer: both halves -- resolving the
  // shadow and following the view/owner alias -- read containers this lock
  // guards, and nothing here allocates.
  HeapLock guard(this);
  sym_rid_t id = NULL_SYM_RID;
  if (container->is_array()) {
    if (!container->is_symbolic()) return NULL_SYM_RID;
    id = container->get_sym_rid();
  } else {
    SymInstance *instance = find_sym_inst_locked(container);
    if (instance == NULL) return NULL_SYM_RID;
    id = instance->get_sym_rid();
  }
  return canonical_container_id_locked(id);
}

Expression *SessionSymbolicHeap::find_container_state(oop container) const {
  if (container == NULL) return NULL;
  // Pure lookup: everything it touches is a container, so one critical
  // section covers the whole answer.
  HeapLock guard(this);
  sym_rid_t id = NULL_SYM_RID;
  if (container->is_array()) {
    if (!container->is_symbolic()) return NULL;
    id = container->get_sym_rid();
  } else {
    SymInstance *instance = find_sym_inst_locked(container);
    if (instance == NULL) return NULL;
    id = instance->get_sym_rid();
  }
  id = canonical_container_id_locked(id);
  ContainerStateStore::const_iterator state = _container_states.find(id);
  return state == _container_states.end() ? NULL : state->second;
}

void SessionSymbolicHeap::set_container_state(oop container, Expression *state) {
  if (container == NULL || state == NULL) return;
  sym_rid_t id;
  if (container->is_array()) {
    SymArr *array = get_or_alloc_sym_array((arrayOop)container);
    if (array == NULL) return;
    id = array->get_sym_rid();
  } else {
    SymInstance *instance = get_or_alloc_sym_inst(container);
    if (instance == NULL) return;
    id = instance->get_sym_rid();
  }
  // Last completed write is the state; see the field-shadow write policy.
  HeapLock guard(this);
  _container_states[canonical_container_id_locked(id)] = state;
}

void SessionSymbolicHeap::forget_container_state(oop container) {
  if (container == NULL) return;
  HeapLock guard(this);
  sym_rid_t id = NULL_SYM_RID;
  if (container->is_array()) {
    if (!container->is_symbolic()) return;
    id = container->get_sym_rid();
  } else {
    SymInstance *instance = find_sym_inst_locked(container);
    if (instance == NULL) return;
    id = instance->get_sym_rid();
  }
  _container_states.erase(canonical_container_id_locked(id));
}

void SessionSymbolicHeap::write_array_element(arrayOop array, int index,
                                        Expression *expression,
                                        const ElementWord &word) {
  if (array == NULL || expression == NULL || index < 0
      || index >= array->length()) return;
  SymArr *symbolic = get_or_alloc_sym_array(array);
  if (symbolic == NULL) return;
  exp_list_t arguments;
  arguments.push_back(new ConExpression((jint)index));
  arguments.push_back(expression);
  Expression *next = new ContainerExpression(
      "INDEXED", "WRITE", container_state(array, "INDEXED"), arguments,
      T_OBJECT, std::string(), NULL, word);
  set_container_state(array, next);
  symbolic->store();
}

void SessionSymbolicHeap::alias_container(oop derived, oop owner) {
  if (derived == NULL || owner == NULL || derived->is_array()
      || owner->is_array()) return;
  SymInstance *derived_instance = get_or_alloc_sym_inst(derived);
  SymInstance *owner_instance = get_or_alloc_sym_inst(owner);
  if (derived_instance == NULL || owner_instance == NULL) return;
  HeapLock guard(this);
  _container_owners[derived_instance->get_sym_rid()] =
      canonical_container_id_locked(owner_instance->get_sym_rid());
}

// A traversal cursor belongs to the thread walking it, but its ordinals live
// in a session container, so each read-modify-write below is one critical
// section rather than a lookup followed by a store.

int SessionSymbolicHeap::next_container_position(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return -1;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return -1;
  sym_rid_t id = instance->get_sym_rid();
  HeapLock guard(this);
  int position = _container_positions[id];
  _container_positions[id] = position + 1;
  return position;
}

int SessionSymbolicHeap::current_container_position(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return 0;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return 0;
  sym_rid_t id = instance->get_sym_rid();
  HeapLock guard(this);
  return _container_positions[id];
}

int SessionSymbolicHeap::current_container_index(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return 0;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return 0;
  sym_rid_t id = instance->get_sym_rid();
  HeapLock guard(this);
  return _container_positions[id] - _container_removals[id];
}

int SessionSymbolicHeap::next_container_removal_position(oop cursor) {
  if (cursor == NULL || cursor->is_array()) return -1;
  SymInstance *instance = get_or_alloc_sym_inst(cursor);
  if (instance == NULL) return -1;
  sym_rid_t id = instance->get_sym_rid();
  HeapLock guard(this);
  int traversal_position = _container_positions[id];
  int removed = _container_removals[id];
  if (traversal_position <= 0) return -1;
  _container_removals[id] = removed + 1;
  return traversal_position - 1 - removed;
}

SymInstance *SessionSymbolicHeap::get_or_alloc_sym_inst(oop obj) {
  if (obj == NULL) return NULL;
  SymInstance *existing = find_sym_inst(obj);
  return existing == NULL ? this->alloc_sym_inst(obj) : existing;
}

SymInstance *SessionSymbolicHeap::alloc_sym_inst(oop obj) {
  if (obj == NULL || obj->is_array()) return NULL;
  {
    HeapLock guard(this);
    SymInstance *existing = find_sym_inst_locked(obj);
    if (existing != NULL) return existing;
  }

  // ---------------------------------------------------------------------
  // Unlocked: mint the id, build the shadow, and retain the GC root.
  //
  // JNIHandles::make_global takes JNIGlobalHandle_lock, and taking a HotSpot
  // Mutex from _thread_in_vm can block for a safepoint that a thread parked
  // on _mutex would never reach.  Holding _mutex across it deadlocks the VM
  // thread, so this whole section stays outside the lock and the result is
  // published below.  The id is spent whether or not this thread wins; ids
  // are session-scoped and monotone, so a lost race costs one id, not
  // correctness.
  // ---------------------------------------------------------------------
  // An object this session already named keeps that id: the shadow published
  // below adopts it and clears SYM_RID_NAMED_ONLY, so a reference read that
  // stated this object's identity earlier and an owner projection that states
  // it now are the same term.  A fresh id is minted only for an object no
  // recording has named.
  sym_rid_t sym_rid = obj->get_sym_rid();
  if (sym_rid == NULL_SYM_RID) sym_rid = get_next_sym_rid();
  SymInstance *sym_inst = NULL;
  ResourceMark rm;

  Symbol *klass_symbol = obj->klass()->name();
  guarantee(klass_symbol != NULL, "unexpected null class");
//  tty->print_cr("alloc_sym_inst for %s", klass_symbol->as_C_string());

  bool detached_from_oop_header = requires_detached_object_shadow(obj);
  if (klass_symbol->equals(SymString::TYPE_NAME)) {
    if (detached_from_oop_header) {
      // Intern-table entries are VM-global and may be concurrently shared by
      // unrelated Java code.  Never write this context's sym_rid into that
      // shared oop.  A session-local, GC-stable shadow gives the value a
      // symbolic identity without changing Java reference/content semantics.
    }
    sym_inst = new SymString(sym_rid);
  } else if (klass_symbol->equals(SymStrBuilder::TYPE_NAME)) {
    sym_inst = new SymStrBuilder(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jchar>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jchar>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jboolean>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jboolean>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jbyte>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jbyte>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jint>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jint>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jshort>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jshort>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jlong>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jlong>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<jfloat>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jfloat>(sym_rid);
  } else if (klass_symbol->equals(SymPrimitive<double>::TYPE_NAME)) {
    sym_inst = new SymPrimitive<jdouble>(sym_rid);
  } else if (klass_symbol->equals(SymBigDecimal::TYPE_NAME)) {
    sym_inst = new SymBigDecimal(sym_rid, obj);
  } else {
    sym_inst = new SymObj(sym_rid);
  }

  if (sym_inst == NULL) {
    tty->print_cr("Warning: failed to allocate symbolic object shadow");
    return NULL;
  }

  jobject stable_handle = NULL;
  if (detached_from_oop_header) {
    Handle stable_oop(Thread::current(), obj);
    stable_handle = JNIHandles::make_global(stable_oop);
    if (stable_handle == NULL) {
      // Do not publish a partial shadow.  Callers treat NULL as an
      // unsupported symbolic value and continue with concrete semantics.
      delete sym_inst;
      tty->print_cr("Warning: failed to retain interned String shadow");
      return NULL;
    }
  }

  // ---------------------------------------------------------------------
  // Locked: re-check, then publish.  Writing the oop header word inside the
  // same critical section as the store insert is what makes "one oop, one
  // shadow" hold -- a concurrent allocator either sees no shadow and blocks
  // here, or sees the finished one.
  // ---------------------------------------------------------------------
  SymInstance *winner = NULL;
  {
    HeapLock guard(this);
    winner = find_sym_inst_locked(obj);
    if (winner == NULL) {
      if (detached_from_oop_header) {
        set_sym_ref_locked(sym_rid, sym_inst);
        _detached_object_store.insert(
            std::make_pair(stable_handle, sym_inst));
      } else {
        obj->set_sym_rid(sym_rid);
        set_sym_ref_locked(sym_rid, sym_inst);
      }
      return sym_inst;
    }
  }

  // Lost the race.  Discard this thread's unpublished shadow and its GC root
  // outside the lock -- destroy_global is a HotSpot Mutex -- and return the
  // shadow every other thread will also see.
  delete sym_inst;
  if (stable_handle != NULL) JNIHandles::destroy_global(stable_handle);
  return winner;
}

SymInstance *SessionSymbolicHeap::get_sym_inst(sym_rid_t sym_rid) {
  SymInstance *ret = NULL;
  {
    HeapLock guard(this);
    SymStore::const_iterator found = _sym_refs.find(sym_rid);
    if (found != _sym_refs.end()) ret = (SymInstance *) found->second;
  }
  /**
   * When this assertion is broken,
   * it means that the target object is not initialized with NULL_SYM_RID
   */
  guarantee(ret != NULL, "Unexpected null symbolic object. The object might not properly symbolized.");
  return ret;
}

SymInstance *SessionSymbolicHeap::find_sym_inst(oop obj) const {
  if (obj == NULL || obj->is_array()) return NULL;
  HeapLock guard(this);
  return find_sym_inst_locked(obj);
}

SymInstance *SessionSymbolicHeap::find_sym_inst_locked(oop obj) const {
  if (obj == NULL || obj->is_array()) return NULL;
  if (obj->is_symbolic()) {
    SymStore::const_iterator found = _sym_refs.find(obj->get_sym_rid());
    if (found != _sym_refs.end()) {
      return static_cast<SymInstance *>(found->second);
    }
  }
  // JNIHandles::resolve is a plain load through the handle, so this scan adds
  // no blocking call to the critical section.
  for (DetachedObjectStore::const_iterator found =
           _detached_object_store.begin();
       found != _detached_object_store.end(); ++found) {
    if (JNIHandles::resolve(found->first) == obj) return found->second;
  }
  return NULL;
}

bool SessionSymbolicHeap::requires_detached_object_shadow(oop obj) const {
  if (obj == NULL || obj->is_array() || obj->klass() == NULL
      || obj->klass()->name() == NULL) {
    return false;
  }
  // Keep this policy in the shadow heap so bytecode producers do not need to
  // know which VM-managed objects are unsafe to annotate in their oop header.
  return obj->klass()->name()->equals(SymString::TYPE_NAME)
      && OopUtils::is_java_string_interned(obj);
}

SymArr *SessionSymbolicHeap::get_or_alloc_sym_array(arrayOop array,
                                                    Expression *length_exp,
                                                    bool named) {
  {
    HeapLock guard(this);
    SymArr *existing = find_sym_array_locked(array);
    if (existing != NULL) return existing;
  }
  return this->alloc_sym_array(array, length_exp, named);
}

SymArr *SessionSymbolicHeap::alloc_sym_array(arrayOop array,
                                             Expression *length_exp,
                                             bool named) {
  if (array == NULL) return NULL;
  // Same shape as alloc_sym_inst: build first, then publish under one lock
  // that covers both the header word and the store.  An array shadow needs no
  // GC root, so there is nothing to release on the losing path but the shadow.
  // An array this session already named keeps that id, for the same reason.
  sym_rid_t sym_rid = array->get_sym_rid();
  if (sym_rid == NULL_SYM_RID) sym_rid = get_next_sym_rid();

  // if (length_exp == NULL) {
  //   length_exp = new ConExpression(array->length());
  // }

  SymArr *sym_arr = new SymArr(sym_rid, length_exp);
  sym_arr->set_named(named);

  SymArr *winner = NULL;
  {
    HeapLock guard(this);
    winner = find_sym_array_locked(array);
    if (winner == NULL) {
      array->set_sym_rid(sym_rid);
      set_sym_ref_locked(sym_rid, sym_arr);
      return sym_arr;
    }
  }
  delete sym_arr;
  return winner;
}

SymArr *SessionSymbolicHeap::get_sym_array(sym_rid_t sym_rid) {
  SymArr *ret = NULL;
  {
    HeapLock guard(this);
    SymStore::const_iterator found = _sym_refs.find(sym_rid);
    if (found != _sym_refs.end()) ret = (SymArr *) found->second;
  }
  /**
   * When this assertion is broken,
   * it means that the target object is not initialized with NULL_SYM_RID
   */
  assert(ret != NULL, "null sym obj?");
  return ret;
}

SymArr *SessionSymbolicHeap::find_sym_array(arrayOop array_obj) const {
  HeapLock guard(this);
  return find_sym_array_locked(array_obj);
}

SymArr *SessionSymbolicHeap::find_sym_array_locked(arrayOop array_obj) const {
  if (array_obj == NULL || !array_obj->is_symbolic()) return NULL;
  SymStore::const_iterator found = _sym_refs.find(array_obj->get_sym_rid());
  if (found == _sym_refs.end()) return NULL;
  return static_cast<SymArr *>(found->second);
}


#endif // ENABLE_CONCOLIC
