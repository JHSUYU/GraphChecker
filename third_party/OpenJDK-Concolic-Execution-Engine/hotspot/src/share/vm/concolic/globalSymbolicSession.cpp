#ifdef ENABLE_CONCOLIC

#include "concolic/globalSymbolicSession.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "memory/universe.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/atomic.inline.hpp"
#include "runtime/safepoint.hpp"
#include "runtime/vm_operations.hpp"
#include "runtime/vmThread.hpp"
#include "utilities/debug.hpp"
#include "utilities/ostream.hpp"

bool GlobalSymbolicSession::_open = false;
jlong GlobalSymbolicSession::_session_id = 0;
volatile intptr_t GlobalSymbolicSession::_next_session_id = 0;
SessionSymbolicHeap *GlobalSymbolicSession::_heap = NULL;
GlobalSymbolicSession::ExprArena GlobalSymbolicSession::_arena;
pthread_mutex_t GlobalSymbolicSession::_arena_mutex =
    PTHREAD_MUTEX_INITIALIZER;
volatile intptr_t GlobalSymbolicSession::_next_expression_id = 0;
volatile intptr_t GlobalSymbolicSession::_next_sym_rid = 0;
volatile intptr_t GlobalSymbolicSession::_next_event_id = 0;

namespace {

// An object closure to reset symbolic ids
class RestoreSymbolicClosure : public ObjectClosure {
public:
  void do_object(oop o) {
    if (o != NULL) {
      o->set_sym_rid(NULL_SYM_RID);
    }
  }
};

// Clearing the oop header extension requires a stable heap.  A traced
// workload keeps many mutator threads alive while the session finishes, so a
// raw safe_object_iterate from a Java thread can race allocation or GC.  Run
// the cleanup as a blocking VM operation instead.
class VM_RestoreConcolicSymbolicIds : public VM_Operation {
public:
  virtual VMOp_Type type() const { return VMOp_Dummy; }

  virtual void doit() {
    assert(SafepointSynchronize::is_at_safepoint(),
           "concolic oop cleanup requires a safepoint");
    RestoreSymbolicClosure closure;
    CollectedHeap* heap = Universe::heap();
    heap->ensure_parsability(false);
    heap->safe_object_iterate(&closure);
  }
};

} // anonymous namespace

void GlobalSymbolicSession::open() {
  guarantee(!_open, "a symbolic session is already open");
  // Nothing may have survived the previous session's teardown.  An expression
  // here would be one whose owner is unaccounted for, which is exactly the
  // condition the arena exists to make impossible.
  guarantee(_arena.empty(), "expressions outlived the previous session");
  guarantee(_heap == NULL, "a shadow heap outlived the previous session");
  _next_expression_id = 0;
  _next_sym_rid = 0;
  _next_event_id = 0;
  // Minted before anything else: the counters reset just above are only
  // interpretable against the session that owns them.
  _session_id = (jlong) Atomic::add_ptr((intptr_t) 1, &_next_session_id);
  _heap = new SessionSymbolicHeap();
  SharedFieldVersions::open_session();
  _open = true;
  // The built-in symbols are session state, not per-thread state.  They used
  // to be rebuilt by every ThreadContext constructor, which left every earlier
  // holder of SymbolExpression::get() pointing at a freed node.
  SymbolExpression::init_single_instances();
}

void GlobalSymbolicSession::close() {
  guarantee(_open, "no symbolic session is open");

  // Order matters: drop the version records first -- they name shadows and
  // expressions but own neither -- then the shadows (that is what releases the
  // detached objects' GC roots), then retire the object ids those shadows
  // interpreted, then drop the expressions, and only then declare the session
  // closed.
  SharedFieldVersions::close_session();
  delete _heap;
  _heap = NULL;
  restore_object_symbolic_ids();
  SymbolExpression::clear_single_instances();

  tty->print_cr("Releasing %lu session expressions",
                (unsigned long) _arena.size());
  for (size_t index = 0; index < _arena.size(); ++index) {
    delete _arena[index];
  }
  _arena.clear();
  _next_expression_id = 0;
  _next_sym_rid = 0;
  _next_event_id = 0;
  // Retired, not recycled.  The next session draws a strictly larger id.
  _session_id = 0;
  _open = false;
}

void GlobalSymbolicSession::record_expression(Expression *expression) {
  if (expression == NULL) return;
  pthread_mutex_lock(&_arena_mutex);
  _arena.push_back(expression);
  pthread_mutex_unlock(&_arena_mutex);
}

size_t GlobalSymbolicSession::expression_count() {
  pthread_mutex_lock(&_arena_mutex);
  size_t count = _arena.size();
  pthread_mutex_unlock(&_arena_mutex);
  return count;
}

uint GlobalSymbolicSession::next_expression_id() {
  return (uint) Atomic::add_ptr((intptr_t) 1, &_next_expression_id);
}

jlong GlobalSymbolicSession::next_event_id() {
  return (jlong) Atomic::add_ptr((intptr_t) 1, &_next_event_id);
}

sym_rid_t GlobalSymbolicSession::next_sym_rid() {
  intptr_t next = Atomic::add_ptr((intptr_t) 1, &_next_sym_rid);
  guarantee(next < MAX_SYM_RID, "sym_rid limitted");
  return (sym_rid_t) next;
}

void GlobalSymbolicSession::restore_object_symbolic_ids() {
  VM_RestoreConcolicSymbolicIds restore;
  VMThread::execute(&restore);
}

#endif // ENABLE_CONCOLIC
