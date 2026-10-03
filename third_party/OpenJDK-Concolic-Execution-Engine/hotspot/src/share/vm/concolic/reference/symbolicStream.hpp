#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICSTREAM_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICSTREAM_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/methodSymbolizerHandle.hpp"

#include <map>
#include <vector>

class MethodSymbolizer;
class StreamPipeline;

/**
 * The java.util.stream model: a sequential pipeline over a modeled
 * container -- a list, a deque, a hash set, a map's key, entry or values
 * view -- as the relation it computes.
 *
 * A pipeline is bookkeeping, never an Expression: `stream()` records its
 * source (the container's state as the stream read it, its view, its
 * member count), and each modeled intermediate call (filter, map, limit,
 * sorted, distinct, unordered) one stage on the stream object it returns.
 * Their bodies run muted.  The terminal call (collect to a list or a set,
 * toArray, count, any/all/noneMatch, findFirst/findAny, forEach) runs
 * muted too, and every stage's functional object is a callback
 * (MethodSymbolizer::enter_callback) seeded with what the element it is
 * called for is: the source's member (READ of the state at its position,
 * or the map entry or key, SymMap::visited_member), then the previous map
 * stage's result.  The sequential pipeline calls the stages per element in
 * order and stops an element at the first filter that answers false, so
 * each element's progress is reconstructed from the callbacks' answers.
 *
 * The terminal states the result as a container relation: an INDEXED chain
 * from the exact empty container with one APPEND_IF per element under the
 * conjunction of its filters' answers and its LIMIT positions (a set: a
 * guarded PUT_IF); count is that chain's SIZE, a match its IS_EMPTY.  What
 * the run decided and no relation can state -- an element no run pushed
 * past a filter that dropped it before a stage that calls back, the
 * members a LIMIT or a short-circuit never pulled, the members beyond the
 * source's end -- is a PIN node on the chain: its condition, in the run's
 * polarity, holds wherever the result is used.  A result that cannot be
 * stated at all (a symbolic element entering sorted or distinct, a
 * reconstruction the callbacks contradict, more members than the snapshot
 * bound, findFirst, forEach under a symbolic decision) is the run's own
 * concrete value, named STREAM_PINNED:<reason>; an unmodeled operation
 * (flatMap, peek, skip, reduce, parallel, an unknown collector, ...) stops
 * the recording and the rest runs as bytecode, named
 * STREAM_OPERATION_UNMODELED:<operation>.  Either name is filed only when
 * something symbolic reached the pipeline (ThreadContext::note_model_gap);
 * a pipeline nothing symbolic reached returns its concrete result and
 * names nothing.
 */
class SymStream {
public:
  static void init_register_class(MethodSymbolizer *m_symbolizer);
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  // Collection.stream(): SymMap holds java/util/Collection's registration
  // and routes it here.
  static bool invoke_source(MethodSymbolizerHandle &handle);
  static Expression *finish_source(MethodSymbolizerHandle &handle);

private:
  static void seed_callback(MethodSymbolizerHandle &call, sym_rid_t receiver,
                            const std::vector<oop> &arguments,
                            exp_list_t *seeds, Expression **key);
  static void fold_callback(MethodSymbolizerHandle &call,
                            const CallbackResult &result, oop returned,
                            const std::vector<oop> &arguments);
  static void unwound(MethodSymbolizerHandle &call);
};

/**
 * One thread's recorded pipelines, by the session id of the stream object
 * that holds them, and the collector kinds Collectors.toList/toSet named,
 * by their accumulator.  Owned by the thread's context, so a pipeline a
 * thread never ended dies with it.
 */
class StreamTable {
public:
  StreamTable() {}
  ~StreamTable();
  StreamPipeline *find(sym_rid_t stream) const;
  // Takes ownership; replaces nothing (a stream object holds one pipeline).
  void put(sym_rid_t stream, StreamPipeline *pipeline);
  // Releases ownership.
  StreamPipeline *take(sym_rid_t stream);
  void name_collector(sym_rid_t accumulator, int kind);
  // The kind named, 0 for none.
  int collector(sym_rid_t accumulator) const;

private:
  std::map<sym_rid_t, StreamPipeline *> _pipelines;
  std::map<sym_rid_t, int> _collectors;
  StreamTable(const StreamTable &);
  StreamTable &operator=(const StreamTable &);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICSTREAM_HPP
