#ifndef SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
#define SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/exp/symbolExpression.hpp"

#include <string>
#include <vector>

/**
 * The value an ordinary concurrent read observed, when the run does not prove
 * which write produced it.
 *
 * One concrete execution performs one real read, and the engine sees the value
 * it returned.  It does not see which store that value came from, and when
 * several tracked writers stored the same value there is nothing in the
 * observation that separates them.  Choosing one anyway -- by concrete value,
 * by event id, by thread -- would manufacture a read-from edge the run never
 * showed.  This node is the alternative: it says exactly what is known, which
 * is that the value came from one of a bounded set of candidates, or from a
 * writer this run did not observe.
 *
 *     exactlyOne(rf1, ..., rfk, rf_unknown)
 *     value = ite(rf1, E1, ite(rf2, E2, ... Unknown_x))
 *
 * `rf_unknown` is present in every node of this kind, without exception.  It
 * is not a fallback for the cases that looked doubtful: it is what keeps the
 * disjunction from asserting that the observed writer set was complete.  A
 * formula that omits it is closed over the writers this one run happened to
 * execute, so an UNSAT answer from it would describe that run rather than the
 * program, and would be reported as a global conclusion.  With it present, an
 * UNSAT answer means "not with any of these writers, and not with an unknown
 * one either", which is a statement the model can actually support.
 *
 * Each candidate also carries the two things a solver needs in order to select
 * it honestly:
 *
 *   - the writer's path guard, so a candidate can only be chosen on a path its
 *     writer actually took;
 *   - its order constraints, which are the sparse read cut: the selected write
 *     precedes the read, and every other candidate write is either before the
 *     selected one or after the read.  Nothing here builds a total schedule --
 *     these are the only order facts the choice needs.
 *
 * An *exact* read produces no node of this kind at all.  It receives the
 * writer's expression directly, so that the reader's own arithmetic composes
 * onto it, which is the whole point of proving provenance.
 */
class ReadFromExpression : public Expression {
public:
  struct Candidate {
    std::string selector;
    // 0 for the unknown candidate, which names no recorded write.
    jlong field_version_id;
    jlong writer_context_id;
    jlong writer_java_thread_id;
    std::string region_id;
    std::string task_id;
    std::string version_kind;
    bool volatile_write;
    bool unknown;
    Expression *value;
    // NULL denotes the empty conjunction, i.e. an unguarded write.
    Expression *path_guard;
    // Field version ids of the other candidates, which the read cut must
    // place either before this one or after the read.
    std::vector<jlong> competing_version_ids;
    Candidate()
        : field_version_id(0), writer_context_id(0), writer_java_thread_id(0),
          volatile_write(false), unknown(false),
          value(NULL), path_guard(NULL) {}
  };

  ReadFromExpression(const std::vector<Candidate> &candidates,
                     const std::string &java_type, jlong read_event_id,
                     sym_rid_t owner, int slot, const char *location_kind,
                     const char *reason, bool writer_set_complete);

  virtual void print();
  virtual bool is_boolean_expression();
  virtual std::string get_name();

protected:
  virtual void serialize_internal(
      rapidjson::Writer<rapidjson::StringBuffer> &writer);

private:
  std::vector<Candidate> _candidates;
  std::string _java_type;
  std::string _reason;
  std::string _location_kind;
  jlong _read_event_id;
  sym_rid_t _owner;
  int _slot;
  bool _writer_set_complete;

  void serialize_candidate(
      rapidjson::Writer<rapidjson::StringBuffer> &writer,
      const Candidate &candidate);
  // Writes the ite chain from `index` onwards.  The last candidate is always
  // the unknown one, so the chain always bottoms out in a free symbol rather
  // than in a candidate asserted by default.
  void serialize_selection(
      rapidjson::Writer<rapidjson::StringBuffer> &writer, size_t index);
};

/**
 * A free symbol standing for a write this run did not observe.
 *
 * Minted per read, not per location: two reads that both fall back to an
 * unknown writer may have observed two different unknown writes, and sharing
 * one symbol between them would assert that they did not.
 */
class UnknownWriterSymbolExp : public SymbolExpression {
public:
  UnknownWriterSymbolExp(sym_rid_t owner, int slot, jlong read_event_id,
                         BasicType type);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_EXP_READFROMEXPRESSION_HPP
