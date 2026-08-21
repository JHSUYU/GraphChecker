#ifdef ENABLE_CONCOLIC

#include "concolic/exp/readFromExpression.hpp"

#include "utilities/ostream.hpp"

#include <stdio.h>

ReadFromExpression::ReadFromExpression(
    const std::vector<Candidate> &candidates, const std::string &java_type,
    jlong read_event_id, sym_rid_t owner, int slot,
    const char *location_kind, const char *reason, bool writer_set_complete)
    : _candidates(candidates), _java_type(java_type),
      _reason(reason == NULL ? "" : reason),
      _location_kind(location_kind == NULL ? "" : location_kind),
      _read_event_id(read_event_id), _owner(owner), _slot(slot),
      _writer_set_complete(writer_set_complete) {
  // The unknown candidate is the last arm of the ite chain and the last
  // selector of the exactly-one.  Building a node without it would be building
  // a closed disjunction over one run's writers, which is the one thing this
  // node exists not to do.
  guarantee(!_candidates.empty() && _candidates.back().unknown,
            "a guarded read must end in rf_unknown");
}

bool ReadFromExpression::is_boolean_expression() {
  return _java_type.size() == 1 && _java_type[0] == type2char(T_BOOLEAN);
}

std::string ReadFromExpression::get_name() {
  char buf[64];
  int length = snprintf(buf, sizeof(buf), "rf_read%ld",
                        (long) _read_event_id);
  return std::string(buf, length < 0 ? 0 : length);
}

void ReadFromExpression::print() {
  tty->print("(read-from r%ld", (long) _read_event_id);
  for (size_t index = 0; index < _candidates.size(); ++index) {
    tty->print(" %s=", _candidates[index].selector.c_str());
    Expression::print_on_maybe_null(_candidates[index].value);
  }
  tty->print(")");
}

void ReadFromExpression::serialize_candidate(
    rapidjson::Writer<rapidjson::StringBuffer> &writer,
    const Candidate &candidate) {
  writer.StartObject();
  writer.Key("selector");
  writer.String(candidate.selector.c_str());
  writer.Key("unknown");
  writer.Bool(candidate.unknown);
  writer.Key("fieldVersionId");
  writer.Int64(candidate.field_version_id);
  writer.Key("writerContextId");
  writer.Int64(candidate.writer_context_id);
  writer.Key("writerJavaThreadId");
  writer.Int64(candidate.writer_java_thread_id);
  writer.Key("regionId");
  writer.String(candidate.region_id.c_str());
  writer.Key("taskId");
  writer.String(candidate.task_id.c_str());
  writer.Key("versionKind");
  writer.String(candidate.version_kind.c_str());
  writer.Key("volatileWrite");
  writer.Bool(candidate.volatile_write);
  writer.Key("expression");
  if (candidate.value == NULL) {
    writer.Null();
  } else {
    candidate.value->serialize(writer);
  }
  writer.Key("pathGuard");
  if (candidate.path_guard == NULL) {
    // The empty conjunction, i.e. this writer took no recorded branch.
    // Reported rather than omitted, so a consumer can tell an unguarded write
    // from a guard that was never captured.
    writer.Null();
  } else {
    candidate.path_guard->serialize(writer);
  }
  writer.Key("orderConstraints");
  writer.StartArray();
  if (candidate.unknown) {
    writer.StartObject();
    writer.Key("kind");
    writer.String("UNKNOWN_WRITE_BEFORE_READ");
    writer.Key("readEventId");
    writer.Int64(_read_event_id);
    writer.EndObject();
  } else {
    writer.StartObject();
    writer.Key("kind");
    writer.String("WRITE_BEFORE_READ");
    writer.Key("beforeEventId");
    writer.Int64(candidate.field_version_id);
    writer.Key("afterEventId");
    writer.Int64(_read_event_id);
    writer.EndObject();
    for (size_t index = 0;
         index < candidate.competing_version_ids.size(); ++index) {
      // The sparse read cut: a competing write is either before the selected
      // one or after the read.  Nothing here orders it against anything else.
      writer.StartObject();
      writer.Key("kind");
      writer.String("OTHER_WRITE_OUTSIDE_CUT");
      writer.Key("otherEventId");
      writer.Int64(candidate.competing_version_ids[index]);
      writer.Key("selectedEventId");
      writer.Int64(candidate.field_version_id);
      writer.Key("readEventId");
      writer.Int64(_read_event_id);
      writer.EndObject();
    }
  }
  writer.EndArray();
  writer.EndObject();
}

void ReadFromExpression::serialize_selection(
    rapidjson::Writer<rapidjson::StringBuffer> &writer, size_t index) {
  // Written as a loop rather than as recursion down the chain: a location with
  // many recorded writers would otherwise put one native frame per candidate
  // on the stack, which is the same unbounded-depth problem the expression
  // walk itself used to have.
  size_t opened = 0;
  for (; index + 1 < _candidates.size(); ++index) {
    const Candidate &candidate = _candidates[index];
    writer.StartObject();
    writer.Key("_type");
    writer.String("IteExpression");
    writer.Key("selector");
    writer.String(candidate.selector.c_str());
    writer.Key("then");
    if (candidate.value == NULL) {
      writer.Null();
    } else {
      candidate.value->serialize(writer);
    }
    writer.Key("else");
    ++opened;
  }

  // The unknown arm: no condition, because exactly-one already says that it
  // holds when no other selector does.
  const Candidate &last = _candidates[index];
  if (last.value == NULL) {
    writer.Null();
  } else {
    last.value->serialize(writer);
  }

  while (opened-- > 0) {
    writer.EndObject();
  }
}

void ReadFromExpression::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ReadFromExpression");
  writer.Key("_java_type");
  writer.String(_java_type.c_str());
  writer.Key("resolution");
  writer.String("GUARDED");
  writer.Key("reason");
  writer.String(_reason.c_str());
  writer.Key("expressionAuthority");
  writer.String("VM_GUARDED_READ_FROM_V1");
  writer.Key("readEventId");
  writer.Int64(_read_event_id);
  writer.Key("location");
  writer.StartObject();
  writer.Key("ownerSymRid");
  writer.Int64((jlong) _owner);
  writer.Key("slot");
  writer.Int(_slot);
  writer.Key("locationKind");
  writer.String(_location_kind.c_str());
  writer.EndObject();
  writer.Key("writerSetComplete");
  writer.Bool(_writer_set_complete);

  writer.Key("exactlyOne");
  writer.StartArray();
  for (size_t index = 0; index < _candidates.size(); ++index) {
    writer.String(_candidates[index].selector.c_str());
  }
  writer.EndArray();

  writer.Key("candidates");
  writer.StartArray();
  for (size_t index = 0; index < _candidates.size(); ++index) {
    serialize_candidate(writer, _candidates[index]);
  }
  writer.EndArray();

  writer.Key("ite");
  serialize_selection(writer, 0);
}

UnknownWriterSymbolExp::UnknownWriterSymbolExp(sym_rid_t owner, int slot,
                                               jlong read_event_id,
                                               BasicType type) {
  char buf[BUF_SIZE];
  int length = snprintf(buf, BUF_SIZE, "M_%c_unknownWriter_%lu_%d_r%ld",
                        type2char(type), (unsigned long) owner, slot,
                        (long) read_event_id);
  set(buf, length < 0 ? 0 : length);
  set_type(std::string(1, type2char(type)));
}

#endif // ENABLE_CONCOLIC
