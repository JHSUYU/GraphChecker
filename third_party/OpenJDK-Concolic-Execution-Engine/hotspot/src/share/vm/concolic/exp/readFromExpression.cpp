#ifdef ENABLE_CONCOLIC

#include "concolic/exp/readFromExpression.hpp"

#include "utilities/ostream.hpp"

#include <stdio.h>

ReadFromExpression::ReadFromExpression(
    const std::vector<Candidate> &candidates, const std::string &java_type,
    jlong read_event_id, sym_rid_t owner, int slot,
    const char *location_kind, bool writer_set_complete)
    : _candidates(candidates), _java_type(java_type),
      _location_kind(location_kind == NULL ? "" : location_kind),
      _read_event_id(read_event_id), _owner(owner), _slot(slot),
      _writer_set_complete(writer_set_complete) {
  guarantee(!_candidates.empty(),
            "a guarded read must name a recorded writer");
}

bool ReadFromExpression::is_boolean_expression() {
  return _java_type.size() == 1 && _java_type[0] == type2char(T_BOOLEAN);
}

bool ReadFromExpression::is_guarded_reference_read() {
  // The emitted Java type of the location, which SharedFieldVersions builds
  // from type2char: 'L' for an object field, '[' for an array-valued one.
  // Both are identities rather than scalars, and both are what a dependent
  // field read has to resolve against the selected writer's object.
  return _java_type.size() == 1
      && (_java_type[0] == type2char(T_OBJECT)
          || _java_type[0] == type2char(T_ARRAY));
}

std::string ReadFromExpression::get_name() {
  char buf[64];
  int length = snprintf(buf, sizeof(buf), "rf_read%ld",
                        (long) _read_event_id);
  return std::string(buf, length < 0 ? 0 : length);
}

void ReadFromExpression::serialize_candidate(
    rapidjson::Writer<rapidjson::StringBuffer> &writer,
    const Candidate &candidate) {
  writer.StartObject();
  writer.Key("selector");
  writer.String(candidate.selector.c_str());
  writer.Key("fieldVersionId");
  writer.Int64(candidate.field_version_id);
  writer.Key("versionKind");
  writer.String(candidate.version_kind.c_str());
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
  writer.EndObject();
}

void ReadFromExpression::serialize_internal(
    rapidjson::Writer<rapidjson::StringBuffer> &writer) {
  writer.Key("_type");
  writer.String("ReadFromExpression");
  writer.Key("_java_type");
  writer.String(_java_type.c_str());
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
}

#endif // ENABLE_CONCOLIC
