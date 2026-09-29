#ifdef ENABLE_CONCOLIC

#include "concolic/exp/readFromExpression.hpp"
#include "concolic/sharedFieldVersions.hpp"

#include "utilities/ostream.hpp"

#include <stdio.h>

ReadFromExpression::ReadFromExpression(
    jlong observed_version_id, const std::string &observed_version_kind,
    Expression *observed_value, const std::string &java_type,
    jlong read_event_id, sym_rid_t owner, int slot,
    const char *location_kind, bool writer_set_complete,
    const Returned &returned,
    const std::string &site_class, const std::string &site_method,
    const std::string &site_descriptor, int site_bci)
    : _observed_version_id(observed_version_id),
      _observed_version_kind(observed_version_kind),
      _observed_value(observed_value), _java_type(java_type),
      _location_kind(location_kind == NULL ? "" : location_kind),
      _read_event_id(read_event_id), _owner(owner), _slot(slot),
      _writer_set_complete(writer_set_complete), _returned(returned),
      _site_class(site_class), _site_method(site_method),
      _site_descriptor(site_descriptor), _site_bci(site_bci) {
  guarantee(_observed_version_id > 0,
            "a read must name the version it observed");
  guarantee(_observed_value != NULL,
            "the observed version must carry the value it wrote");
}

bool ReadFromExpression::is_boolean_expression() {
  return _java_type.size() == 1 && _java_type[0] == type2char(T_BOOLEAN);
}

bool ReadFromExpression::is_guarded_reference_read() {
  // The emitted Java type of the location, which SharedFieldVersions builds
  // from type2char: 'L' for an object field, '[' for an array-valued one.
  // Both are identities rather than scalars, and both are what a dependent
  // field read has to resolve against the observed writer's object.
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
  // Absent, not null, when the read returned an identity: null is a value.
  switch (_returned.kind) {
    case Returned::CONSTANT:
      writer.Key("concreteValue");
      _returned.constant->serialize(writer);
      break;
    case Returned::NULL_REFERENCE:
      writer.Key("concreteValue");
      writer.Null();
      break;
    case Returned::STRING:
      writer.Key("concreteValue");
      writer.String(_returned.content.c_str(),
                    (rapidjson::SizeType) _returned.content.size());
      break;
    case Returned::UNSTATED:
      break;
  }

  // Where the read stood.  A consumer that has to tell two reads of one
  // location by one occurrence apart has nothing else to tell them by: the
  // event id orders them, the location does not distinguish them, and the
  // site is the innermost frame of the endpoint's site index.
  SharedFieldVersions::EventSite site;
  site.class_name = _site_class;
  site.method_name = _site_method;
  site.method_descriptor = _site_descriptor;
  site.bci = _site_bci;
  SharedFieldVersions::write_site(writer, site);

  // One object, never an array.  `fieldVersionId` addresses the same write in
  // the location's write log, so a reader may take the value from either.
  writer.Key("observedVersion");
  writer.StartObject();
  writer.Key("fieldVersionId");
  writer.Int64(_observed_version_id);
  writer.Key("versionKind");
  writer.String(_observed_version_kind.c_str());
  writer.Key("expression");
  _observed_value->serialize(writer);
  writer.EndObject();
}

#endif // ENABLE_CONCOLIC
