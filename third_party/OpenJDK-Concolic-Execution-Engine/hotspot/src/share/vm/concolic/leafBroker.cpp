#ifdef ENABLE_CONCOLIC

#include "concolic/leafBroker.hpp"
#include "classfile/javaClasses.hpp"
#include "classfile/systemDictionary.hpp"
#include "concolic/concolicMngr.hpp"
#include "concolic/exp/containerExpression.hpp"
#include "concolic/exp/expression.hpp"
#include "concolic/exp/stringExpression.hpp"
#include "concolic/exp/symbolExpression.hpp"
#include "concolic/globalSymbolicSession.hpp"
#include "concolic/reference/containerSupport.hpp"
#include "concolic/reference/symbolicArray.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/sessionSymbolicHeap.hpp"
#include "concolic/sharedFieldVersions.hpp"
#include "concolic/threadContext.hpp"
#include "concolic/utils.hpp"
#include "memory/resourceArea.hpp"
#include "oops/instanceKlass.hpp"
#include "oops/objArrayOop.hpp"
#include "oops/typeArrayOop.hpp"
#include "prims/jvm.h"
#include "runtime/fieldDescriptor.hpp"
#include "runtime/thread.hpp"
#include "utilities/ostream.hpp"
#include "utilities/utf8.hpp"
#include "webridge/utils/rapidjson/document.h"
#include "webridge/utils/rapidjson/stringbuffer.h"
#include "webridge/utils/rapidjson/writer.h"

#include <errno.h>
#include <stdlib.h>
#include <string.h>

#include <algorithm>
#include <string>
#include <vector>

namespace {

typedef rapidjson::Writer<rapidjson::StringBuffer> JsonWriter;
typedef SharedFieldVersions SFV;
// The template is read as UTF-16, the unit a String's content is compared in.
typedef rapidjson::GenericDocument<rapidjson::UTF16<jchar> > TemplateDocument;
typedef rapidjson::GenericValue<rapidjson::UTF16<jchar> > TemplateValue;

// ---------------------------------------------------------------------------
// Answers
// ---------------------------------------------------------------------------

enum Status {
  STATUS_OK,
  // exportLeaf: no shadow anywhere, so the leaf's typed constant.
  STATUS_CONSTANT,
  // mintLeaf: the object the expression would land on, or the object that
  // holds the leaf's slot, is JVM-wide.
  STATUS_SHARED,
  // mintLeaf: what the expression would land on already carries one -- the
  // leaf object (a cached String another decode minted: the caller stores a
  // fresh equal object and mints that) or the field or element slot.  A mint
  // never replaces an expression.
  STATUS_SHADOWED,
  // mintLeaf: the container holding the leaf already has a recorded state
  // (an entry or position), or the element is a versioned location.
  STATUS_TRACKED_CONTAINER,
  STATUS_UNSUPPORTED,
  // Neither inside a region nor under an open workload session.
  STATUS_NO_SESSION,
  // The slot addresses nothing: no such field, index, key or position.
  STATUS_SLOT_MISSING,
  // The slot holds null.
  STATUS_NULL_LEAF,
  // The template does not state this leaf (its texts are not the String's
  // content, a decimal is not Java's rendering, a hole of the wrong sort).
  STATUS_TEMPLATE_MISMATCH,
  // The template is not the grammar's.
  STATUS_MALFORMED_TEMPLATE
};

const char *status_name(Status status) {
  switch (status) {
    case STATUS_OK:                return "OK";
    case STATUS_CONSTANT:          return "CONSTANT";
    case STATUS_SHARED:            return "SHARED";
    case STATUS_SHADOWED:          return "SHADOWED";
    case STATUS_TRACKED_CONTAINER: return "TRACKED_CONTAINER";
    case STATUS_UNSUPPORTED:       return "UNSUPPORTED";
    case STATUS_NO_SESSION:        return "NO_SESSION";
    case STATUS_SLOT_MISSING:      return "SLOT_MISSING";
    case STATUS_NULL_LEAF:         return "NULL_LEAF";
    case STATUS_TEMPLATE_MISMATCH: return "TEMPLATE_MISMATCH";
    default:                       return "MALFORMED_TEMPLATE";
  }
}

const char *slot_kind_name(jint kind) {
  switch (kind) {
    case LeafBroker::SLOT_FIELD:    return "FIELD";
    case LeafBroker::SLOT_ELEMENT:  return "ELEMENT";
    case LeafBroker::SLOT_ENTRY:    return "ENTRY";
    case LeafBroker::SLOT_POSITION: return "POSITION";
    case LeafBroker::SLOT_VALUE:    return "VALUE";
    default:                        return "UNKNOWN";
  }
}

// One answer document.  Every expression in it is a reference into its own
// expression table, which finish() writes.
class Answer {
 public:
  Answer(const char *kind, jint slot_kind) : _writer(_buffer) {
    _writer.StartObject();
    _writer.Key("schemaVersion");
    _writer.Int(1);
    _writer.Key("kind");
    _writer.String(kind);
    _writer.Key("slotKind");
    _writer.String(slot_kind_name(slot_kind));
  }

  JsonWriter &writer() { return _writer; }

  // The status, and the reason a refusal names.
  Answer &status(Status status, const std::string &reason) {
    _writer.Key("status");
    _writer.String(status_name(status));
    if (!reason.empty()) {
      _writer.Key("reason");
      _writer.String(reason.c_str(), (rapidjson::SizeType) reason.size());
    }
    return *this;
  }

  std::string finish() {
    _table.write_table(_writer);
    _writer.EndObject();
    return std::string(_buffer.GetString(), _buffer.GetLength());
  }

 private:
  rapidjson::StringBuffer _buffer;
  JsonWriter _writer;
  VmExpressionArtifactScope _table;
};

// ---------------------------------------------------------------------------
// The leaf a slot holds
// ---------------------------------------------------------------------------

struct Leaf {
  jint kind;
  // FIELD: the owner; ELEMENT: the array; ENTRY, POSITION: the container;
  // VALUE: the leaf itself.
  Handle holder;
  // The slot's type: a primitive for a primitive field or an element of a
  // primitive array, else T_OBJECT.
  BasicType cell;
  // What a reference slot holds; null is a null leaf.
  Handle object;
  int offset;        // FIELD
  bool boxed_field;  // FIELD: wrapper-typed (SFV::wrapper_value_type)
  jint index;        // ELEMENT, POSITION
  int members;       // POSITION: how many the list holds
  Handle key;        // ENTRY
  // What the leaf is: a primitive (the cell's, or a box's), T_OBJECT for a
  // String, T_ILLEGAL for null or any other object.
  BasicType sort;
  jlong bits;        // a primitive's or a box's word, in raw_bits
  Leaf()
      : kind(-1), cell(T_ILLEGAL), offset(-1), boxed_field(false), index(-1),
        members(0), sort(T_ILLEGAL), bits(0) {}
  bool numeric() const { return is_java_primitive(sort); }
  bool string() const { return sort == T_OBJECT; }
  bool null() const { return cell == T_OBJECT && object.is_null(); }
  // Whether a mint lands on the leaf object rather than on the slot.
  bool lands_on_object() const {
    return kind == LeafBroker::SLOT_VALUE || kind == LeafBroker::SLOT_ENTRY
        || kind == LeafBroker::SLOT_POSITION;
  }
};

jlong box_bits(oop box, BasicType *type) {
  jvalue value;
  *type = java_lang_boxing_object::get_value(box, &value);
  switch (*type) {
    case T_BOOLEAN: return SFV::raw_bits(value.z);
    case T_BYTE:    return SFV::raw_bits(value.b);
    case T_CHAR:    return SFV::raw_bits(value.c);
    case T_SHORT:   return SFV::raw_bits(value.s);
    case T_INT:     return SFV::raw_bits(value.i);
    case T_LONG:    return SFV::raw_bits(value.j);
    case T_FLOAT:   return SFV::raw_bits(value.f);
    case T_DOUBLE:  return SFV::raw_bits(value.d);
    default:
      *type = T_ILLEGAL;
      return 0;
  }
}

void classify(Leaf *leaf) {
  if (leaf->cell != T_OBJECT) {
    leaf->sort = leaf->cell;
    return;
  }
  oop value = leaf->object();
  if (value == NULL || value->is_array()) return;
  if (value->klass() == SystemDictionary::String_klass()) {
    leaf->sort = T_OBJECT;
    return;
  }
  BasicType boxed = T_ILLEGAL;
  const jlong bits = box_bits(value, &boxed);
  if (boxed != T_ILLEGAL) {
    leaf->sort = boxed;
    leaf->bits = bits;
  }
}

bool integer_slot(oop slot, jint *index) {
  jvalue value;
  if (slot == NULL || java_lang_boxing_object::get_value(slot, &value)
                          != T_INT) {
    return false;
  }
  *index = value.i;
  return true;
}

std::string class_of(oop value) {
  return value == NULL ? std::string("null")
                       : std::string(value->klass()->external_name());
}

Status locate_field(Handle parent, Handle slot, Leaf *leaf,
                    std::string *reason) {
  oop reflected = slot();
  if (reflected == NULL
      || reflected->klass() != SystemDictionary::reflect_Field_klass()) {
    *reason = "SLOT_NOT_A_FIELD";
    return STATUS_SLOT_MISSING;
  }
  Klass *holder = java_lang_Class::as_Klass(
      java_lang_reflect_Field::clazz(reflected));
  if (holder == NULL || !holder->oop_is_instance()) {
    *reason = "FIELD_HOLDER_UNRESOLVED";
    return STATUS_SLOT_MISSING;
  }
  if ((java_lang_reflect_Field::modifiers(reflected) & JVM_ACC_STATIC) != 0) {
    *reason = "STATIC_FIELD";
    return STATUS_UNSUPPORTED;
  }
  if (parent()->is_array() || !parent()->is_a(holder)) {
    *reason = "FIELD_NOT_OF_PARENT";
    return STATUS_SLOT_MISSING;
  }
  fieldDescriptor field;
  field.reinitialize(InstanceKlass::cast(holder),
                     java_lang_reflect_Field::slot(reflected));
  leaf->offset = field.offset();
  const BasicType type = field.field_type();
  if (is_java_primitive(type)) {
    leaf->cell = type;
    leaf->bits = SFV::field_bits(parent(), leaf->offset, type).bits;
  } else {
    leaf->cell = T_OBJECT;
    leaf->boxed_field =
        SFV::wrapper_value_type(field.signature()) != T_ILLEGAL;
    leaf->object = Handle(Thread::current(),
                          parent()->obj_field(leaf->offset));
  }
  return STATUS_OK;
}

Status locate_element(Handle parent, Handle slot, Leaf *leaf,
                      std::string *reason) {
  if (!parent()->is_array()) {
    *reason = "PARENT_NOT_AN_ARRAY";
    return STATUS_SLOT_MISSING;
  }
  if (!integer_slot(slot(), &leaf->index)) {
    *reason = "SLOT_NOT_AN_INDEX";
    return STATUS_SLOT_MISSING;
  }
  arrayOop array = arrayOop(parent());
  if (leaf->index < 0 || leaf->index >= array->length()) {
    *reason = "INDEX_OUT_OF_RANGE";
    return STATUS_SLOT_MISSING;
  }
  if (array->is_typeArray()) {
    const SFV::ConcreteBits word = SFV::element_bits(array, leaf->index);
    leaf->cell = word.type;
    leaf->bits = word.bits;
  } else {
    leaf->cell = T_OBJECT;
    leaf->object = Handle(Thread::current(),
                          objArrayOop(array)->obj_at(leaf->index));
  }
  return STATUS_OK;
}

Status locate_member(Handle parent, Handle slot, Leaf *leaf,
                     std::string *reason) {
  oop container = parent();
  const ContainerSupport::Capability capability =
      ContainerSupport::capability(container);
  const bool entry = leaf->kind == LeafBroker::SLOT_ENTRY;
  if (entry) {
    if (capability != ContainerSupport::CAPABILITY_HASH_MAP
        && capability != ContainerSupport::CAPABILITY_CONCURRENT_MAP
        && capability != ContainerSupport::CAPABILITY_HASHTABLE) {
      *reason = "NOT_A_MODELED_MAP:" + class_of(container);
      return STATUS_UNSUPPORTED;
    }
    if (slot.is_null()) {
      *reason = "NULL_KEY";
      return STATUS_SLOT_MISSING;
    }
    leaf->key = slot;
  } else {
    if (capability != ContainerSupport::CAPABILITY_INDEXED
        || container->is_array()) {
      *reason = "NOT_A_MODELED_LIST:" + class_of(container);
      return STATUS_UNSUPPORTED;
    }
    if (!integer_slot(slot(), &leaf->index)) {
      *reason = "SLOT_NOT_AN_INDEX";
      return STATUS_SLOT_MISSING;
    }
  }
  oop member = NULL;
  const char *unreadable = NULL;
  if (!ContainerSupport::member_of(container, entry ? slot() : (oop) NULL,
                                   leaf->index, &member, &leaf->members,
                                   &unreadable)) {
    if (unreadable != NULL) {
      *reason = std::string("CONTAINER_UNREADABLE:") + unreadable;
      return STATUS_UNSUPPORTED;
    }
    *reason = entry ? "KEY_ABSENT" : "POSITION_OUT_OF_RANGE";
    return STATUS_SLOT_MISSING;
  }
  leaf->cell = T_OBJECT;
  leaf->object = Handle(Thread::current(), member);
  return STATUS_OK;
}

Status locate(Handle parent, jint kind, Handle slot, Leaf *leaf,
              std::string *reason) {
  leaf->kind = kind;
  leaf->holder = parent;
  Status status = STATUS_OK;
  if (kind == LeafBroker::SLOT_VALUE) {
    leaf->cell = T_OBJECT;
    leaf->object = parent;
  } else if (parent.is_null()) {
    *reason = "NULL_PARENT";
    status = STATUS_SLOT_MISSING;
  } else if (kind == LeafBroker::SLOT_FIELD) {
    status = locate_field(parent, slot, leaf, reason);
  } else if (kind == LeafBroker::SLOT_ELEMENT) {
    status = locate_element(parent, slot, leaf, reason);
  } else if (kind == LeafBroker::SLOT_ENTRY
             || kind == LeafBroker::SLOT_POSITION) {
    status = locate_member(parent, slot, leaf, reason);
  } else {
    char text[48];
    jio_snprintf(text, sizeof(text), "SLOT_KIND:%d", (int) kind);
    *reason = text;
    status = STATUS_UNSUPPORTED;
  }
  if (status == STATUS_OK) classify(leaf);
  return status;
}

// The descriptor of what a leaf is: a primitive's (a box's value sort), or
// a String's; empty for null or another object.
std::string java_type(const Leaf &leaf) {
  if (leaf.numeric()) return std::string(1, type2char(leaf.sort));
  if (leaf.string()) return "Ljava/lang/String;";
  return std::string();
}

// What the leaf held, as a read states what it returned.
ReturnedValue leaf_value(const Leaf &leaf) {
  if (leaf.numeric()) {
    return SFV::returned_value(SFV::ConcreteBits(leaf.sort, leaf.bits), NULL);
  }
  if (leaf.cell == T_OBJECT) {
    return SFV::returned_value(SFV::ConcreteBits(), leaf.object());
  }
  return ReturnedValue();
}

// Refuses a leaf a template cannot state: null, or neither a primitive, a
// box nor a String.
Status statable(const Leaf &leaf, std::string *reason) {
  if (leaf.null()) return STATUS_NULL_LEAF;
  if (!leaf.numeric() && !leaf.string()) {
    *reason = "LEAF_CLASS:" + class_of(leaf.object());
    return STATUS_UNSUPPORTED;
  }
  return STATUS_OK;
}

// ---------------------------------------------------------------------------
// exportLeaf: slot, then object, then constant
// ---------------------------------------------------------------------------

// A READ of `state` at the leaf's position or key: the leaf in terms of the
// container, when the recording cannot name one write.  Built, not recorded.
Expression *container_read(const char *shape, Expression *state,
                           Expression *position, const Leaf &leaf) {
  exp_list_t arguments;
  arguments.push_back(position);
  if (leaf.cell != T_OBJECT) {
    return new ContainerExpression(shape, "READ", state, arguments,
                                   leaf.cell);
  }
  return new ContainerExpression(
      shape, "READ", state, arguments,
      ContainerSupport::result_type(leaf.object(), T_OBJECT),
      ContainerSupport::java_type(leaf.object(), T_OBJECT));
}

// The expression the slot holds for the leaf, or NULL.
Expression *slot_shadow(const Leaf &leaf) {
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  if (leaf.kind == LeafBroker::SLOT_FIELD) {
    SymInstance *owner = heap->find_sym_inst(leaf.holder());
    return owner == NULL ? NULL : owner->get(leaf.offset);
  }
  if (leaf.kind == LeafBroker::SLOT_VALUE) return NULL;
  Expression *state = heap->find_container_state(leaf.holder());
  if (state == NULL) return NULL;
  Expression *stored = NULL;
  ContainerSupport::MemberAnswer answer;
  if (leaf.kind == LeafBroker::SLOT_ELEMENT) {
    arrayOop array = arrayOop(leaf.holder());
    answer = ContainerSupport::element_answer(
        array, heap->find_sym_array(array), state, leaf.index, &stored);
  } else if (leaf.kind == LeafBroker::SLOT_POSITION) {
    answer = ContainerSupport::position_answer(state, leaf.index,
                                               leaf.members, &stored);
  } else {
    answer = ContainerSupport::entry_answer(state, leaf.key(), &stored);
  }
  if (answer == ContainerSupport::MEMBER_RECORDED) return stored;
  // The heap's own: the leaf object's shadow, else its constant.
  if (answer != ContainerSupport::MEMBER_UNDECIDED) return NULL;
  if (leaf.kind != LeafBroker::SLOT_ENTRY) {
    return container_read("INDEXED", state, new ConExpression(leaf.index),
                          leaf);
  }
  Expression *key = ContainerSupport::semantic_value(leaf.key());
  if (key == NULL) key = ContainerSupport::concrete_value(leaf.key());
  return container_read("ASSOCIATIVE", state, key, leaf);
}

// The leaf object's own expression, or NULL.  A JVM-wide object carries
// none of its own (item 5): whatever it holds belongs to some slot.
Expression *own_shadow(const Leaf &leaf) {
  if (leaf.cell != T_OBJECT || leaf.object.is_null()) return NULL;
  oop value = leaf.object();
  if (jvm_shared_object(value)) return NULL;
  return ContainerSupport::semantic_value(value);
}

// The leaf's typed constant; NULL for a String past the symbol-name bound,
// whose value only `concrete` states.
Expression *typed_constant(const Leaf &leaf) {
  if (leaf.numeric()) return SFV::primitive_expression(leaf.sort, leaf.bits);
  ResourceMark rm;
  const std::string text = OopUtils::java_string_to_c(leaf.object());
  return ConStringSymbolExp::fits(text) ? new ConStringSymbolExp(text)
                                        : NULL;
}

// ---------------------------------------------------------------------------
// mintLeaf: the template
// ---------------------------------------------------------------------------

enum PartKind {
  PART_LITERAL, PART_NUM, PART_DEC_INT, PART_DEC_LONG, PART_BOOL, PART_STR
};

const char *const PART_KIND_NAMES[] = {
  "LITERAL", "NUM", "DEC_INT", "DEC_LONG", "BOOL", "STR"
};

struct Part {
  PartKind kind;
  std::string label;
  // A literal's text, or a text hole's rendering in this leaf.
  std::vector<jchar> text;
  Part() : kind(PART_LITERAL) {}
};

// The longest label a hole symbol's name keeps whole.
const size_t MAX_LABEL = 256;

bool ascii_equals(const TemplateValue &value, const char *ascii) {
  const size_t length = strlen(ascii);
  if (!value.IsString() || value.GetStringLength() != length) return false;
  const jchar *chars = value.GetString();
  for (size_t index = 0; index < length; ++index) {
    if (chars[index] != (jchar) (unsigned char) ascii[index]) return false;
  }
  return true;
}

const TemplateValue *member(const TemplateValue &object, const char *name) {
  for (TemplateValue::ConstMemberIterator it = object.MemberBegin();
       it != object.MemberEnd(); ++it) {
    if (ascii_equals(it->name, name)) return &it->value;
  }
  return NULL;
}

// A label or a kind: visible ASCII, no quote or backslash, at most
// MAX_LABEL characters.
bool token(const TemplateValue *value, std::string *out) {
  if (value == NULL || !value->IsString() || value->GetStringLength() == 0
      || value->GetStringLength() > MAX_LABEL) {
    return false;
  }
  out->clear();
  const jchar *chars = value->GetString();
  for (size_t index = 0; index < value->GetStringLength(); ++index) {
    const jchar c = chars[index];
    if (c < 0x21 || c > 0x7e || c == '"' || c == '\\') return false;
    out->push_back((char) c);
  }
  return true;
}

std::vector<jchar> chars_of(const TemplateValue &value) {
  const jchar *chars = value.GetString();
  return std::vector<jchar>(chars, chars + value.GetStringLength());
}

// The VM's UTF-8 spelling of UTF-16 text (OopUtils::java_string_to_c's).
std::string utf8_of(const std::vector<jchar> &text) {
  if (text.empty()) return std::string();
  ResourceMark rm;
  jchar *chars = const_cast<jchar *>(&text[0]);
  const int length = UNICODE::utf8_length(chars, (int) text.size());
  char *utf8 = NEW_RESOURCE_ARRAY(char, length + 1);
  UNICODE::convert_to_utf8(chars, (int) text.size(), utf8);
  return std::string(utf8, (size_t) length);
}

// A String's UTF-16 content.
std::vector<jchar> content_of(oop string) {
  std::vector<jchar> content;
  typeArrayOop value = java_lang_String::value(string);
  const int length = java_lang_String::length(string);
  if (value != NULL && length > 0) {
    jchar *first = value->char_at_addr(java_lang_String::offset(string));
    content.assign(first, first + length);
  }
  return content;
}

// Parses {"parts":[{"literal":T} | {"hole":K,"label":L[,"text":T]}...]},
// read in the String's own UTF-16 so no text changes spelling on the way.
bool parse_template(oop json, std::vector<Part> *parts,
                    std::string *reason) {
  if (json == NULL || json->klass() != SystemDictionary::String_klass()) {
    *reason = "NO_TEMPLATE";
    return false;
  }
  std::vector<jchar> text = content_of(json);
  text.push_back(0);
  TemplateDocument document;
  document.Parse<rapidjson::kParseValidateEncodingFlag
                     | rapidjson::kParseIterativeFlag,
                 rapidjson::UTF16<jchar> >(&text[0]);
  if (document.HasParseError() || !document.IsObject()) {
    *reason = "NOT_A_JSON_OBJECT";
    return false;
  }
  const TemplateValue *list = member(document, "parts");
  if (list == NULL || !list->IsArray() || list->Empty()) {
    *reason = "NO_PARTS";
    return false;
  }
  for (TemplateValue::ConstValueIterator it = list->Begin();
       it != list->End(); ++it) {
    if (!it->IsObject()) {
      *reason = "PART_NOT_AN_OBJECT";
      return false;
    }
    const TemplateValue *literal = member(*it, "literal");
    const TemplateValue *hole = member(*it, "hole");
    Part part;
    if ((literal == NULL) == (hole == NULL)) {
      *reason = "PART_NEITHER_LITERAL_NOR_HOLE";
      return false;
    }
    if (literal != NULL) {
      if (!literal->IsString()) {
        *reason = "LITERAL_NOT_TEXT";
        return false;
      }
      part.text = chars_of(*literal);
      parts->push_back(part);
      continue;
    }
    std::string kind;
    if (!token(hole, &kind)) {
      *reason = "HOLE_KIND";
      return false;
    }
    bool known = false;
    for (int index = PART_NUM; index <= PART_STR; ++index) {
      if (kind == PART_KIND_NAMES[index]) {
        part.kind = (PartKind) index;
        known = true;
      }
    }
    if (!known) {
      *reason = "HOLE_KIND:" + kind;
      return false;
    }
    if (!token(member(*it, "label"), &part.label)) {
      *reason = "HOLE_LABEL";
      return false;
    }
    const TemplateValue *text = member(*it, "text");
    if (part.kind == PART_NUM) {
      if (text != NULL) {
        *reason = "NUM_HOLE_WITH_TEXT:" + part.label;
        return false;
      }
    } else {
      if (text == NULL || !text->IsString()) {
        *reason = "HOLE_WITHOUT_TEXT:" + part.label;
        return false;
      }
      part.text = chars_of(*text);
    }
    parts->push_back(part);
  }
  return true;
}

// Java's decimal rendering of an int (or a long) is `text` exactly:
// Long.toString(Long.parseLong(text)).equals(text).
bool canonical_decimal(const std::string &text, bool is_int, jlong *out) {
  if (text.empty() || text.size() > 20) return false;
  errno = 0;
  char *tail = NULL;
  const long long parsed = strtoll(text.c_str(), &tail, 10);
  if (errno != 0 || tail == text.c_str() || tail == NULL || *tail != '\0') {
    return false;
  }
  if (is_int && (parsed < (long long) min_jint
                 || parsed > (long long) max_jint)) {
    return false;
  }
  char rendered[32];
  jio_snprintf(rendered, sizeof(rendered), JLONG_FORMAT, (jlong) parsed);
  if (text != rendered) return false;
  *out = (jlong) parsed;
  return true;
}

/**
 * One boundary symbol: `M_<T>_field_<label>` for a primitive sort, and
 * `M_L'String'_field_<label>` for a String, as the exact field symbolizer
 * names its symbols.  It states the value the leaf held for it, as a
 * method-return symbol does, since nothing else declares it.
 */
class HoleSymbolExp : public SymbolExpression {
 public:
  HoleSymbolExp(const std::string &label, BasicType type,
                const ReturnedValue &value)
      : _value(value) {
    char buf[BUF_SIZE];
    stringStream ss(buf, BUF_SIZE);
    if (type == T_OBJECT) {
      set_head(ss, 'M', T_OBJECT, "'String'");
      _type = "java/lang/String";
    } else {
      set_head(ss, 'M', type);
      _type = std::string(1, type2char(type));
    }
    ss.print("field_%s", label.c_str());
    this->finalize(buf, (int) ss.size());
  }

  const std::string &name() const { return _str; }
  const ReturnedValue &value() const { return _value; }

  virtual void serialize_internal(JsonWriter &writer) {
    SymbolExpression::serialize_internal(writer);
    _value.serialize(writer);
  }

 private:
  ReturnedValue _value;
};

struct Hole {
  const Part *part;
  HoleSymbolExp *symbol;
  std::string java_type;
};

ReturnedValue constant(Expression *value) {
  ReturnedValue returned;
  returned.kind = ReturnedValue::CONSTANT;
  returned.constant = value;
  return returned;
}

HoleSymbolExp *hole(const Part &part, BasicType type,
                    const ReturnedValue &value, std::vector<Hole> *holes) {
  Hole minted;
  minted.part = &part;
  minted.symbol = new HoleSymbolExp(part.label, type, value);
  minted.java_type = type == T_OBJECT ? "Ljava/lang/String;"
                                      : std::string(1, type2char(type));
  holes->push_back(minted);
  return minted.symbol;
}

// The leaf's expression over fresh hole symbols, once the template is shown
// to state exactly this leaf.
Status build(const Leaf &leaf, const std::vector<Part> &parts,
             std::vector<Hole> *holes, Expression **expression,
             std::string *reason) {
  if (leaf.numeric()) {
    if (parts.size() != 1 || parts[0].kind != PART_NUM) {
      *reason = "NUMERIC_LEAF_TAKES_ONE_NUM_HOLE";
      return STATUS_TEMPLATE_MISMATCH;
    }
    *expression = hole(parts[0], leaf.sort,
                       constant(SFV::primitive_expression(leaf.sort,
                                                          leaf.bits)),
                       holes);
    return STATUS_OK;
  }
  // A String: the parts' texts, in order, are exactly its content.
  const std::vector<jchar> content = content_of(leaf.object());
  exp_list_t pieces;
  size_t at = 0;
  for (size_t index = 0; index < parts.size(); ++index) {
    const Part &part = parts[index];
    if (part.kind == PART_NUM) {
      *reason = "NUM_HOLE_IN_STRING:" + part.label;
      return STATUS_TEMPLATE_MISMATCH;
    }
    if (at + part.text.size() > content.size()
        || !std::equal(part.text.begin(), part.text.end(),
                       content.begin() + at)) {
      *reason = "TEXT_MISMATCH";
      return STATUS_TEMPLATE_MISMATCH;
    }
    at += part.text.size();
    const std::string text = utf8_of(part.text);
    jlong number = 0;
    switch (part.kind) {
      case PART_LITERAL:
        if (text.empty()) break;
        if (!ConStringSymbolExp::fits(text)) {
          *reason = "LITERAL_OVER_SYMBOL_BOUND";
          return STATUS_UNSUPPORTED;
        }
        pieces.push_back(new ConStringSymbolExp(text));
        break;
      case PART_DEC_INT:
      case PART_DEC_LONG: {
        const bool is_int = part.kind == PART_DEC_INT;
        if (!canonical_decimal(text, is_int, &number)) {
          *reason = "DECIMAL_NOT_CANONICAL:" + part.label;
          return STATUS_TEMPLATE_MISMATCH;
        }
        Expression *stated = is_int
            ? static_cast<Expression *>(new ConExpression((jint) number))
            : static_cast<Expression *>(new ConExpression(number));
        pieces.push_back(OpStrExpression::to_string(
            hole(part, is_int ? T_INT : T_LONG, constant(stated), holes)));
        break;
      }
      case PART_BOOL:
        if (text != "true" && text != "false") {
          *reason = "BOOLEAN_NOT_CANONICAL:" + part.label;
          return STATUS_TEMPLATE_MISMATCH;
        }
        pieces.push_back(OpStrExpression::to_string(hole(
            part, T_BOOLEAN,
            constant(new ConExpression((jboolean) (text == "true"))),
            holes)));
        break;
      default: {
        ReturnedValue stated;
        if (text.size() > SFV::MAX_RETURNED_STRING_BYTES) {
          stated.kind = ReturnedValue::TRUNCATED_STRING;
          stated.length = (int) text.size();
        } else {
          stated.kind = ReturnedValue::STRING;
          stated.content = text;
        }
        pieces.push_back(hole(part, T_OBJECT, stated, holes));
        break;
      }
    }
  }
  if (at != content.size()) {
    *reason = "TEXT_MISMATCH";
    return STATUS_TEMPLATE_MISMATCH;
  }
  if (holes->empty()) {
    *reason = "NO_HOLE";
    return STATUS_TEMPLATE_MISMATCH;
  }
  *expression = new OpStrExpression("concat", pieces);
  return STATUS_OK;
}

// Whether what a mint would land on already states an expression: for a
// value, an entry or a position the leaf object (a String another decode or
// the program gave one, a box whose value has one); for a field or an
// element the slot (the owner's field shadow or the projection an input
// owner's unwritten field reads; an element a recorded state names, or any
// element of an array that is itself an input).
bool carries_expression(const Leaf &leaf) {
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  if (leaf.kind == LeafBroker::SLOT_FIELD) {
    SymInstance *owner = heap->find_sym_inst(leaf.holder());
    return owner != NULL
        && (owner->get(leaf.offset) != NULL
            || (owner->demand_symbolic_fields_enabled()
                && !owner->field_written(leaf.offset)));
  }
  if (leaf.kind == LeafBroker::SLOT_ELEMENT) {
    arrayOop array = arrayOop(leaf.holder());
    SymArr *shadow = heap->find_sym_array(array);
    if (shadow != NULL && shadow->has_semantic_expression()) return true;
    Expression *state = heap->find_container_state(array);
    if (state == NULL) return false;
    // What slot_shadow would build (the recorded write, or a READ of the
    // state), decided without building it.
    Expression *stored = NULL;
    const ContainerSupport::MemberAnswer answer =
        ContainerSupport::element_answer(array, shadow, state, leaf.index,
                                         &stored);
    return answer == ContainerSupport::MEMBER_RECORDED
        || answer == ContainerSupport::MEMBER_UNDECIDED;
  }
  SymInstance *instance = heap->find_sym_inst(leaf.object());
  if (instance == NULL) return false;
  if (leaf.string()) return instance->get_ref_exp() != NULL;
  return instance->get(java_lang_boxing_object::value_offset_in_bytes(
      leaf.sort)) != NULL;
}

// Refuses a mint that would put an expression where it does not belong to
// this leaf alone, or would replace one: a JVM-wide holder or landing object
// (SHARED: every holder in the JVM would read it), a versioned location or a
// container with a recorded state (TRACKED_CONTAINER: the recording, not the
// leaf, states it), a slot or object that already carries an expression
// (SHADOWED).  A decoded graph is fresh, so none of these is its own.
Status fresh(const Leaf &leaf, std::string *reason) {
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  if (leaf.kind != LeafBroker::SLOT_VALUE && jvm_shared_object(leaf.holder())) {
    *reason = "HOLDER_JVM_SHARED:" + class_of(leaf.holder());
    return STATUS_SHARED;
  }
  if (leaf.kind == LeafBroker::SLOT_FIELD) {
    oop owner = leaf.holder();
    if (owner->is_symbolic()
        && SFV::is_tracked(SFV::Location(owner->get_sym_rid(), leaf.offset,
                                         SFV::LOC_INSTANCE_FIELD))) {
      *reason = "FIELD_TRACKED";
      return STATUS_TRACKED_CONTAINER;
    }
  } else if (leaf.kind == LeafBroker::SLOT_ENTRY
      || leaf.kind == LeafBroker::SLOT_POSITION) {
    if (heap->find_container_state(leaf.holder()) != NULL) {
      *reason = "CONTAINER_HAS_STATE";
      return STATUS_TRACKED_CONTAINER;
    }
  } else if (leaf.kind == LeafBroker::SLOT_ELEMENT) {
    arrayOop array = arrayOop(leaf.holder());
    if (array->is_symbolic()
        && (SFV::is_tracked(SFV::Location(array->get_sym_rid(), leaf.index,
                                          SFV::LOC_ARRAY_ELEMENT))
            || SFV::is_tracked(ContainerSupport::state_location(array)))) {
      *reason = "ELEMENT_VERSIONED";
      return STATUS_TRACKED_CONTAINER;
    }
  }
  if (leaf.lands_on_object() && jvm_shared_object(leaf.object())) {
    *reason = "JVM_SHARED:" + class_of(leaf.object());
    return STATUS_SHARED;
  }
  if (carries_expression(leaf)) {
    *reason = leaf.lands_on_object()
        ? "OBJECT_CARRIES_EXPRESSION:" + class_of(leaf.object())
        : std::string("SLOT_CARRIES_EXPRESSION");
    return STATUS_SHADOWED;
  }
  return STATUS_OK;
}

// Installs the expression where the leaf's reader will find it: the slot
// for a field or an element, the object for a value, an entry or a
// position.  A field mint is a write of it, versioned like a putfield.
bool land(const Leaf &leaf, Expression *expression, std::string *reason) {
  SessionSymbolicHeap *heap = GlobalSymbolicSession::heap();
  if (leaf.kind == LeafBroker::SLOT_FIELD) {
    SymInstance *owner = heap->get_or_alloc_sym_inst(leaf.holder());
    if (owner == NULL) {
      *reason = "NO_OWNER_SHADOW";
      return false;
    }
    owner->mark_field_written(leaf.offset);
    owner->set_sym_exp(leaf.offset, expression);
    if (owner->get(leaf.offset) != expression) {
      // A String or builder owner keeps no field shadows.
      *reason = "OWNER_KEEPS_NO_FIELD:" + class_of(leaf.holder());
      return false;
    }
    owner->mark_semantic_expression();
    Expression *guard = ConcolicMngr::has_active_context()
        ? ConcolicMngr::ctx->path_guard() : NULL;
    SFV::publish_held(
        SFV::Location(owner->get_sym_rid(), leaf.offset,
                      SFV::LOC_INSTANCE_FIELD),
        SFV::Cell(leaf.holder(), leaf.cell, leaf.boxed_field), expression,
        guard, SFV::VERSION_WRITE);
    return true;
  }
  if (leaf.kind == LeafBroker::SLOT_ELEMENT) {
    arrayOop array = arrayOop(leaf.holder());
    // Named: every other element stays the heap's own under the writes the
    // state records (ContainerSupport::element_answer).
    if (heap->get_or_alloc_sym_array(array, NULL, true) == NULL) {
      *reason = "NO_ARRAY_SHADOW";
      return false;
    }
    const jlong word = leaf.cell == T_OBJECT
        ? (jlong) heap->name_reference(leaf.object()) : leaf.bits;
    heap->write_array_element(array, leaf.index, expression,
                              ElementWord(true, word));
    return true;
  }
  SymInstance *instance = heap->get_or_alloc_sym_inst(leaf.object());
  if (instance == NULL) {
    *reason = "NO_LEAF_SHADOW";
    return false;
  }
  if (leaf.string()) {
    instance->set_ref_exp(expression);
  } else {
    instance->set_sym_exp(
        java_lang_boxing_object::value_offset_in_bytes(leaf.sort),
        expression);
    instance->mark_semantic_expression();
  }
  return true;
}

}  // namespace

std::string LeafBroker::export_leaf(Handle parent, jint slot_kind,
                                    Handle slot) {
  ResourceMark rm;
  Answer answer("VM_LEAF_EXPORT", slot_kind);
  if (!ConcolicMngr::may_use_session_heap()) {
    return answer.status(STATUS_NO_SESSION, std::string()).finish();
  }
  Leaf leaf;
  std::string reason;
  Status status = locate(parent, slot_kind, slot, &leaf, &reason);
  // A null leaf is absent from the message, whatever its slot's shadow.
  if (status == STATUS_OK && leaf.null()) status = STATUS_NULL_LEAF;
  if (status != STATUS_OK) return answer.status(status, reason).finish();

  const char *source = "SLOT";
  Expression *expression = slot_shadow(leaf);
  if (expression == NULL) {
    source = "OBJECT";
    expression = own_shadow(leaf);
  }
  if (expression == NULL) {
    status = statable(leaf, &reason);
    if (status != STATUS_OK) {
      JsonWriter &writer = answer.status(status, reason).writer();
      leaf_value(leaf).serialize(writer, "concrete");
      return answer.finish();
    }
    source = "CONSTANT";
    status = STATUS_CONSTANT;
    expression = typed_constant(leaf);
  }
  // The export's own endpoint identity; a peek is no event of the log.
  const jlong export_event = GlobalSymbolicSession::next_event_id();
  JsonWriter &writer = answer.status(status, std::string()).writer();
  writer.Key("source");
  writer.String(source);
  writer.Key("exportEvent");
  writer.Int64(export_event);
  const std::string type = java_type(leaf);
  if (!type.empty()) {
    writer.Key("javaType");
    writer.String(type.c_str());
  }
  writer.Key("expression");
  if (expression == NULL) {
    writer.Null();
  } else {
    expression->serialize(writer);
  }
  leaf_value(leaf).serialize(writer, "concrete");
  return answer.finish();
}

std::string LeafBroker::mint_leaf(Handle parent, jint slot_kind, Handle slot,
                                  Handle template_json) {
  ResourceMark rm;
  Answer answer("VM_LEAF_MINT", slot_kind);
  if (!ConcolicMngr::may_use_session_heap()) {
    return answer.status(STATUS_NO_SESSION, std::string()).finish();
  }
  std::string reason;
  std::vector<Part> parts;
  if (!parse_template(template_json(), &parts, &reason)) {
    return answer.status(STATUS_MALFORMED_TEMPLATE, reason).finish();
  }
  Leaf leaf;
  Status status = locate(parent, slot_kind, slot, &leaf, &reason);
  if (status == STATUS_OK) status = statable(leaf, &reason);
  if (status == STATUS_OK) status = fresh(leaf, &reason);
  std::vector<Hole> holes;
  Expression *expression = NULL;
  if (status == STATUS_OK) {
    status = build(leaf, parts, &holes, &expression, &reason);
  }
  if (status == STATUS_OK && !land(leaf, expression, &reason)) {
    status = STATUS_UNSUPPORTED;
  }
  if (status != STATUS_OK) return answer.status(status, reason).finish();

  // A mint is an input: it opens this thread's path-condition gate, as
  // every mint does.  It records no condition.
  if (ConcolicMngr::has_active_context()) {
    ConcolicMngr::ctx->set_pc_admitted(true);
  }
  JsonWriter &writer = answer.status(STATUS_OK, std::string()).writer();
  writer.Key("javaType");
  writer.String(java_type(leaf).c_str());
  writer.Key("holes");
  writer.StartArray();
  for (size_t index = 0; index < holes.size(); ++index) {
    const Hole &minted = holes[index];
    writer.StartObject();
    writer.Key("label");
    writer.String(minted.part->label.c_str());
    writer.Key("kind");
    writer.String(PART_KIND_NAMES[minted.part->kind]);
    writer.Key("exp");
    writer.String(minted.symbol->name().c_str());
    writer.Key("javaType");
    writer.String(minted.java_type.c_str());
    minted.symbol->value().serialize(writer);
    writer.EndObject();
  }
  writer.EndArray();
  writer.Key("expression");
  expression->serialize(writer);
  return answer.finish();
}

#endif // ENABLE_CONCOLIC
