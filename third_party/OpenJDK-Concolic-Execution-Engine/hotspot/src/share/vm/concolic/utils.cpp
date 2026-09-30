#ifdef ENABLE_CONCOLIC

#include <concolic/reference/symbolicStringBuilder.hpp>
#include "concolic/utils.hpp"
#include "classfile/symbolTable.hpp"
#include "concolic/fieldTraverser.hpp"
#include "concolic/reference/symbolicPrimitive.hpp"
#include "concolic/reference/symbolicString.hpp"

bool OopUtils::is_java_string_interned(oop str_obj) {
  if (str_obj == NULL) return false;
  ResourceMark rm;

  typeArrayOop char_array_obj = java_string_to_char_array(str_obj);
  // A freshly allocated String can acquire a shadow while its constructor is
  // still before the value-field write.  Such an object cannot yet be in the
  // intern table, and dereferencing its null value array would crash the VM.
  if (char_array_obj == NULL) return false;
  int length = char_array_obj->length();
  jchar *char_array = (jchar *)char_array_obj->base(T_CHAR);

  oop str_in_table = StringTable::lookup(char_array, length);
  return str_obj == str_in_table;
}

typeArrayOop OopUtils::java_string_to_char_array(oop str_obj) {
    Klass *klass;
    InstanceKlass *ik;
    if (str_obj->klass()->name()->equals(SymString::TYPE_NAME)) {
        klass = str_obj->klass();
    } else if (str_obj->klass()->name()->equals(SymStrBuilder::TYPE_NAME)){
        klass = str_obj->klass()->super();
    } else {
        tty->print_cr("Not handled type %s, returning numm", str_obj->klass()->name()->as_C_string());
//        ShouldNotReachHere();
      return NULL;
    }
  ik = (InstanceKlass *)klass;
  const int value_field_index = 0;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  typeArrayOop char_array_obj =
      (typeArrayOop)(str_obj->obj_field(field_offset));
  return char_array_obj;
}

const char *OopUtils::java_string_to_c(oop str_obj) {
  typeArrayOop char_array_obj = java_string_to_char_array(str_obj);
  if (char_array_obj != NULL) {
    int length = char_array_obj->length();
    if (str_obj->klass()->name()->equals(SymStrBuilder::TYPE_NAME)) {
      InstanceKlass *builder =
          InstanceKlass::cast(str_obj->klass()->super());
      const int count_field_index = 1;
      assert(builder->field_name(count_field_index)->equals("count"),
             "AbstractStringBuilder field 1 should be count");
      length = str_obj->int_field(
          builder->field_offset(count_field_index));
      if (length < 0 || length > char_array_obj->length()) return "";
    }
    jchar *chars = (jchar *)char_array_obj->base(T_CHAR);
    int utf8_length = UNICODE::utf8_length(chars, length);
    char *utf8 = NEW_RESOURCE_ARRAY(char, utf8_length + 1);
    UNICODE::convert_to_utf8(chars, length, utf8);
    utf8[utf8_length] = 0;
    return utf8;
  } else {
    return "";
  }
}
jchar OopUtils::java_char_to_c(oop char_obj) {
  Klass *klass = char_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jchar>::TYPE_NAME),
         "should be Character");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = CHARACTER_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return char_obj->char_field(field_offset);
}

jboolean OopUtils::java_boolean_to_c(oop bool_obj) {
  Klass *klass = bool_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jboolean>::TYPE_NAME),
         "should be Boolean");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = BOOLEAN_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return bool_obj->bool_field(field_offset);
}

jbyte OopUtils::java_byte_to_c(oop byte_obj) {
  Klass *klass = byte_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jbyte>::TYPE_NAME),
         "should be Byte");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = BYTE_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return byte_obj->byte_field(field_offset);
}

jint OopUtils::java_int_to_c(oop int_obj) {
  Klass *klass = int_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jint>::TYPE_NAME),
         "should be Integer");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = INTEGER_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return int_obj->int_field(field_offset);
}

jshort OopUtils::java_short_to_c(oop short_obj) {
  Klass *klass = short_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jshort>::TYPE_NAME),
         "should be Short");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = SHORT_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return short_obj->short_field(field_offset);
}

jlong OopUtils::java_long_to_c(oop long_obj) {
  Klass *klass = long_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jlong>::TYPE_NAME),
         "should be Long");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = LONG_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return long_obj->long_field(field_offset);
}

jfloat OopUtils::java_float_to_c(oop float_obj) {
  Klass *klass = float_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jfloat>::TYPE_NAME),
         "should be Float");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = FLOAT_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return float_obj->float_field(field_offset);
}

jdouble OopUtils::java_double_to_c(oop double_obj) {
  Klass *klass = double_obj->klass();
  assert(klass->name()->equals(SymPrimitive<jdouble>::TYPE_NAME),
         "should be Double");
  InstanceKlass *ik = (InstanceKlass *)klass;

  const int value_field_index = DOUBLE_VALUE_FIELD_INDEX;
  assert(ik->field_name(value_field_index)->equals("value"),
         "this field should be value");
  int field_offset = ik->field_offset(value_field_index);

  return double_obj->double_field(field_offset);
}

Klass *OopUtils::get_fd_by_name(oop obj, const std::string &name, const std::string &signature, fieldDescriptor& ret_fd) {
  Thread *thread = ConcolicMngr::ctx == NULL
      ? Thread::current() : ConcolicMngr::ctx->get_thread();
  TempNewSymbol field_name = SymbolTable::new_symbol(name.c_str(), thread);
  TempNewSymbol field_signature = SymbolTable::new_symbol(signature.c_str(), thread);
  return obj->klass()->find_field(field_name, field_signature, &ret_fd);
}

Klass *OopUtils::get_local_fd_by_name(
    oop obj, const std::string &declaring_class, const std::string &name,
    const std::string &signature, fieldDescriptor& ret_fd) {
  if (obj == NULL || !obj->is_instance()) return NULL;

  Thread *thread = ConcolicMngr::ctx == NULL
      ? Thread::current() : ConcolicMngr::ctx->get_thread();
  TempNewSymbol field_name = SymbolTable::new_symbol(name.c_str(), thread);
  TempNewSymbol field_signature =
      SymbolTable::new_symbol(signature.c_str(), thread);
  for (Klass *candidate = obj->klass(); candidate != NULL;
       candidate = candidate->super()) {
    if (!candidate->oop_is_instance()
        || declaring_class != candidate->external_name()) {
      continue;
    }
    InstanceKlass *holder = InstanceKlass::cast(candidate);
    return holder->find_local_field(
        field_name, field_signature, &ret_fd) ? holder : NULL;
  }
  return NULL;
}

oop OopUtils::obj_field_by_name(oop obj, const std::string &name,
                                const std::string &signature) {
  fieldDescriptor fd;
  return get_fd_by_name(obj, name, signature, fd) == NULL
      ? NULL : obj->obj_field(fd.offset());
}

oop OopUtils::bigd_to_java_string(oop bigd) {
  JavaThread* thread = ConcolicMngr::ctx->get_thread();
  InstanceKlass* instKlass = (InstanceKlass*)bigd->klass();

  Array<Method *> *methods = instKlass->methods();
//  int size = methods->size();
//  tty->print_cr("%d------", size);
//  for (int i = 0; i < size - 1; ++i) {
//    Method* method = methods->at(i);
//    tty->print("%d %p", i, method);
//    method->print_name();
//    tty->cr();
//  }

  // 121 is the index of toString() in BigDecimal
//  Method* toStringMethod = methods->at(121);
  JavaCallArguments java_args(1);
  java_args.push_oop(bigd);

  JavaValue result(T_OBJECT);
  ConcolicMngr::ctx->get_method_symbolizer().set_symbolizing_method(true);
  JavaThreadState lastState = thread->thread_state();
  // must transfer thread state to state_VM
  thread->set_thread_state(_thread_in_vm);
//  tty->print_cr("Calling big decimal to string");
  JavaCalls::call_virtual(&result, instKlass, vmSymbols::toString_name(), vmSymbols::void_string_signature(),
                          &java_args, thread);
  thread->set_thread_state(lastState);
  ConcolicMngr::ctx->get_method_symbolizer().set_symbolizing_method(false);
  oop res = (oop)result.get_jobject();
  guarantee(res->klass()->name() == vmSymbols::java_lang_String(), "should be string");
  return res;
}

jint OopUtils::int_field_by_name(oop obj, const std::string &name,
                                 bool *found) {
  if (found != NULL) *found = false;
  if (obj == NULL) return 0;
  fieldDescriptor fd;
  if (get_fd_by_name(obj, name, "I", fd) == NULL) return 0;
  if (found != NULL) *found = true;
  return obj->int_field(fd.offset());
}

oop OopUtils::list_of_iterator(oop iterator_obj) {
  if (iterator_obj == NULL) return NULL;
  oop owner = obj_field_by_name(iterator_obj, "this$0",
                                "Ljava/util/ArrayList;");
  if (owner != NULL) return owner;
  return obj_field_by_name(iterator_obj, "this$0",
                           "Ljava/util/AbstractList;");
}

jint OopUtils::last_returned_index(oop iterator_obj, bool *found) {
  return int_field_by_name(iterator_obj, "lastRet", found);
}

oop OopUtils::current_node_of_iterator(oop iterator_obj) {
  if (iterator_obj == NULL) return NULL;
  oop node = obj_field_by_name(iterator_obj, "current",
                               "Ljava/util/HashMap$Node;");
  if (node != NULL) return node;
  node = obj_field_by_name(iterator_obj, "current",
                           "Ljava/util/LinkedHashMap$Entry;");
  if (node != NULL) return node;
  return obj_field_by_name(iterator_obj, "lastReturned",
                           "Ljava/util/concurrent/ConcurrentHashMap$Node;");
}

oop OopUtils::key_of_map_node(oop node_obj) {
  if (node_obj == NULL) {
    return NULL;
  }
  // Same layout caveat as value_of_map_node: resolve the declared `key` field
  // (inherited by LinkedHashMap$Entry from HashMap$Node) by name.
  return obj_field_by_name(node_obj, "key", "Ljava/lang/Object;");
}

void StringUtils::replaceAll(std::string &str, const std::string &from, const std::string &to) {
  if (from.empty())
    return;
  size_t start_pos = 0;
  while ((start_pos = str.find(from, start_pos)) != std::string::npos) {
    str.replace(start_pos, from.length(), to);
    start_pos += to.length(); // In case 'to' contains 'from', like replacing 'x' with 'yx'
  }
}
#endif
