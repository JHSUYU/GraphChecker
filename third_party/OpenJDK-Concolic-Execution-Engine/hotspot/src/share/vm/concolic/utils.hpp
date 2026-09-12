#ifndef SHARE_VM_CONCOLIC_UTILS_HPP
#define SHARE_VM_CONCOLIC_UTILS_HPP

#ifdef ENABLE_CONCOLIC

#define CHARACTER_VALUE_FIELD_INDEX 65
#define BOOLEAN_VALUE_FIELD_INDEX 3
#define BYTE_VALUE_FIELD_INDEX 3
#define INTEGER_VALUE_FIELD_INDEX 7
#define SHORT_VALUE_FIELD_INDEX 3
#define LONG_VALUE_FIELD_INDEX 3
#define FLOAT_VALUE_FIELD_INDEX 11
#define DOUBLE_VALUE_FIELD_INDEX 11

#include "oops/klass.inline.hpp"
#include "oops/oop.inline.hpp"
#include "runtime/handles.hpp"

namespace OopUtils {

bool is_java_string_interned(oop str_obj);

typeArrayOop java_string_to_char_array(oop str_obj);

Klass* get_fd_by_name(oop obj, const std::string &name, const std::string &signature, fieldDescriptor& ret_fd);
Klass* get_local_fd_by_name(
    oop obj, const std::string &declaring_class, const std::string &name,
    const std::string &signature, fieldDescriptor& ret_fd);

// Only the reference-typed lookup is used (by key_of_map_node below); the
// nine primitive variants this macro also generated had no caller.
oop obj_field_by_name(oop obj, const std::string &name,
                      const std::string &signature);


/**
 * Do not forget to use ResourceMark before this function call!
 */
const char *java_string_to_c(oop str_obj);
jchar java_char_to_c(oop char_obj);
jboolean java_boolean_to_c(oop bool_obj);
jbyte java_byte_to_c(oop byte_obj);
jint java_int_to_c(oop int_obj);
jshort java_short_to_c(oop short_obj);
jlong java_long_to_c(oop long_obj);
jfloat java_float_to_c(oop float_obj);
jdouble java_double_to_c(oop double_obj);

oop bigd_to_java_string(oop bigd);

// The KEY oop of a Map.Entry node (HashMap$Node / LinkedHashMap$Entry).
// removeExpiredKeys iterates entrySet() and never calls e.getKey(), so a
// conditional removal recovers the map key from the entry directly.
oop key_of_map_node(oop node_obj);

} // namespace OopUtils

namespace StringUtils {
  void replaceAll(std::string& str, const std::string& from, const std::string& to);
}
#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_UTILS_HPP
