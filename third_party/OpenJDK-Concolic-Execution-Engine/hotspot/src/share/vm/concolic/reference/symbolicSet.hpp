#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICSET_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICSET_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/methodSymbolizerHandle.hpp"
#include "concolic/methodSymbolizer.hpp"

/**
 * The Set contract over the hash sets, which have a state of their own, and
 * a ConcurrentHashMap's KeySetView (newKeySet, keySet(v)), which is its
 * map's: a member is a key the map holds, mapped to the view's value.
 */
class SymSet {
private:
  static std::set<std::string> target_class_names;
  static std::set<std::string> init_target_class_names();
  static std::set<std::string> handle_method_names;
  static std::set<std::string> init_handle_method_names();
public:
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  static void init_register_class(MethodSymbolizer *m_symbolizer);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICSET_HPP
