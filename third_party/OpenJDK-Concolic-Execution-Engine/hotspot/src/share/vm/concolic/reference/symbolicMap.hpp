#ifndef SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICMAP_HPP
#define SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICMAP_HPP

#ifdef ENABLE_CONCOLIC

#include "concolic/defs.hpp"
#include "concolic/methodSymbolizerHandle.hpp"

/**
 * The Map contract (Map, ConcurrentMap), over every class the capability
 * table admits as a map -- HashMap, LinkedHashMap in insertion order,
 * ConcurrentHashMap, Hashtable -- with their views, iterators and entries,
 * and a map view's Collection.removeIf.  The receiver's concrete class
 * decides (ContainerSupport::capability); the method holder only routes.
 */
class SymMap {
private:
  static std::set<std::string> target_class_names;
  static std::set<std::string> init_target_class_names();
  static std::set<std::string> handle_method_names;
  static std::set<std::string> init_handle_method_names();
  static void seed_callback(MethodSymbolizerHandle &call,
                            const std::vector<oop> &arguments,
                            exp_list_t *seeds, Expression **key);
public:
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  static void init_register_class(MethodSymbolizer *m_symbolizer);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICMAP_HPP
