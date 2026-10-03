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
  static void seed_callback(MethodSymbolizerHandle &call, sym_rid_t receiver,
                            const std::vector<oop> &arguments,
                            exp_list_t *seeds, Expression **key);
public:
  static bool invoke_method_helper(MethodSymbolizerHandle &handle);
  static Expression *finish_method_helper(MethodSymbolizerHandle &handle);

  static void init_register_class(MethodSymbolizer *m_symbolizer);

  /** What a view's members are, by its class: a key view's (or a hash
   *  set's) keys, an entry view's entries, a values view's values. */
  enum ViewKind { VIEW_NONE, VIEW_KEYS, VIEW_ENTRIES, VIEW_VALUES };
  static ViewKind view_kind(oop view);
  /**
   * One member a callback visits on a view of a map whose state is `state`
   * (NULL for none): an entry is ENTRY(state, k), whose getKey/getValue
   * are k and READ(state, k); a key is itself (`key_expression`); a value
   * is its own semantic value.  `*key` names the visited key, or stays
   * NULL for a value.  The seeding forEach/removeIf and a stream share.
   */
  static Expression *visited_member(ViewKind kind, Expression *state,
                                    Expression *owner, oop member,
                                    Expression **key);
};

#endif // ENABLE_CONCOLIC
#endif // SHARE_VM_CONCOLIC_REFERENCE_SYMBOLICMAP_HPP
