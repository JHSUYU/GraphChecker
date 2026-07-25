package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Schema-preserving metadata support for static control-dependence edges.
 *
 * <p>The static analyzer remains responsible for proving control dependence;
 * this class only owns the common edge retention and serialization policy.</p>
 */
final class ControlDependenceEdgeSupport {
    static final String PATH_GUARD_KIND = "path_guard_dependency";
    private ControlDependenceEdgeSupport() {
    }

    static boolean permitsSameCellEdge(String kind, String fromCell,
                                       String toCell,
                                       boolean hasConcreteGuardSite) {
        return Objects.equals(fromCell, toCell)
                && PATH_GUARD_KIND.equals(kind)
                && hasConcreteGuardSite;
    }

    static void annotatePathGuard(Map<String, Object> edge, String method,
                                  int guardUnitIndex,
                                  int controlledDefinitionUnitIndex,
                                  String controlledDefinitionUnit,
                                  Object requiredOutcome,
                                  String guardCell,
                                  String definitionCell) {
        annotatePathGuard(edge, method, guardUnitIndex,
                controlledDefinitionUnitIndex, controlledDefinitionUnit,
                requiredOutcome, Collections.emptyList(), guardCell,
                definitionCell);
    }

    static void annotatePathGuard(Map<String, Object> edge, String method,
                                  int guardUnitIndex,
                                  int controlledDefinitionUnitIndex,
                                  String controlledDefinitionUnit,
                                  Object requiredOutcome,
                                  Collection<Integer> reachingSuccessors,
                                  String guardCell,
                                  String definitionCell) {
        String guardSiteId = siteId(method, guardUnitIndex,
                PATH_GUARD_KIND);
        String definitionSiteId = siteId(method,
                controlledDefinitionUnitIndex, "controlled_definition");
        List<Integer> successorIndices = integerList(reachingSuccessors);
        edge.put("guardSiteId", guardSiteId);
        List<Map<String, Object>> definitions = mapList(edge,
                "controlledDefinitions");
        boolean present = definitions.stream().anyMatch(item ->
                definitionSiteId.equals(stringValue(
                        item.get("controlledDefinitionSiteId")))
                        && Objects.equals(requiredOutcome,
                        item.get("requiredOutcome"))
                        && successorIndices.equals(item.get(
                        "reachingSuccessorIndices")));
        if (!present) {
            Map<String, Object> definition = new LinkedHashMap<>();
            definition.put("guardSiteId", guardSiteId);
            definition.put("controlledDefinitionSiteId", definitionSiteId);
            definition.put("controlledDefinitionUnitIndex",
                    controlledDefinitionUnitIndex);
            definition.put("controlledDefinitionUnit",
                    controlledDefinitionUnit);
            definition.put("requiredOutcome", requiredOutcome);
            definition.put("reachingSuccessorIndices", successorIndices);
            definition.put("sameCellRedefinition",
                    Objects.equals(guardCell, definitionCell));
            definitions.add(definition);
        }
        if (definitions.size() == 1) {
            edge.put("controlledDefinitionSiteId", definitionSiteId);
            edge.put("controlledDefinitionUnitIndex",
                    controlledDefinitionUnitIndex);
            edge.put("controlledDefinitionUnit", controlledDefinitionUnit);
            if (requiredOutcome instanceof Boolean) {
                edge.put("requiredOutcome", requiredOutcome);
            } else {
                edge.remove("requiredOutcome");
            }
            edge.put("reachingSuccessorIndices", successorIndices);
            edge.put("sameCellRedefinition",
                    Objects.equals(guardCell, definitionCell));
        } else {
            edge.remove("controlledDefinitionSiteId");
            edge.remove("controlledDefinitionUnitIndex");
            edge.remove("controlledDefinitionUnit");
            edge.remove("requiredOutcome");
            edge.remove("reachingSuccessorIndices");
            edge.remove("sameCellRedefinition");
        }
    }

    static boolean requiresSiteIdentity(String kind) {
        return kind != null && (PATH_GUARD_KIND.equals(kind)
                || kind.endsWith("_path_guard"));
    }

    static boolean annotateGuardedMutation(
            Map<String, Object> edge, String method, int guardUnitIndex,
            int mutationUnitIndex, Object requiredOutcome) {
        return annotateGuardedMutation(edge, method, guardUnitIndex,
                mutationUnitIndex, requiredOutcome, Collections.emptyList());
    }

    static boolean annotateGuardedMutation(
            Map<String, Object> edge, String method, int guardUnitIndex,
            int mutationUnitIndex, Object requiredOutcome,
            Collection<Integer> reachingSuccessors) {
        String guardSiteId = siteId(method, guardUnitIndex,
                "heap_mutation_path_guard");
        String mutationSiteId = siteId(method, mutationUnitIndex,
                "field_mutation");
        List<Integer> successorIndices = integerList(reachingSuccessors);
        edge.put("guardSiteId", guardSiteId);
        List<Map<String, Object>> guardedMutations = mapList(edge,
                "guardedMutations");
        boolean present = false;
        for (Map<String, Object> item : guardedMutations) {
            if (mutationSiteId.equals(stringValue(
                    item.get("guardedMutationSiteId")))
                    && Objects.equals(requiredOutcome,
                    item.get("requiredOutcome"))
                    && successorIndices.equals(item.get(
                    "reachingSuccessorIndices"))) {
                present = true;
                break;
            }
        }
        if (!present) {
            Map<String, Object> item = new LinkedHashMap<>();
            item.put("guardSiteId", guardSiteId);
            item.put("guardedMutationSiteId", mutationSiteId);
            item.put("method", method);
            item.put("unitIndex", mutationUnitIndex);
            item.put("requiredOutcome", requiredOutcome);
            item.put("reachingSuccessorIndices", successorIndices);
            guardedMutations.add(item);
        }
        if (guardedMutations.size() == 1) {
            edge.put("guardedMutationSiteId", mutationSiteId);
            if (requiredOutcome instanceof Boolean) {
                edge.put("requiredOutcome", requiredOutcome);
            } else {
                edge.remove("requiredOutcome");
            }
            edge.put("reachingSuccessorIndices", successorIndices);
        } else {
            edge.remove("guardedMutationSiteId");
            edge.remove("requiredOutcome");
            edge.remove("reachingSuccessorIndices");
        }
        return !present;
    }

    static boolean annotateGuardedReceiverEffect(
            Map<String, Object> edge, String method, int guardUnitIndex,
            int effectUnitIndex, Object requiredOutcome, String calleeMethod,
            String effectField) {
        return annotateGuardedReceiverEffect(edge, method, guardUnitIndex,
                effectUnitIndex, requiredOutcome, Collections.emptyList(),
                calleeMethod, effectField);
    }

    static boolean annotateGuardedReceiverEffect(
            Map<String, Object> edge, String method, int guardUnitIndex,
            int effectUnitIndex, Object requiredOutcome,
            Collection<Integer> reachingSuccessors, String calleeMethod,
            String effectField) {
        String guardSiteId = siteId(method, guardUnitIndex,
                "receiver_field_effect_path_guard");
        String effectSiteId = siteId(method, effectUnitIndex,
                "method_receiver_field_effect");
        List<Integer> successorIndices = integerList(reachingSuccessors);
        edge.put("guardSiteId", guardSiteId);
        edge.put("calleeMethod", calleeMethod);
        edge.put("effectField", effectField);
        edge.put("effectSiteId", effectSiteId);
        edge.put("effectAuthority",
                "GLOBAL_WRITER_INDEX_AND_EXACT_CALLSITE_CONTROL_DEPENDENCE_V1");
        List<Map<String, Object>> effects = mapList(edge, "guardedEffects");
        boolean present = effects.stream().anyMatch(item ->
                effectSiteId.equals(stringValue(item.get("effectSiteId")))
                        && Objects.equals(requiredOutcome,
                        item.get("requiredOutcome"))
                        && successorIndices.equals(item.get(
                        "reachingSuccessorIndices")));
        if (!present) {
            Map<String, Object> item = new LinkedHashMap<>();
            item.put("guardSiteId", guardSiteId);
            item.put("effectSiteId", effectSiteId);
            item.put("calleeMethod", calleeMethod);
            item.put("effectField", effectField);
            item.put("unitIndex", effectUnitIndex);
            item.put("requiredOutcome", requiredOutcome);
            item.put("reachingSuccessorIndices", successorIndices);
            effects.add(item);
        }
        if (effects.size() == 1) {
            if (requiredOutcome instanceof Boolean) {
                edge.put("requiredOutcome", requiredOutcome);
            } else {
                edge.remove("requiredOutcome");
            }
            edge.put("reachingSuccessorIndices", successorIndices);
        } else {
            edge.remove("requiredOutcome");
            edge.remove("reachingSuccessorIndices");
        }
        return !present;
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> mapList(
            Map<String, Object> edge, String field) {
        Object existing = edge.get(field);
        if (existing instanceof List) {
            return (List<Map<String, Object>>) existing;
        }
        List<Map<String, Object>> created = new ArrayList<>();
        edge.put(field, created);
        return created;
    }

    private static List<Integer> integerList(Collection<Integer> values) {
        Set<Integer> unique = new LinkedHashSet<>();
        if (values != null) {
            for (Integer value : values) {
                if (value != null) {
                    unique.add(value);
                }
            }
        }
        return new ArrayList<>(unique);
    }

    private static String siteId(String method, int unitIndex, String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        String suffix = kind == null || kind.trim().isEmpty()
                ? "edge" : kind.trim();
        return method + "#synthetic:" + suffix;
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }
}
