package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.d3.plan.CommunicationCatalogContract;

import edu.uva.liftlab.graphchecker.d3.plan.SiteId;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;

/** Schema-preserving metadata support for static control-dependence edges. */
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
                                  Collection<Integer> reachingSuccessors,
                                  String guardCell,
                                  String definitionCell) {
        String guardSiteId = siteId(method, guardUnitIndex,
                PATH_GUARD_KIND);
        String definitionSiteId = siteId(method,
                controlledDefinitionUnitIndex, "controlled_definition");
        List<Integer> successorIndices = integerList(reachingSuccessors);
        Boolean sameCell = Boolean.valueOf(
                Objects.equals(guardCell, definitionCell));
        edge.put("guardSiteId", guardSiteId);
        Map<String, Object> added = record(edge, "controlledDefinitions",
                "controlledDefinitionSiteId", definitionSiteId, guardSiteId,
                requiredOutcome, successorIndices,
                "controlledDefinitionUnitIndex",
                controlledDefinitionUnitIndex,
                "controlledDefinitionUnit", controlledDefinitionUnit);
        if (added != null) added.put("sameCellRedefinition", sameCell);
        List<Map<String, Object>> definitions = mapList(edge,
                "controlledDefinitions");
        if (definitions.size() == 1) {
            edge.put("controlledDefinitionSiteId", definitionSiteId);
            edge.put("controlledDefinitionUnitIndex",
                    controlledDefinitionUnitIndex);
            edge.put("controlledDefinitionUnit", controlledDefinitionUnit);
            edge.put("sameCellRedefinition", sameCell);
        } else {
            edge.remove("controlledDefinitionSiteId");
            edge.remove("controlledDefinitionUnitIndex");
            edge.remove("controlledDefinitionUnit");
            edge.remove("sameCellRedefinition");
        }
        syncCommonOutcome(edge, definitions, requiredOutcome,
                successorIndices);
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
        boolean added = record(edge, "guardedMutations",
                "guardedMutationSiteId", mutationSiteId, guardSiteId,
                requiredOutcome, successorIndices,
                "method", method, "unitIndex", mutationUnitIndex) != null;
        List<Map<String, Object>> guardedMutations = mapList(edge,
                "guardedMutations");
        if (guardedMutations.size() == 1) {
            edge.put("guardedMutationSiteId", mutationSiteId);
        } else {
            edge.remove("guardedMutationSiteId");
        }
        syncCommonOutcome(edge, guardedMutations, requiredOutcome,
                successorIndices);
        return added;
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
        edge.put("effectSiteId", effectSiteId);
        boolean added = record(edge, "guardedEffects", "effectSiteId",
                effectSiteId, guardSiteId, requiredOutcome,
                successorIndices, "calleeMethod", calleeMethod,
                "effectField", effectField,
                "unitIndex", effectUnitIndex) != null;
        syncCommonOutcome(edge, mapList(edge, "guardedEffects"),
                requiredOutcome, successorIndices);
        return added;
    }

    /**
     * Appends one guarded row unless an equal one is already recorded; the
     * {@code fields} pairs sit between the site id and the outcome pair.
     * @return the row this call added, or {@code null}
     */
    private static Map<String, Object> record(
            Map<String, Object> edge, String listField, String idField,
            String siteId, String guardSiteId, Object requiredOutcome,
            List<Integer> successorIndices, Object... fields) {
        List<Map<String, Object>> rows = mapList(edge, listField);
        if (contains(rows, idField, siteId, requiredOutcome,
                successorIndices)) {
            return null;
        }
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("guardSiteId", guardSiteId);
        row.put(idField, siteId);
        for (int index = 0; index + 1 < fields.length; index += 2) {
            row.put((String) fields[index], fields[index + 1]);
        }
        row.put("requiredOutcome", requiredOutcome);
        row.put("reachingSuccessorIndices", successorIndices);
        rows.add(row);
        return row;
    }

    private static boolean contains(List<Map<String, Object>> rows,
                                    String idField, String id,
                                    Object requiredOutcome,
                                    List<Integer> successorIndices) {
        for (Map<String, Object> row : rows) {
            if (id.equals(stringValue(row.get(idField)))
                    && Objects.equals(requiredOutcome,
                    row.get("requiredOutcome"))
                    && successorIndices.equals(row.get(
                    "reachingSuccessorIndices"))) {
                return true;
            }
        }
        return false;
    }

    private static void syncCommonOutcome(Map<String, Object> edge,
                                          Collection<?> rows,
                                          Object requiredOutcome,
                                          List<Integer> successorIndices) {
        if (rows.size() == 1) {
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
            return SiteId.of(method, unitIndex);
        }
        String suffix = kind == null || kind.trim().isEmpty()
                ? "edge" : kind.trim();
        return method + "#synthetic:" + suffix;
    }
}
