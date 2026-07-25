package edu.uva.liftlab.graphchecker.causynth;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Canonical persisted schema for static region rows. */
final class StaticRegionArtifactSchema {
    static final int VERSION = 1;

    private StaticRegionArtifactSchema() {
    }

    static List<Map<String, Object>> regions(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> staticEdges) {
        Set<String> edgeIds = ids(staticEdges, "id",
                "static dataflow edge");
        for (Map<String, Object> region : regions) {
            Object slices = region.get("outputSlices");
            if (!(slices instanceof Collection<?>)) continue;
            for (Object value : (Collection<?>) slices) {
                if (!(value instanceof Map<?, ?>)) {
                    throw new IllegalStateException(
                            "outputSlices contains a non-object");
                }
                Set<String> references = ids(
                        ((Map<?, ?>) value).get("causalEdgeIds"),
                        "output slice causal edge");
                if (!edgeIds.containsAll(references)) {
                    references.removeAll(edgeIds);
                    throw new IllegalStateException(
                            "output slice references missing edges: "
                                    + references);
                }
            }
        }
        return regions;
    }

    static List<Map<String, Object>> regionEdges(
            List<Map<String, Object>> edges) {
        return edges;
    }

    private static Set<String> ids(List<Map<String, Object>> rows,
                                   String field, String description) {
        Set<String> result = new LinkedHashSet<>();
        for (Map<String, Object> row : rows) {
            String id = string(row.get(field));
            if (id.isEmpty() || !result.add(id)) {
                throw new IllegalStateException(description
                        + " has an empty or duplicate id: " + id);
            }
        }
        return result;
    }

    private static Set<String> ids(Object values, String description) {
        Set<String> result = new LinkedHashSet<>();
        if (!(values instanceof Collection<?>)) return result;
        for (Object value : (Collection<?>) values) {
            String id = string(value);
            if (id.isEmpty() || !result.add(id)) {
                throw new IllegalStateException(description
                        + " has an empty or duplicate id: " + id);
            }
        }
        return result;
    }

    private static String string(Object value) {
        return value == null ? "" : String.valueOf(value);
    }
}
