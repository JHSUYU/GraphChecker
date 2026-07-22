package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Compact persisted schema for static regions.
 *
 * <p>The planner keeps its rich in-memory rows because they are useful while
 * assembling and checking a region.  The durable artifact has one canonical
 * static-dataflow edge table, however, so output slices retain edge ids rather
 * than copying the same edges a second time.
 */
final class StaticRegionArtifactSchema {
    static final int VERSION = 1;

    private static final String[][] REGION_DERIVED_COUNTS = {
            {"mandatorySeedGuardInputCount", "mandatorySeedGuardInputs"},
            {"seedGuardInputDerivationGapCount",
                    "seedGuardInputDerivationGaps"},
            {"symbolicInputPortCount", "symbolicInputs"},
            {"methodCount", "methods"}
    };
    private static final String[][] SLICE_DERIVED_COUNTS = {
            {"accessorImplementationAdmissionCount",
                    "accessorImplementationAdmissions"},
            {"causalEdgeCount", "causalEdgeIds"},
            {"methodCount", "methods"},
            {"requestedStateTransformerObligationCount",
                    "requestedStateTransformerObligations"}
    };
    private static final String[] REGION_RETIRED_ALIASES = {
            "staticRootCandidate", "rootAuthority", "rootReason",
            "rootValidation", "sinkMethods", "symbolicInputPolicy",
            "inputPortSelectionAuthority",
            "mandatorySeedGuardInputAuthority", "precision"
    };

    private StaticRegionArtifactSchema() {
    }

    static List<Map<String, Object>> regions(
            List<Map<String, Object>> regions,
            List<Map<String, Object>> staticEdges) {
        Set<String> canonicalEdgeIds = canonicalEdgeIds(staticEdges);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> original : values(regions)) {
            Map<String, Object> region = copyMap(original);
            region.put("schemaVersion", VERSION);
            remove(region, REGION_RETIRED_ALIASES);
            removeDerivedCounts(region, REGION_DERIVED_COUNTS,
                    "symbolic region");
            for (Map<String, Object> slice : maps(
                    region.get("outputSlices"))) {
                compactOutputSlice(slice, canonicalEdgeIds);
            }
            result.add(region);
        }
        return result;
    }

    static List<Map<String, Object>> regionEdges(
            List<Map<String, Object>> edges) {
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> original : values(edges)) {
            Map<String, Object> edge = copyMap(original);
            edge.put("schemaVersion", VERSION);
            edge.remove("rootValidation");
            result.add(edge);
        }
        return result;
    }

    private static void compactOutputSlice(Map<String, Object> slice,
                                           Set<String> canonicalEdgeIds) {
        removeDerivedCounts(slice, SLICE_DERIVED_COUNTS, "output slice");
        slice.remove("promotionAuthority");

        List<String> ids = strings(slice.get("causalEdgeIds"));
        Set<String> uniqueIds = new LinkedHashSet<>();
        for (String id : ids) {
            if (id.isEmpty() || !uniqueIds.add(id)
                    || !canonicalEdgeIds.contains(id)) {
                throw new IllegalStateException(
                        "output slice references a missing, empty, or "
                                + "duplicate canonical edge id: " + id);
            }
        }

        Object embeddedValue = slice.get("causalEdges");
        if (embeddedValue instanceof Collection<?>) {
            Set<String> embeddedIds = new LinkedHashSet<>();
            int embeddedCount = 0;
            for (Object item : (Collection<?>) embeddedValue) {
                if (!(item instanceof Map<?, ?>)) {
                    throw new IllegalStateException(
                            "output slice causalEdges contains a non-object");
                }
                embeddedCount++;
                Map<?, ?> edge = (Map<?, ?>) item;
                String id = firstNonBlank(string(edge.get("edgeId")),
                        string(edge.get("id")));
                if (id.isEmpty() || !embeddedIds.add(id)) {
                    throw new IllegalStateException(
                            "output slice has an empty or duplicate embedded "
                                    + "causal edge id: " + id);
                }
            }
            if (embeddedCount != ids.size()
                    || !embeddedIds.equals(uniqueIds)) {
                throw new IllegalStateException(
                        "output slice causalEdgeIds disagree with "
                                + "embedded causalEdges");
            }
        } else if (embeddedValue != null) {
            throw new IllegalStateException(
                    "output slice causalEdges is not an array");
        } else if (!ids.isEmpty()) {
            throw new IllegalStateException(
                    "output slice is missing its in-memory causal edge ledger");
        }
        slice.remove("causalEdges");
    }

    private static Set<String> canonicalEdgeIds(
            List<Map<String, Object>> staticEdges) {
        Set<String> result = new LinkedHashSet<>();
        for (Map<String, Object> edge : values(staticEdges)) {
            String id = string(edge.get("id"));
            if (id.isEmpty() || !result.add(id)) {
                throw new IllegalStateException(
                        "static dataflow catalog has an empty or duplicate "
                                + "canonical edge id: " + id);
            }
        }
        return result;
    }

    private static void removeDerivedCounts(Map<String, Object> row,
                                            String[][] fields,
                                            String context) {
        for (String[] pair : fields) {
            String countField = pair[0];
            if (!row.containsKey(countField)) {
                continue;
            }
            Object values = row.get(pair[1]);
            Object count = row.get(countField);
            if (!(values instanceof Collection<?>)
                    || !(count instanceof Number)
                    || ((Number) count).intValue()
                    != ((Collection<?>) values).size()) {
                throw new IllegalStateException(context + " "
                        + countField + " disagrees with " + pair[1]);
            }
            row.remove(countField);
        }
    }

    private static void remove(Map<String, Object> row, String[] fields) {
        for (String field : fields) {
            row.remove(field);
        }
    }

    private static List<String> strings(Object value) {
        List<String> result = new ArrayList<>();
        if (!(value instanceof Collection<?>)) {
            return result;
        }
        for (Object item : (Collection<?>) value) {
            result.add(string(item));
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    private static List<Map<String, Object>> maps(Object value) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (!(value instanceof Collection<?>)) {
            return result;
        }
        for (Object item : (Collection<?>) value) {
            if (!(item instanceof Map<?, ?>)) {
                throw new IllegalStateException(
                        "expected an array of JSON objects");
            }
            result.add((Map<String, Object>) item);
        }
        return result;
    }

    private static List<Map<String, Object>> values(
            List<Map<String, Object>> rows) {
        return rows == null ? new ArrayList<Map<String, Object>>() : rows;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> copyMap(Map<String, Object> source) {
        return (Map<String, Object>) copy(source);
    }

    private static Object copy(Object value) {
        if (value instanceof Map<?, ?>) {
            Map<String, Object> result = new LinkedHashMap<>();
            for (Map.Entry<?, ?> entry : ((Map<?, ?>) value).entrySet()) {
                result.put(string(entry.getKey()), copy(entry.getValue()));
            }
            return result;
        }
        if (value instanceof Collection<?>) {
            List<Object> result = new ArrayList<>();
            for (Object item : (Collection<?>) value) {
                result.add(copy(item));
            }
            return result;
        }
        return value;
    }

    private static String firstNonBlank(String first, String second) {
        return first.isEmpty() ? second : first;
    }

    private static String string(Object value) {
        return value == null ? "" : String.valueOf(value);
    }
}
