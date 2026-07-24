package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Immutable, input-order-preserving views over finalized static edge rows.
 *
 * <p>Rows are intentionally not validated or deduplicated here. In
 * particular, an edge id can identify several rows; callers that require a
 * unique witness must check the returned list themselves.</p>
 */
final class StaticGraphIndex {
    private final List<Map<String, Object>> edges;
    private final Map<String, List<Map<String, Object>>> byMethod;
    private final Map<String, List<Map<String, Object>>> incoming;
    private final Map<String, List<Map<String, Object>>> outgoing;
    private final Map<String, List<Map<String, Object>>> byId;

    StaticGraphIndex(List<Map<String, Object>> source) {
        edges = Collections.unmodifiableList(new ArrayList<>(source));
        byMethod = index("method");
        incoming = index("toCell");
        outgoing = index("fromCell");
        byId = index("id");
    }

    List<Map<String, Object>> edges() {
        return edges;
    }

    List<Map<String, Object>> forMethod(String method) {
        return byMethod.getOrDefault(method, Collections.emptyList());
    }

    List<Map<String, Object>> incoming(String cell) {
        return incoming.getOrDefault(cell, Collections.emptyList());
    }

    List<Map<String, Object>> outgoing(String cell) {
        return outgoing.getOrDefault(cell, Collections.emptyList());
    }

    List<Map<String, Object>> withId(String id) {
        return byId.getOrDefault(id, Collections.emptyList());
    }

    private Map<String, List<Map<String, Object>>> index(String field) {
        Map<String, List<Map<String, Object>>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            result.computeIfAbsent(key(edge, field),
                    ignored -> new ArrayList<>()).add(edge);
        }
        result.replaceAll((ignored, rows) ->
                Collections.unmodifiableList(rows));
        return Collections.unmodifiableMap(result);
    }

    private static String key(Map<String, Object> edge, String field) {
        Object value = edge.get(field);
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }
}
