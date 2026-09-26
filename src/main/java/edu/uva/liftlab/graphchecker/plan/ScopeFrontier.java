package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

/**
 * Where the fatal slice stops at the analysis scope (SYMBOL-SCOPE §2), the
 * input of {@link ScopeGrowth}: a {@code CALLEE} whose return the slice
 * demands but whose body is not the analysed program's (its class is out of
 * scope, or it is abstract and no class in scope implements it), and every
 * {@code FIELD} the slice reads or stores, since its owner or one of its
 * writers may be out of scope.  A clock callee is a root, not a frontier.
 *
 * <p>Callers are no frontier: a caller moves the region root, and with it the
 * identity of the occurrence under test, so a formal no caller in scope feeds
 * stays pinned to its recording.  Each row carries its {@code distance}, the
 * edges from its cell to the throw, and the rows come nearest first.</p>
 */
public final class ScopeFrontier {
    public static final String FILE = "scope_frontier.jsonl";
    public static final String CALLEE = "CALLEE";
    public static final String FIELD = "FIELD";
    /** The distance of a cell the throw does not depend on. */
    private static final int UNREACHED = Integer.MAX_VALUE;

    private ScopeFrontier() {
    }

    /**
     * @param analysed whether a callee's body is the analysed program's: a
     *                 concrete method of a class in scope
     */
    public static List<JsonObject> rows(List<Map<String, Object>> edges,
                                        Predicate<String> analysed,
                                        Collection<String> clockCallees) {
        Map<String, Integer> distance = distances(edges);
        Map<String, JsonObject> found = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            Integer at = distance.get(text(edge.get("toCell")));
            int hops = at == null ? UNREACHED : at;
            String callee = text(edge.get("invoke"));
            if ("call_return".equals(text(edge.get("kind")))
                    && !callee.isEmpty() && !analysed.test(callee)
                    && !clockCallees.contains(callee)) {
                add(found, CALLEE, callee, hops);
            }
            String field = StaticScopeMap.field(edge);
            if (!field.isEmpty()) add(found, FIELD, field, hops);
        }
        List<JsonObject> rows = new ArrayList<>(found.values());
        rows.sort(Comparator.comparingInt((JsonObject row)
                        -> row.get("distance").getAsInt())
                .thenComparing(row -> row.get("kind").getAsString())
                .thenComparing(row -> row.get("signature").getAsString()));
        return rows;
    }

    /** Each cell's edges to the throw: a breadth-first walk back from it. */
    private static Map<String, Integer> distances(
            List<Map<String, Object>> edges) {
        Map<String, List<String>> into = new LinkedHashMap<>();
        Deque<String> frontier = new ArrayDeque<>();
        Map<String, Integer> distance = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            String to = text(edge.get("toCell"));
            into.computeIfAbsent(to, ignored -> new ArrayList<>())
                    .add(text(edge.get("fromCell")));
            if (to.contains("#exception:") && distance.put(to, 0) == null) {
                frontier.add(to);
            }
        }
        while (!frontier.isEmpty()) {
            String cell = frontier.poll();
            for (String from : into.getOrDefault(cell,
                    new ArrayList<String>())) {
                if (distance.containsKey(from)) continue;
                distance.put(from, distance.get(cell) + 1);
                frontier.add(from);
            }
        }
        return distance;
    }

    private static void add(Map<String, JsonObject> found, String kind,
                            String signature, int distance) {
        JsonObject row = found.get(kind + "|" + signature);
        if (row != null && row.get("distance").getAsInt() <= distance) return;
        row = new JsonObject();
        row.addProperty("kind", kind);
        row.addProperty("signature", signature);
        row.addProperty("distance", distance);
        found.put(kind + "|" + signature, row);
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value).trim();
    }
}
