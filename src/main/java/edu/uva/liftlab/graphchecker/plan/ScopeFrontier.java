package edu.uva.liftlab.graphchecker.plan;

import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Where the fatal slice stops at the analysis scope (SYMBOL-SCOPE §2), the
 * input of {@link ScopeGrowth}:
 * <ul>
 *   <li>{@code CALLEE}: a callee whose return the slice demands but whose body
 *       is not the analysed program's (its class is out of scope, or it is
 *       abstract and no class in scope implements it);</li>
 *   <li>{@code FIELD}: a field the slice reads or stores, since its owner or
 *       one of its writers may be out of scope;</li>
 *   <li>{@code FORMAL}: a method whose primitive or string formal the slice
 *       demands only through a field -- a writer's value, whose callers are
 *       writers too.  A formal of any other type hands over an object whose
 *       state is its own frontier, or bytes to decode: a payload, F3's.</li>
 * </ul>
 * A formal the throw depends on without a field in between is on the target's
 * own call chain: its callers would move the region root, the identity of the
 * occurrence under test, so it stays pinned to its recording.  A clock callee
 * is a root, not a frontier, and a cell the throw does not depend on (a
 * declared wire flow's or fault's own seed) is no part of the slice.
 *
 * <p>Each row carries its {@code distance}, the edges from its cell to the
 * throw's guards (the thrown value's own construction, its message, is not
 * the fatal condition), and the rows come nearest first.</p>
 */
public final class ScopeFrontier {
    public static final String FILE = "scope_frontier.jsonl";
    public static final String CALLEE = "CALLEE";
    public static final String FIELD = "FIELD";
    public static final String FORMAL = "FORMAL";
    private static final Pattern FORMAL_CELL = Pattern.compile(
            "(<[^>]+>)\\.param\\d+:(boolean|byte|char|short|int|long|float"
                    + "|double|java\\.lang\\.String)");

    private ScopeFrontier() {
    }

    /**
     * @param analysed whether a callee's body is the analysed program's: a
     *                 concrete method of a class in scope
     */
    public static List<JsonObject> rows(List<Map<String, Object>> edges,
                                        Predicate<String> analysed,
                                        Collection<String> clockCallees) {
        Map<String, List<String>> into = new LinkedHashMap<>();
        Set<String> fields = new LinkedHashSet<>();
        Set<String> sinks = new LinkedHashSet<>();
        for (Map<String, Object> edge : edges) {
            String to = text(edge.get("toCell"));
            if (to.contains("#exception:")) sinks.add(to);
            if ("exception_throw".equals(text(edge.get("kind")))) continue;
            into.computeIfAbsent(to, ignored -> new ArrayList<>())
                    .add(text(edge.get("fromCell")));
            String field = StaticScopeMap.field(edge);
            if (!field.isEmpty()) fields.add(field);
        }
        Map<String, Integer> distance = walk(into, sinks,
                Collections.<String>emptySet());
        Set<String> ownChain = walk(into, sinks, fields).keySet();
        Map<String, JsonObject> found = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            Integer hops = distance.get(text(edge.get("toCell")));
            if (hops == null) continue;
            String callee = text(edge.get("invoke"));
            if ("call_return".equals(text(edge.get("kind")))
                    && !callee.isEmpty() && !analysed.test(callee)
                    && !clockCallees.contains(callee)) {
                add(found, CALLEE, callee, hops);
            }
            String field = StaticScopeMap.field(edge);
            if (!field.isEmpty()) add(found, FIELD, field, hops);
        }
        for (Map.Entry<String, Integer> cell : distance.entrySet()) {
            Matcher formal = FORMAL_CELL.matcher(cell.getKey());
            if (formal.matches() && !ownChain.contains(cell.getKey())) {
                add(found, FORMAL, formal.group(1), cell.getValue());
            }
        }
        List<JsonObject> rows = new ArrayList<>(found.values());
        rows.sort(Comparator.comparingInt((JsonObject row)
                        -> row.get("distance").getAsInt())
                .thenComparing(row -> row.get("kind").getAsString())
                .thenComparing(row -> row.get("signature").getAsString()));
        return rows;
    }

    /** Each cell's edges to a sink, walking back from the sinks and never
     *  past a cell of {@code barriers}. */
    private static Map<String, Integer> walk(Map<String, List<String>> into,
                                             Set<String> sinks,
                                             Set<String> barriers) {
        Map<String, Integer> distance = new LinkedHashMap<>();
        Deque<String> frontier = new ArrayDeque<>();
        for (String sink : sinks) {
            distance.put(sink, 0);
            frontier.add(sink);
        }
        while (!frontier.isEmpty()) {
            String cell = frontier.poll();
            if (barriers.contains(cell)) continue;
            for (String from : into.getOrDefault(cell,
                    Collections.<String>emptyList())) {
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
