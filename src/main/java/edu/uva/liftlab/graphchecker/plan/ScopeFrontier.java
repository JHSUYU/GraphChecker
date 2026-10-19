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

import static edu.uva.liftlab.graphchecker.plan.StaticScopeMap.text;

public final class ScopeFrontier {
    public static final String FILE = "scope_frontier.jsonl";
    public static final String CALLEE = "CALLEE";
    public static final String FIELD = "FIELD";
    public static final String FORMAL = "FORMAL";
    static final String IO = "IO";
    private static final Pattern FORMAL_CELL = Pattern.compile(
            "(<[^>]+>)\\.param\\d+:(boolean|byte|char|short|int|long|float"
                    + "|double|java\\.lang\\.String)");

    private ScopeFrontier() {
    }

    public static List<JsonObject> rows(
            List<Map<String, Object>> edges, Predicate<String> analysed,
            Collection<String> rootCallees,
            Map<String, StaticScopeMap.Demanded> demanded) {
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
                    && !rootCallees.contains(callee)) {
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
        for (Map.Entry<String, StaticScopeMap.Demanded> io
                : demanded.entrySet()) {
            if (IO.equals(io.getValue().kind)) {
                add(found, CALLEE, io.getKey(), io.getValue().distance);
            }
        }
        List<JsonObject> rows = new ArrayList<>(found.values());
        for (JsonObject row : rows) {
            StaticScopeMap.Demanded demand = demanded.get(
                    row.get("signature").getAsString());
            if (demand != null) row.addProperty("demand", demand.kind);
        }
        rows.sort(Comparator.comparing((JsonObject row) -> !row.has("demand"))
                .thenComparingInt(row -> row.get("distance").getAsInt())
                .thenComparing(row -> row.get("kind").getAsString())
                .thenComparing(row -> row.get("signature").getAsString()));
        return rows;
    }

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
}
