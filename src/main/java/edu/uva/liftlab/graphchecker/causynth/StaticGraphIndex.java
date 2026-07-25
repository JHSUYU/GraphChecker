package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

/** Input-order-preserving indexes over finalized static edge rows. */
final class StaticGraphIndex {
    private static final Pattern DECLARED_FIELD = Pattern.compile(
            "^<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>$");
    private final List<Map<String, Object>> edges;
    private final Map<String, List<Map<String, Object>>> byMethod;
    private final Map<String, List<Map<String, Object>>> incoming;
    private final Map<String, List<Map<String, Object>>> outgoing;
    private final Map<String, List<Map<String, Object>>> byId;
    private final Map<String, List<String>> inputsByMethod =
            new LinkedHashMap<>();
    private final Map<String, List<String>> outputsByMethod =
            new LinkedHashMap<>();
    private final Map<String, List<String>> sitesByMethod =
            new LinkedHashMap<>();
    private final Set<String> symbolicMethods = new LinkedHashSet<>();

    StaticGraphIndex(List<Map<String, Object>> source) {
        edges = source;
        byMethod = index("method");
        incoming = index("toCell");
        outgoing = index("fromCell");
        byId = index("id");
        indexMethodFacts();
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

    Set<String> methods() {
        return inputsByMethod.keySet();
    }

    boolean hasMethod(String method) {
        return inputsByMethod.containsKey(method);
    }

    boolean requiresSymbolicExecution(String method) {
        return symbolicMethods.contains(method);
    }

    List<String> inputs(String method) {
        return inputsByMethod.getOrDefault(method, Collections.emptyList());
    }

    List<String> outputs(String method) {
        return outputsByMethod.getOrDefault(method, Collections.emptyList());
    }

    List<String> sites(String method) {
        return sitesByMethod.getOrDefault(method, Collections.emptyList());
    }

    private void indexMethodFacts() {
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : byMethod.entrySet()) {
            String method = entry.getKey();
            if (method.isEmpty()) continue;
            Set<String> inputs = new LinkedHashSet<>();
            Set<String> outputs = new LinkedHashSet<>();
            Set<String> heapInputs = new LinkedHashSet<>();
            Set<String> environmentInputs = new LinkedHashSet<>();
            Set<String> transfers = new LinkedHashSet<>();
            Set<String> sites = new LinkedHashSet<>();
            boolean guard = false;
            boolean exception = false;
            for (Map<String, Object> edge : entry.getValue()) {
                String from = key(edge, "fromCell");
                String to = key(edge, "toCell");
                String transfer = key(edge, "transferKind");
                if (!from.isEmpty()) inputs.add(from);
                if (!to.isEmpty()) outputs.add(to);
                if (!transfer.isEmpty()) transfers.add(transfer);
                String site = key(edge, "siteId");
                if (!site.isEmpty()) sites.add(site);
                if ("HEAP_READ".equals(transfer)
                        || "HEAP_LOOKUP".equals(transfer)
                        || from.contains("#field:")
                        || DECLARED_FIELD.matcher(from).matches()) {
                    heapInputs.add(from);
                }
                guard |= "GUARD".equals(transfer);
                exception |= "EXCEPTION".equals(transfer);
                String unit = key(edge, "unit").toLowerCase(Locale.ROOT);
                if (unit.contains("time.now")
                        || unit.contains("currenttimemillis")
                        || unit.contains("nanotime")) {
                    environmentInputs.add("environment.now");
                }
            }
            Set<String> liveIns = new LinkedHashSet<>(inputs);
            liveIns.removeAll(outputs);
            for (String input : inputs) {
                if (input.contains(".param") || input.contains("@this")
                        || input.contains("#field:")
                        || DECLARED_FIELD.matcher(input).matches()) {
                    liveIns.add(input);
                }
            }
            liveIns.addAll(heapInputs);
            liveIns.addAll(environmentInputs);
            inputsByMethod.put(method, sorted(liveIns));
            outputsByMethod.put(method, sorted(outputs));
            sitesByMethod.put(method, sorted(sites));
            if (transfers.contains("COMPUTE") || guard || exception
                    || transfers.contains("HEAP_WRITE")
                    || transfers.contains("MODEL_TRANSFORM")
                    || transfers.contains("PROTOCOL_TRANSFER")
                    || transfers.contains("CONSTRUCT")
                    || transfers.contains("UNKNOWN")
                    || transfers.contains("HEAP_LOOKUP")
                    && (guard || exception)) {
                symbolicMethods.add(method);
            }
        }
    }

    private Map<String, List<Map<String, Object>>> index(String field) {
        Map<String, List<Map<String, Object>>> result = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            result.computeIfAbsent(key(edge, field),
                    ignored -> new ArrayList<>()).add(edge);
        }
        return result;
    }

    private static String key(Map<String, Object> edge, String field) {
        Object value = edge.get(field);
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static List<String> sorted(Set<String> values) {
        List<String> result = new ArrayList<>(values);
        Collections.sort(result);
        return result;
    }
}
