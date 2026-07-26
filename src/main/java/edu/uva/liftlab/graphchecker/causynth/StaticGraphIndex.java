package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

/** Canonical input-order-preserving graph and method-fact index. */
final class StaticGraphIndex {
    private static final Pattern DECLARED_FIELD = Pattern.compile(
            "^<([^:]+):\\s+([^()<>]+)\\s+([^\\s()>]+)>$");
    private final List<Map<String, Object>> edges;
    private final Map<String, List<Map<String, Object>>> byMethod;
    private final Map<String, List<Map<String, Object>>> incoming;
    private final Map<String, List<Map<String, Object>>> outgoing;
    private final Map<String, List<Map<String, Object>>> byId;
    private final Map<String, MethodFacts> methods = new LinkedHashMap<>();
    private final Map<String, List<Map<String, Object>>> methodSets =
            new LinkedHashMap<>();

    StaticGraphIndex(List<Map<String, Object>> source) {
        edges = source;
        byMethod = new LinkedHashMap<>();
        incoming = new LinkedHashMap<>();
        outgoing = new LinkedHashMap<>();
        byId = new LinkedHashMap<>();
        for (Map<String, Object> edge : edges) {
            add(byMethod, key(edge, "method"), edge);
            add(incoming, key(edge, "toCell"), edge);
            add(outgoing, key(edge, "fromCell"), edge);
            add(byId, key(edge, "id"), edge);
        }
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

    List<Map<String, Object>> withIds(Collection<String> ids) {
        Set<String> selected = new LinkedHashSet<>(ids);
        List<Map<String, Object>> result = new ArrayList<>();
        for (Map<String, Object> edge : edges) {
            if (selected.contains(key(edge, "id"))) {
                result.add(edge);
            }
        }
        return result;
    }

    List<Map<String, Object>> forMethods(Collection<String> selected) {
        List<String> ordered = new ArrayList<>(selected);
        Collections.sort(ordered);
        String key = String.join("\n", ordered);
        List<Map<String, Object>> cached = methodSets.get(key);
        if (cached == null) {
            cached = new ArrayList<>();
            for (String method : ordered) {
                cached.addAll(forMethod(method));
            }
            methodSets.put(key, cached);
        }
        return cached;
    }

    Set<String> methods() {
        return methods.keySet();
    }

    boolean hasMethod(String method) {
        return methods.containsKey(method);
    }

    boolean requiresSymbolicExecution(String method) {
        MethodFacts facts = methods.get(method);
        return facts != null && facts.symbolic;
    }

    List<String> inputs(String method) {
        MethodFacts facts = methods.get(method);
        return facts == null ? Collections.emptyList() : facts.inputs;
    }

    List<String> outputs(String method) {
        MethodFacts facts = methods.get(method);
        return facts == null ? Collections.emptyList() : facts.outputs;
    }

    List<String> sites(String method) {
        MethodFacts facts = methods.get(method);
        return facts == null ? Collections.emptyList() : facts.sites;
    }

    private void indexMethodFacts() {
        for (Map.Entry<String, List<Map<String, Object>>> entry
                : byMethod.entrySet()) {
            String method = entry.getKey();
            if (method.isEmpty()) continue;
            Set<String> inputs = new LinkedHashSet<>();
            Set<String> outputs = new LinkedHashSet<>();
            Set<String> forcedInputs = new LinkedHashSet<>();
            Set<String> sites = new LinkedHashSet<>();
            boolean guard = false;
            boolean exception = false;
            boolean symbolic = false;
            for (Map<String, Object> edge : entry.getValue()) {
                String from = key(edge, "fromCell");
                String to = key(edge, "toCell");
                String transfer = key(edge, "transferKind");
                if (!from.isEmpty()) inputs.add(from);
                if (!to.isEmpty()) outputs.add(to);
                String site = key(edge, "siteId");
                if (!site.isEmpty()) sites.add(site);
                if ("HEAP_READ".equals(transfer)
                        || "HEAP_LOOKUP".equals(transfer)
                        || from.contains("#field:")
                        || DECLARED_FIELD.matcher(from).matches()) {
                    forcedInputs.add(from);
                }
                guard |= "GUARD".equals(transfer);
                exception |= "EXCEPTION".equals(transfer);
                symbolic |= "COMPUTE".equals(transfer)
                        || "HEAP_WRITE".equals(transfer)
                        || "MODEL_TRANSFORM".equals(transfer)
                        || "PROTOCOL_TRANSFER".equals(transfer)
                        || "CONSTRUCT".equals(transfer)
                        || "UNKNOWN".equals(transfer);
                String unit = key(edge, "unit").toLowerCase(Locale.ROOT);
                if (unit.contains("time.now")
                        || unit.contains("currenttimemillis")
                        || unit.contains("nanotime")) {
                    forcedInputs.add("environment.now");
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
            liveIns.addAll(forcedInputs);
            symbolic |= guard || exception;
            methods.put(method, new MethodFacts(sorted(liveIns),
                    sorted(outputs), sorted(sites), symbolic));
        }
    }

    private static void add(
            Map<String, List<Map<String, Object>>> index, String key,
            Map<String, Object> edge) {
        index.computeIfAbsent(key, ignored -> new ArrayList<>()).add(edge);
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

    private static final class MethodFacts {
        private final List<String> inputs;
        private final List<String> outputs;
        private final List<String> sites;
        private final boolean symbolic;

        private MethodFacts(List<String> inputs, List<String> outputs,
                            List<String> sites, boolean symbolic) {
            this.inputs = inputs;
            this.outputs = outputs;
            this.sites = sites;
            this.symbolic = symbolic;
        }
    }
}
