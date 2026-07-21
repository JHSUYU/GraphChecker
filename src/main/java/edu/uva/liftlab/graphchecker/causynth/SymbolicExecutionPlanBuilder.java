package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

/** Accumulates one method-level symbolic execution plan row. */
final class SymbolicExecutionPlanBuilder {
    private static final int MAX_PLAN_VALUES = 256;

    private final String method;
    private final Set<String> inputs = new LinkedHashSet<>();
    private final Set<String> defined = new LinkedHashSet<>();
    private final Set<String> outputs = new LinkedHashSet<>();
    private final Set<String> heapInputs = new LinkedHashSet<>();
    private final Set<String> environmentInputs = new LinkedHashSet<>();
    private final Set<String> guards = new LinkedHashSet<>();
    private final Set<String> exceptions = new LinkedHashSet<>();
    private final Set<String> possibleCallees = new LinkedHashSet<>();
    private final Set<String> transferKinds = new LinkedHashSet<>();
    private final Set<String> siteIds = new LinkedHashSet<>();
    private final Set<String> requiredModels = new LinkedHashSet<>();
    private final Set<String> reasons = new LinkedHashSet<>();
    private int edgeCount;

    SymbolicExecutionPlanBuilder(String method) {
        this.method = method;
    }

    String method() {
        return method;
    }

    void observe(Map<String, Object> edge, String transfer, String siteId) {
        edgeCount++;
        String from = stringValue(edge.get("fromCell"));
        String to = stringValue(edge.get("toCell"));
        String unit = stringValue(edge.get("unit"));
        String invoke = stringValue(edge.get("invoke"));
        if (!from.isEmpty()) {
            inputs.add(from);
        }
        if (!to.isEmpty()) {
            outputs.add(to);
            defined.add(to);
        }
        transferKinds.add(transfer);
        siteIds.add(siteId);
        if (!invoke.isEmpty()) {
            possibleCallees.add(invoke);
        }
        if ("HEAP_READ".equals(transfer) || "HEAP_LOOKUP".equals(transfer)
                || from.contains("#field:")
                || looksLikeFieldSignature(from)) {
            heapInputs.add(from);
        }
        if ("GUARD".equals(transfer)) {
            guards.add(firstNonBlank(unit, to, siteId));
            reasons.add("relevant branch guard");
        }
        if ("EXCEPTION".equals(transfer)) {
            exceptions.add(firstNonBlank(unit, to, siteId));
            reasons.add("relevant exceptional path");
        }
        if ("HEAP_WRITE".equals(transfer)) {
            reasons.add("writes coordination-relevant heap state");
        }
        if ("HEAP_LOOKUP".equals(transfer)) {
            requiredModels.add("symbolic_map_state");
            reasons.add("selects or looks up state by symbolic key");
        }
        if ("MODEL_TRANSFORM".equals(transfer)) {
            reasons.add("requires an observed region summary for the "
                    + "transformation");
            if (edge.containsKey("containerProjectionContractVersion")) {
                requiredModels.add("symbolic_container_projection");
                reasons.add("preserves collection elements through an "
                        + "exact Java collection API contract");
            }
        }
        if ("PROTOCOL_TRANSFER".equals(transfer)) {
            reasons.add("crosses a format or protocol boundary that "
                    + "requires region capture and runtime mapping");
        }
        if ("DYNAMIC_DISPATCH".equals(transfer)) {
            requiredModels.add("dynamic_dispatch_resolution");
            reasons.add("selects a runtime callee or receiver state");
        }
        if ("COMPUTE".equals(transfer)) {
            reasons.add("computes a new tracked value");
        }
        String lowerUnit = unit.toLowerCase(Locale.ROOT);
        if (lowerUnit.contains("time.now")
                || lowerUnit.contains("currenttimemillis")
                || lowerUnit.contains("nanotime")) {
            environmentInputs.add("environment.now");
            reasons.add("reads symbolic time");
        }
    }

    Map<String, Object> toRow(String id) {
        Set<String> liveIns = new LinkedHashSet<>(inputs);
        liveIns.removeAll(defined);
        for (String value : inputs) {
            if (value.contains(".param") || value.contains("@this")
                    || value.contains("#field:")
                    || looksLikeFieldSignature(value)) {
                liveIns.add(value);
            }
        }
        liveIns.addAll(heapInputs);
        liveIns.addAll(environmentInputs);

        String classification = classification();
        if (reasons.isEmpty()) {
            reasons.add("tracked projection is forwarded without a local "
                    + "semantic transform");
        }
        boolean truncated = inputs.size() > MAX_PLAN_VALUES
                || outputs.size() > MAX_PLAN_VALUES
                || siteIds.size() > MAX_PLAN_VALUES;
        return object(
                "id", id,
                "method", method,
                "classification", classification,
                "requiresSymbolicExecution",
                "SYMBOLIC_EXECUTION".equals(classification),
                "reason", joinReasons(reasons),
                "edgeCount", edgeCount,
                "symbolicInputs", sortedLimited(liveIns),
                "heapInputs", sortedLimited(heapInputs),
                "environmentInputs", sortedLimited(environmentInputs),
                "outputs", sortedLimited(outputs),
                "guards", sortedLimited(guards),
                "exceptions", sortedLimited(exceptions),
                "transferKinds", sortedLimited(transferKinds),
                "possibleCallees", sortedLimited(possibleCallees),
                "runtimeObservedCallees", Collections.emptyList(),
                "requiredModels", sortedLimited(requiredModels),
                "siteIds", sortedLimited(siteIds),
                "truncated", truncated,
                "precision", "graph_directed_static_slice");
    }

    private String classification() {
        if (transferKinds.contains("COMPUTE")
                || transferKinds.contains("GUARD")
                || transferKinds.contains("EXCEPTION")
                || transferKinds.contains("HEAP_WRITE")
                || transferKinds.contains("MODEL_TRANSFORM")
                || transferKinds.contains("PROTOCOL_TRANSFER")
                || transferKinds.contains("CONSTRUCT")
                || transferKinds.contains("UNKNOWN")
                || (transferKinds.contains("HEAP_LOOKUP")
                && (!guards.isEmpty() || !exceptions.isEmpty()))) {
            return "SYMBOLIC_EXECUTION";
        }
        if (transferKinds.contains("HEAP_LOOKUP")
                || transferKinds.contains("DYNAMIC_DISPATCH")) {
            return "ROUTE_SUMMARY";
        }
        return "FUNCTION_PASS";
    }

    private static boolean looksLikeFieldSignature(String value) {
        return value != null
                && value.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>");
    }

    private static String joinReasons(Set<String> values) {
        StringBuilder builder = new StringBuilder();
        for (String value : values) {
            if (builder.length() > 0) {
                builder.append("; ");
            }
            builder.append(value);
        }
        return builder.toString();
    }

    private static List<String> sortedLimited(Set<String> values) {
        List<String> sorted = new ArrayList<>(values);
        Collections.sort(sorted);
        if (sorted.size() <= MAX_PLAN_VALUES) {
            return sorted;
        }
        return new ArrayList<>(sorted.subList(0, MAX_PLAN_VALUES));
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static Map<String, Object> object(Object... keyValues) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int i = 0; i + 1 < keyValues.length; i += 2) {
            map.put(String.valueOf(keyValues[i]), keyValues[i + 1]);
        }
        return map;
    }
}
