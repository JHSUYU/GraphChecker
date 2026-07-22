package edu.uva.liftlab.graphchecker.causynth;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Pattern;

/** Builds deterministic method-level symbolic plans from static edges. */
final class SymbolicPlanningStage {
    private static final Pattern METHOD_SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>");

    private SymbolicPlanningStage() {
    }

    static void build(CausynthAnalysisResult result) {
        Map<String, SymbolicExecutionPlanBuilder> builders =
                new LinkedHashMap<>();
        for (Map<String, Object> edge : result.edges) {
            String method = stringValue(edge.get("method"));
            if (method.isEmpty()) {
                continue;
            }
            String kind = stringValue(edge.get("kind"));
            String unit = stringValue(edge.get("unit"));
            String invoke = stringValue(edge.get("invoke"));
            String from = stringValue(edge.get("fromCell"));
            String to = stringValue(edge.get("toCell"));
            String transfer = stringValue(edge.get("transferKind"));
            if (transfer.isEmpty()) {
                transfer = transferKind(kind, unit, invoke, from, to);
                edge.put("transferKind", transfer);
            }
            String siteId = stringValue(edge.get("siteId"));
            if (siteId.isEmpty()) {
                siteId = stableSiteId(method,
                        intValue(edge.get("unitIndex"), -1), kind);
                edge.put("siteId", siteId);
            }
            SymbolicExecutionPlanBuilder builder = builders.get(method);
            if (builder == null) {
                builder = new SymbolicExecutionPlanBuilder(method);
                builders.put(method, builder);
            }
            builder.observe(edge, transfer, siteId);
        }

        List<SymbolicExecutionPlanBuilder> ordered =
                new ArrayList<>(builders.values());
        ordered.sort(Comparator.comparing(
                SymbolicExecutionPlanBuilder::method));
        int index = 0;
        for (SymbolicExecutionPlanBuilder builder : ordered) {
            result.symbolicPlan.add(builder.toRow("SP." + index++));
        }
        result.slices.put("symbolicPlanMethodCount",
                result.symbolicPlan.size());
        result.slices.put("symbolicPlanClassifications",
                summarizePlanClassifications(result.symbolicPlan));
    }

    static String transferKind(String kind, String unit, String invoke,
                               String from, String to) {
        String normalizedKind = lower(kind);
        String text = lower(firstNonBlank(unit, "") + "\n"
                + firstNonBlank(invoke, "") + "\n"
                + firstNonBlank(from, "") + "\n"
                + firstNonBlank(to, ""));
        if (normalizedKind.contains("seed")) {
            return "SEED";
        }
        if (normalizedKind.contains("guard")) {
            return "GUARD";
        }
        if (normalizedKind.contains("throw")) {
            return "EXCEPTION";
        }
        if (normalizedKind.contains("rpc")) {
            return "PROTOCOL_TRANSFER";
        }
        if (normalizedKind.contains("dispatch")) {
            return "DYNAMIC_DISPATCH";
        }
        if (normalizedKind.contains("field_write")
                || normalizedKind.contains("field_mutation")
                || normalizedKind.contains("field_effect")) {
            return "HEAP_WRITE";
        }
        if (normalizedKind.contains("field_read")) {
            return "HEAP_READ";
        }
        if (normalizedKind.startsWith("container_")) {
            return "MODEL_TRANSFORM";
        }
        if (normalizedKind.contains("accessor")
                && from != null
                && from.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>")
                && !METHOD_SIGNATURE.matcher(from).find()) {
            return "HEAP_READ";
        }
        if (looksLikeMapMutation(text)) {
            return "HEAP_WRITE";
        }
        if (looksLikeMapLookup(text)) {
            return "HEAP_LOOKUP";
        }
        if (looksLikeModeledTransform(text)) {
            return "MODEL_TRANSFORM";
        }
        if (normalizedKind.contains("constructor")) {
            return "CONSTRUCT";
        }
        if (normalizedKind.contains("accessor")
                || normalizedKind.contains("receiver_field")) {
            return "PROJECTION";
        }
        if (normalizedKind.contains("argument")
                || normalizedKind.endsWith("receiver")
                || normalizedKind.contains("caller_receiver")) {
            return "IDENTITY_BINDING";
        }
        if (normalizedKind.contains("return")) {
            return "FUNCTION_RETURN";
        }
        if (normalizedKind.contains("local_def_use")) {
            if (invoke != null && !invoke.trim().isEmpty()) {
                return "FUNCTION_RETURN";
            }
            return looksLikeComputation(unit) ? "COMPUTE" : "VALUE_PASS";
        }
        if (normalizedKind.contains("projected")) {
            return "PROJECTION";
        }
        return "UNKNOWN";
    }

    private static boolean looksLikeMapMutation(String text) {
        return looksLikeMapOperation(text, "put")
                || looksLikeMapOperation(text, "putall")
                || looksLikeMapOperation(text, "remove")
                || looksLikeMapOperation(text, "clear")
                || looksLikeMapOperation(text, "replace")
                || looksLikeMapOperation(text, "replaceall")
                || looksLikeMapOperation(text, "compute")
                || looksLikeMapOperation(text, "computeifabsent")
                || looksLikeMapOperation(text, "computeifpresent")
                || looksLikeMapOperation(text, "merge");
    }

    private static boolean looksLikeMapLookup(String text) {
        return looksLikeMapOperation(text, "get")
                || looksLikeMapOperation(text, "getordefault")
                || looksLikeMapOperation(text, "containskey")
                || looksLikeMapOperation(text, "containsvalue");
    }

    private static boolean looksLikeMapOperation(String text,
                                                 String operation) {
        if (text == null || text.isEmpty()) {
            return false;
        }
        String marker = operation + "(";
        boolean namedMap = text.contains(" map." + marker)
                || text.contains(" allkeys." + marker)
                || text.contains(" keymap." + marker)
                || text.contains(" cache." + marker);
        boolean mapOwner = text.contains("<java.util.map:")
                || text.contains("<java.util.hashmap:")
                || text.contains("<java.util.linkedhashmap:")
                || text.contains("<java.util.treemap:")
                || text.contains("<java.util.concurrent.concurrentmap:")
                || text.contains(
                "<java.util.concurrent.concurrenthashmap:");
        return namedMap || (mapOwner && (text.contains(" " + marker)
                || text.contains("." + marker)));
    }

    private static boolean looksLikeModeledTransform(String text) {
        return text.contains("stringbuilder")
                || text.contains("stringbuffer")
                || text.contains(
                "java.lang.string: java.lang.string concat")
                || text.contains(
                "java.lang.string: java.lang.string[] split")
                || text.contains("integer: int parseint")
                || text.contains("long: long parselong")
                || text.contains("base64")
                || text.contains(" encode")
                || text.contains(" decode")
                || text.contains("serialize")
                || text.contains("deserialize")
                || text.contains("readfields")
                || text.contains("writefields");
    }

    private static boolean looksLikeComputation(String unit) {
        String text = lower(firstNonBlank(unit, ""));
        return text.contains(" + ")
                || text.contains(" - ")
                || text.contains(" * ")
                || text.contains(" / ")
                || text.contains(" % ")
                || text.contains(" & ")
                || text.contains(" | ")
                || text.contains(" ^ ")
                || text.contains(" cmp")
                || text.contains(" new ")
                || text.startsWith("new ");
    }

    private static String stableSiteId(String method, int unitIndex,
                                       String kind) {
        if (unitIndex >= 0) {
            return method + "#u" + unitIndex;
        }
        return method + "#synthetic:" + firstNonBlank(kind, "edge");
    }

    private static Map<String, Object> summarizePlanClassifications(
            List<Map<String, Object>> plan) {
        Map<String, Object> counts = new LinkedHashMap<>();
        for (Map<String, Object> row : plan) {
            String classification = stringValue(row.get("classification"));
            Object previous = counts.get(classification);
            counts.put(classification, previous instanceof Number
                    ? ((Number) previous).intValue() + 1 : 1);
        }
        return counts;
    }

    private static String stringValue(Object value) {
        return value == null || "null".equals(String.valueOf(value))
                ? "" : String.valueOf(value);
    }

    private static int intValue(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(String.valueOf(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String lower(String value) {
        return value == null ? "" : value.toLowerCase(Locale.ROOT);
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return null;
    }
}
