package edu.uva.liftlab.graphchecker.causynth;

import java.util.Map;
import java.util.Locale;
import java.util.regex.Pattern;

/** Default semantics for one versioned static data-flow edge row. */
final class StaticDataflowEdgeSchema {
    static final int VERSION = 2;
    static final String ASSERTABLE = "ASSERTABLE";
    static final String MAPPING_ONLY = "MAPPING_ONLY";
    static final String RUNTIME_VALIDATION_REQUIRED =
            "RUNTIME_VALIDATION_REQUIRED";
    private static final Pattern METHOD_SIGNATURE = Pattern.compile(
            "<([^:]+):\\s+(.+)\\s+([^\\s(]+)\\((.*)\\)>");

    private StaticDataflowEdgeSchema() {
    }

    static boolean mappingOnly(Map<String, Object> edge) {
        return MAPPING_ONLY.equals(semanticMode(edge));
    }

    static String mappingAuthority(Map<String, Object> edge) {
        return string(edge, "mappingAuthority", "");
    }

    static boolean automaticSemantics(Map<String, Object> edge) {
        return supported(edge) && ASSERTABLE.equals(semanticMode(edge));
    }

    static String semanticMode(Map<String, Object> edge) {
        return string(edge, "semanticMode", "");
    }

    static String transferKind(String kind, String unit, String invoke,
                               String from, String to) {
        String normalizedKind = lower(kind);
        String text = lower(text(unit) + "\n" + text(invoke) + "\n"
                + text(from) + "\n" + text(to));
        if (normalizedKind.contains("seed")) return "SEED";
        if (normalizedKind.contains("guard")) return "GUARD";
        if (normalizedKind.contains("throw")) return "EXCEPTION";
        if (normalizedKind.contains("rpc")) return "PROTOCOL_TRANSFER";
        if (normalizedKind.contains("dispatch")) return "DYNAMIC_DISPATCH";
        if (normalizedKind.contains("field_write")
                || normalizedKind.contains("field_mutation")
                || normalizedKind.contains("field_effect")) {
            return "HEAP_WRITE";
        }
        if (normalizedKind.contains("field_read")) return "HEAP_READ";
        if (normalizedKind.startsWith("container_")) return "MODEL_TRANSFORM";
        if (normalizedKind.contains("accessor")
                && from != null
                && from.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>")
                && !METHOD_SIGNATURE.matcher(from).find()) {
            return "HEAP_READ";
        }
        if (mapOperation(text, "put")
                || mapOperation(text, "putall")
                || mapOperation(text, "remove")
                || mapOperation(text, "clear")
                || mapOperation(text, "replace")
                || mapOperation(text, "replaceall")
                || mapOperation(text, "compute")
                || mapOperation(text, "computeifabsent")
                || mapOperation(text, "computeifpresent")
                || mapOperation(text, "merge")) {
            return "HEAP_WRITE";
        }
        if (mapOperation(text, "get")
                || mapOperation(text, "getordefault")
                || mapOperation(text, "containskey")
                || mapOperation(text, "containsvalue")) {
            return "HEAP_LOOKUP";
        }
        if (text.contains("stringbuilder")
                || text.contains("stringbuffer")
                || text.contains("java.lang.string: java.lang.string concat")
                || text.contains("java.lang.string: java.lang.string[] split")
                || text.contains("integer: int parseint")
                || text.contains("long: long parselong")
                || text.contains("base64")
                || text.contains(" encode")
                || text.contains(" decode")
                || text.contains("serialize")
                || text.contains("deserialize")
                || text.contains("readfields")
                || text.contains("writefields")) {
            return "MODEL_TRANSFORM";
        }
        if (normalizedKind.contains("constructor")) return "CONSTRUCT";
        if (normalizedKind.contains("accessor")
                || normalizedKind.contains("receiver_field")) {
            return "PROJECTION";
        }
        if (normalizedKind.contains("argument")
                || normalizedKind.endsWith("receiver")
                || normalizedKind.contains("caller_receiver")) {
            return "IDENTITY_BINDING";
        }
        if (normalizedKind.contains("return")) return "FUNCTION_RETURN";
        if (normalizedKind.contains("local_def_use")) {
            if (invoke != null && !invoke.trim().isEmpty()) {
                return "FUNCTION_RETURN";
            }
            return computation(unit) ? "COMPUTE" : "VALUE_PASS";
        }
        if (normalizedKind.contains("projected")) return "PROJECTION";
        return "UNKNOWN";
    }

    private static boolean mapOperation(String text, String operation) {
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
                || text.contains("<java.util.concurrent.concurrenthashmap:");
        return namedMap || mapOwner && (text.contains(" " + marker)
                || text.contains("." + marker));
    }

    private static boolean computation(String unit) {
        String text = lower(unit);
        return text.contains(" + ") || text.contains(" - ")
                || text.contains(" * ") || text.contains(" / ")
                || text.contains(" % ") || text.contains(" & ")
                || text.contains(" | ") || text.contains(" ^ ")
                || text.contains(" cmp") || text.contains(" new ")
                || text.startsWith("new ");
    }

    private static String text(String value) {
        return value == null ? "" : value;
    }

    private static String lower(String value) {
        return text(value).toLowerCase(Locale.ROOT);
    }

    static boolean supported(Map<String, Object> edge) {
        if (edge == null) {
            return false;
        }
        Object value = edge.get("schemaVersion");
        if (value instanceof Number) {
            return ((Number) value).intValue() == VERSION;
        }
        return value != null && String.valueOf(VERSION).equals(
                String.valueOf(value));
    }

    private static String string(Map<String, Object> edge, String field,
                                 String fallback) {
        if (edge == null || !edge.containsKey(field)
                || edge.get(field) == null) {
            return fallback;
        }
        return String.valueOf(edge.get(field));
    }
}
