package edu.uva.liftlab.graphchecker.causynth;

import java.util.Map;

/** Default semantics for one versioned static data-flow edge row. */
final class StaticDataflowEdgeSchema {
    static final int VERSION = 1;
    static final String DEFAULT_DIRECTION = "backward_provenance";

    private StaticDataflowEdgeSchema() {
    }

    static boolean mappingOnly(Map<String, Object> edge) {
        if (edge != null && edge.containsKey("mappingOnly")) {
            return !Boolean.FALSE.equals(edge.get("mappingOnly"));
        }
        return !hasDefaults(edge);
    }

    static String mappingAuthority(Map<String, Object> edge) {
        return string(edge, "mappingAuthority", "");
    }

    static boolean semanticAssertionsAllowed(Map<String, Object> edge) {
        return flag(edge, "semanticAssertionsAllowed");
    }

    static boolean eligibleForAutomaticDerivation(
            Map<String, Object> edge) {
        return flag(edge, "eligibleForAutomaticDerivation");
    }

    static boolean eligibleForAutomaticSmt(Map<String, Object> edge) {
        return flag(edge, "eligibleForAutomaticSmt");
    }

    static String direction(Map<String, Object> edge) {
        return string(edge, "direction",
                hasDefaults(edge) ? DEFAULT_DIRECTION : "");
    }

    static boolean automaticSemantics(Map<String, Object> edge) {
        return supported(edge)
                && !mappingOnly(edge)
                && semanticAssertionsAllowed(edge)
                && eligibleForAutomaticDerivation(edge)
                && eligibleForAutomaticSmt(edge)
                && DEFAULT_DIRECTION.equals(direction(edge));
    }

    private static boolean flag(Map<String, Object> edge, String field) {
        if (edge != null && edge.containsKey(field)) {
            return Boolean.TRUE.equals(edge.get(field));
        }
        return hasDefaults(edge);
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

    private static boolean hasDefaults(Map<String, Object> edge) {
        return supported(edge);
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
