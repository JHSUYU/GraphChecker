package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * Evidence gate shared by graph discovery and SMT preparation.
 *
 * <p>A port map may be useful for locating another region without proving a
 * value relation.  Automatic composition is deliberately stricter: equality
 * requires an observed complete runtime value fingerprint, and shared state
 * requires a confirmed concrete write/read pair.  Static protocol contracts,
 * endpoint order, and domain-specific mapping names never satisfy this gate.</p>
 */
public final class AutomaticRegionEdge {
    private AutomaticRegionEdge() {
    }

    public static boolean composable(JsonObject edge) {
        if (edge == null || !bool(edge, "composable", false)
                || explicitlyFalse(edge,
                "eligibleForAutomaticDerivation")
                || explicitlyFalse(edge, "eligibleForAutomaticSmt")) {
            return false;
        }
        String relation = firstNonBlank(string(edge, "validatedRelation"),
                string(edge, "relation"));
        if ("READ_FROM".equals(relation)) {
            return "CONFIRMED_READ_FROM".equals(string(edge, "status"))
                    && integer(edge, "confirmedReadFromPairCount", 0) > 0;
        }
        if ("EQUALITY".equals(relation)) {
            String authority = string(edge, "valueEqualityAuthority");
            return bool(edge, "valueEqualityObserved", false)
                    && integer(edge, "confirmedValueEqualityPairCount", 0) > 0
                    && authority.startsWith("RUNTIME_");
        }
        return false;
    }

    public static boolean discoverable(JsonObject edge) {
        if (composable(edge)) return true;
        if (edge == null) return false;
        if (bool(edge, "eligibleForRecursiveDiscovery", false)) return true;
        int endpoints = integer(edge, "endpointPairCount", 0);
        int ordered = integer(edge, "orderedPairCount", 0);
        return endpoints > 0
                && (!bool(edge, "requiresOrder", false) || ordered > 0)
                && !string(edge, "fromRegion").isEmpty()
                && !string(edge, "toRegion").isEmpty();
    }

    /**
     * A static protocol-port mapping may justify spending a bounded execution
     * to look for a transition, but it never proves the mapped values equal.
     * This predicate is intentionally disjoint from {@link #composable} and
     * does not relax {@link #discoverable}; callers must keep its products in
     * a discovery-only quarantine until a fresh runtime edge passes
     * {@code composable} in that same execution.
     */
    public static boolean transitionDiscoveryCandidate(JsonObject edge) {
        if (edge == null || composable(edge)
                || string(edge, "fromRegion").isEmpty()
                || string(edge, "fromPort").isEmpty()
                || string(edge, "toRegion").isEmpty()
                || string(edge, "toPort").isEmpty()
                || bool(edge, "eligibleForAutomaticDerivation", false)
                || bool(edge, "eligibleForAutomaticSmt", false)) {
            return false;
        }
        String candidate = firstNonBlank(string(edge,
                "candidateRelation"), string(edge, "relation"));
        String authority = firstNonBlank(string(edge,
                "transitionDiscoveryAuthority"), string(edge,
                "mappingAuthority"), string(edge,
                "sourceMappingAuthority"));
        boolean explicit = bool(edge, "eligibleForTransitionDiscovery",
                false) && authority.startsWith("STATIC_");
        boolean mappedEquality = "EQUALITY".equals(candidate)
                && bool(edge, "mappingOnly", false)
                && bool(edge, "payloadEqualityCheckRequired", false)
                && authority.startsWith("STATIC_");
        return explicit || mappedEquality;
    }

    public static String exclusionReason(JsonObject edge) {
        if (composable(edge)) return "";
        String explicit = string(edge, "exclusionReason");
        if (!explicit.isEmpty()) return explicit;
        String relation = firstNonBlank(string(edge, "validatedRelation"),
                string(edge, "candidateRelation"),
                string(edge, "relation"));
        if ("EQUALITY".equals(relation)) {
            return "RUNTIME_VALUE_EQUALITY_NOT_PROVEN";
        }
        if ("READ_FROM".equals(relation)
                || "READ_FROM_CANDIDATE".equals(relation)) {
            return "RUNTIME_WRITE_READ_PAIR_NOT_PROVEN";
        }
        return "NO_AUTOMATICALLY_VALIDATED_RELATION";
    }

    private static boolean explicitlyFalse(JsonObject object, String name) {
        JsonElement value = object.get(name);
        try {
            return value != null && !value.isJsonNull()
                    && !value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return true;
        }
    }

    private static String string(JsonObject object, String name) {
        if (object == null) return "";
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        } catch (RuntimeException ignored) {
            return "";
        }
    }

    private static boolean bool(JsonObject object, String name,
                                boolean fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static int integer(JsonObject object, String name, int fallback) {
        if (object == null) return fallback;
        JsonElement value = object.get(name);
        try {
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsInt();
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static String firstNonBlank(String... values) {
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) return value;
        }
        return "";
    }
}
