package edu.uva.liftlab.graphchecker.causynth;

import java.util.Locale;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** Default semantics for one versioned static data-flow edge row. */
final class StaticDataflowEdgeSchema {
    static final int VERSION = 3;
    private StaticDataflowEdgeSchema() {
    }

    static String transferKind(String kind, String unit, String invoke,
                               String from, String to) {
        String normalizedKind = lower(kind);
        String text = lower(text(unit) + "\n" + text(invoke) + "\n"
                + text(from) + "\n" + text(to));
        if (normalizedKind.contains("seed")) return "SEED";
        if (normalizedKind.contains("guard")) return "GUARD";
        if (normalizedKind.contains("throw")) return "EXCEPTION";
        if (normalizedKind.contains("dispatch")) return "DYNAMIC_DISPATCH";
        // The explicit fault marker is a modeled call-return boundary.
        if (normalizedKind.contains("explicit_symbolic_fault")) {
            return "FUNCTION_RETURN";
        }
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
                && !CausynthStaticFacts.METHOD_SIGNATURE.matcher(from)
                .find()) {
            return "HEAP_READ";
        }
        if (mapOperation(text, "put", "putall", "remove", "clear",
                "replace", "replaceall", "compute", "computeifabsent",
                "computeifpresent", "merge")) {
            return "HEAP_WRITE";
        }
        if (mapOperation(text, "get", "getordefault", "containskey",
                "containsvalue")) {
            return "HEAP_LOOKUP";
        }
        if (containsAny(text, "stringbuilder", "stringbuffer",
                "java.lang.string: java.lang.string concat",
                "java.lang.string: java.lang.string[] split",
                "integer: int parseint", "long: long parselong", "base64",
                " encode", " decode", "serialize", "deserialize",
                "readfields", "writefields")) {
            return "MODEL_TRANSFORM";
        }
        if (normalizedKind.contains("constructor")) return "CONSTRUCT";
        if (normalizedKind.contains("accessor")
                || normalizedKind.contains("receiver_field")) {
            return "IDENTITY_BINDING";
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
        return "UNKNOWN";
    }

    private static boolean mapOperation(String text, String... operations) {
        if (!containsAny(text, "<java.util.map:", "<java.util.hashmap:",
                "<java.util.linkedhashmap:", "<java.util.treemap:",
                "<java.util.concurrent.concurrentmap:",
                "<java.util.concurrent.concurrenthashmap:")) {
            return false;
        }
        for (String operation : operations) {
            String marker = operation + "(";
            if (text.contains(" " + marker)
                    || text.contains("." + marker)) {
                return true;
            }
        }
        return false;
    }

    private static boolean containsAny(String text, String... markers) {
        for (String marker : markers) {
            if (text.contains(marker)) return true;
        }
        return false;
    }

    private static boolean computation(String unit) {
        String text = lower(unit);
        return containsAny(text, " + ", " - ", " * ", " / ", " % ", " & ",
                " | ", " ^ ", " cmp", " new ") || text.startsWith("new ");
    }

    private static String lower(String value) {
        return text(value).toLowerCase(Locale.ROOT);
    }

}
