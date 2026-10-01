package edu.uva.liftlab.graphchecker.causynth;

import java.util.Locale;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.text;

/** Default semantics for one versioned static data-flow edge row. */
public final class StaticDataflowEdgeSchema {
    static final int VERSION = 3;

    /**
     * The one kind for every edge that carries a value forward; only kinds a
     * reader tests by name (GUARD, EXCEPTION, HEAP_WRITE, HEAP_READ,
     * VALUE_PASS, DYNAMIC_DISPATCH) get their own.
     */
    public static final String VALUE_TRANSFER = "VALUE_TRANSFER";

    private StaticDataflowEdgeSchema() {
    }

    static String transferKind(String kind, String unit, String invoke,
                               String from, String to) {
        String normalizedKind = lower(kind);
        String text = lower(text(unit) + "\n" + text(invoke) + "\n"
                + text(from) + "\n" + text(to));
        if (normalizedKind.contains("guard")) return "GUARD";
        if (normalizedKind.contains("throw")
                || normalizedKind.startsWith("exception_")) {
            return "EXCEPTION";
        }
        if (normalizedKind.contains("dispatch")) return "DYNAMIC_DISPATCH";
        if (normalizedKind.contains("field_write")
                || normalizedKind.contains("field_mutation")
                || normalizedKind.contains("field_effect")) {
            return "HEAP_WRITE";
        }
        if (normalizedKind.contains("field_read")) return "HEAP_READ";
        if (normalizedKind.startsWith("container_")) return VALUE_TRANSFER;
        if (normalizedKind.contains("accessor")
                && from != null
                && from.matches("<[^:]+:\\s+.+\\s+[^\\s()]+>")
                && !CausynthStaticFacts.METHOD_SIGNATURE.matcher(from)
                .find()) {
            return "HEAP_READ";
        }
        // A map mutation is a heap write; a map read or re-encoding is not.
        if (mapOperation(text, "put", "putall", "remove", "clear", "replace",
                "replaceall", "compute", "computeifabsent",
                "computeifpresent", "merge")) {
            return "HEAP_WRITE";
        }
        if (mapOperation(text, "get", "getordefault", "containskey",
                "containsvalue")
                || containsAny(text, "stringbuilder", "stringbuffer",
                "java.lang.string: java.lang.string concat",
                "java.lang.string: java.lang.string[] split",
                "integer: int parseint", "long: long parselong", "base64",
                " encode", " decode", "serialize", "deserialize",
                "readfields", "writefields")
                || normalizedKind.contains("explicit_symbolic_fault")
                || normalizedKind.contains("constructor")
                || normalizedKind.contains("accessor")
                || normalizedKind.contains("receiver_field")
                || normalizedKind.contains("argument")
                || normalizedKind.endsWith("receiver")
                || normalizedKind.contains("caller_receiver")
                || normalizedKind.contains("return")) {
            return VALUE_TRANSFER;
        }
        if (normalizedKind.contains("local_def_use")) {
            // VALUE_PASS is an exact copy only (read by exactLocalPass).
            return invoke != null && !invoke.trim().isEmpty()
                    || computation(unit) ? VALUE_TRANSFER : "VALUE_PASS";
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
