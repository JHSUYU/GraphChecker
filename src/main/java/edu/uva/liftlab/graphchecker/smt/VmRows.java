package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * The spellings the VM uses inside a recorded expression (not the row
 * contract): read versions, recorded readings, object references and the
 * truncation marker.  Kept here so {@code compose} depends only on
 * {@code contract} and the VM's format.
 */
public final class VmRows {
    private VmRows() {
    }

    /** A read of shared state, as the VM serializes it. */
    public static final String GUARDED_READ_TYPE = "ReadFromExpression";
    /** The version a read states it observed. */
    public static final String OBSERVED_VERSION = "observedVersion";
    /** What a joined read returned, stamped onto the joined value. */
    public static final String RECORDED_READING = "inSessionRecordedReading";
    /** A container whose base the recording never showed. */
    public static final String CONTAINER_BASE_UNSTATED =
            "CONTAINER_BASE_UNSTATED";

    private static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    private static final String TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";
    private static final int MAX_DEPTH = 512;

    /** The rid one {@code M_L'class'_rid} reference symbol names, or -1. */
    public static long referencedObjectRid(String symbol) {
        if (symbol == null) return -1L;
        int quoted = symbol.lastIndexOf("'_");
        if (!symbol.startsWith("M_L'") || quoted < 0) return -1L;
        String digits = symbol.substring(quoted + 2);
        if (digits.isEmpty()) return -1L;
        for (int index = 0; index < digits.length(); index++) {
            if (!Character.isDigit(digits.charAt(index))) return -1L;
        }
        try {
            return Long.parseLong(digits);
        } catch (NumberFormatException notAnObject) {
            return -1L;
        }
    }

    /** One VM location node as {@code kind/owner#slot}, or "". */
    public static String sessionLocation(JsonObject location) {
        if (location == null || location.size() == 0) return "";
        String kind = optionalString(location, "locationKind");
        if (kind.isEmpty() || !location.has("slot")) return "";
        long owner = optionalLongInteger(location, "ownerSymRid", 0L);
        if (owner == 0L) return "";
        return kind + "/" + owner + "#"
                + optionalLongInteger(location, "slot", 0L);
    }

    /**
     * Whether the serializer cut this expression short; such a value must
     * not be lowered (it would become a free constant).
     */
    public static boolean truncated(JsonElement expression) {
        if (expression == null) return false;
        Deque<JsonElement> pending = new ArrayDeque<JsonElement>();
        Set<JsonElement> visited = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        pending.push(expression);
        int steps = 0;
        while (!pending.isEmpty()) {
            // THE BUDGET IS A REFUSAL, NOT AN ANSWER: "false" would claim
            // the expression is whole, which is fail-open.
            if (steps++ >= MAX_DEPTH * MAX_DEPTH) {
                throw new IllegalStateException("this expression could not"
                        + " be walked for the serializer's truncation"
                        + " marker within " + (MAX_DEPTH * MAX_DEPTH)
                        + " nodes, so whether the recording published it"
                        + " whole is unstated: a composition may not lower"
                        + " a value it cannot tell is complete");
            }
            JsonElement current = pending.pop();
            if (current == null || current.isJsonNull()) continue;
            if (!current.isJsonPrimitive() && !visited.add(current)) continue;
            if (current.isJsonArray()) {
                for (JsonElement child : current.getAsJsonArray()) {
                    if (child != null) pending.push(child);
                }
                continue;
            }
            if (!current.isJsonObject()) continue;
            JsonObject term = current.getAsJsonObject();
            if (TRUNCATED_EXPRESSION_TYPE.equals(
                    optionalString(term, "_type"))
                    && TRUNCATION_AUTHORITY.equals(
                    optionalString(term, "expressionAuthority"))) {
                return true;
            }
            for (String member : term.keySet()) {
                JsonElement child = term.get(member);
                if (child != null && !child.isJsonPrimitive()) {
                    pending.push(child);
                }
            }
        }
        return false;
    }
}
