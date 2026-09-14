package edu.uva.liftlab.graphchecker.d3.compose;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.d3.compose.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.d3.compose.JsonFields.optionalString;

/**
 * The spellings the VM uses inside a recorded expression.
 *
 * <p>These are members of the recording's own JSON, not of the Design 3
 * row contract: a read node's {@code observedVersion}, the tag a resolved
 * read carries its recorded value under, the {@code M_L'class'_rid} shape
 * of an object reference, and the truncation marker the serializer writes
 * when an expression was too deep to publish.  They live here, beside the
 * lowering that reads them, so that the whole of {@code d3.compose} depends
 * on nothing but {@code d3.contract} and the VM's own format.</p>
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

    /**
     * The object id one reference symbol names, or -1.
     *
     * <p>{@code M_L'org/apache/hadoop/.../BlockKey'_42} is the VM's spelling
     * for "the object the runtime gave rid 42".  Which object an execution
     * ran on says nothing about the failure, but that it was an object, and
     * a different one from its neighbours, are recorded facts the lowering
     * states.</p>
     */
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

    /** One decimal integer as SMT-LIB spells it, or null. */
    public static String integerLiteral(String value) {
        String raw = value == null ? "" : value.trim();
        if (raw.isEmpty() || raw.length() > 1024) return null;
        try {
            BigInteger parsed = new BigInteger(raw);
            return parsed.signum() < 0 ? "(- " + parsed.negate() + ")"
                    : parsed.toString();
        } catch (NumberFormatException malformed) {
            return null;
        }
    }

    /**
     * Whether the serializer cut this expression short.
     *
     * <p>A truncated expression is not a value the composition may lower: it
     * is the recording saying it did not publish one.  Lowering it anyway
     * would put a free constant where a chain was.</p>
     */
    public static boolean truncated(JsonElement expression) {
        if (expression == null) return false;
        Deque<JsonElement> pending = new ArrayDeque<JsonElement>();
        Set<JsonElement> visited = Collections.newSetFromMap(
                new IdentityHashMap<JsonElement, Boolean>());
        pending.push(expression);
        int steps = 0;
        while (!pending.isEmpty() && steps++ < MAX_DEPTH * MAX_DEPTH) {
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
