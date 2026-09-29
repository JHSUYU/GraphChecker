package edu.uva.liftlab.graphchecker.smt;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

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
    /** Whether the VM saw every writer of the location a read observed. */
    public static final String WRITER_SET_COMPLETE = "writerSetComplete";

    /**
     * Whether a read's observed version is the value it read.  Not when the
     * VM says the location's writer set is incomplete: a mutation it does not
     * model reached the location, so the version is one candidate among
     * writers nobody stated (SOLR-18406: a list read at its CLEAR version,
     * refilled since by an unmodeled call, was iterated for three names).
     * Such a read states no version: a scalar is pinned to what it
     * returned, a container state is refused.
     */
    public static boolean joinable(JsonObject read) {
        JsonElement complete = read == null ? null
                : read.get(WRITER_SET_COMPLETE);
        return complete == null || !complete.isJsonPrimitive()
                || complete.getAsBoolean();
    }
    /** What a joined read returned, stamped onto the joined value. */
    public static final String RECORDED_READING = "inSessionRecordedReading";
    /** A container whose base the recording never showed. */
    public static final String CONTAINER_BASE_UNSTATED =
            "CONTAINER_BASE_UNSTATED";

    private static final String TRUNCATED_EXPRESSION_TYPE =
            "TruncatedExpression";
    private static final String TRUNCATION_AUTHORITY =
            "VM_SERIALIZATION_TRUNCATION_V1";

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

    /**
     * Whether the serializer cut this expression short; such a value must
     * not be lowered (it would become a free constant).  Each node once
     * ({@link ExpressionWalk}), so no walk budget: the budget that refused
     * a large expression guarded a walk that paid per path.
     */
    public static boolean truncated(JsonElement expression) {
        for (ExpressionWalk walk = ExpressionWalk.of(expression);
             walk.hasNext(); ) {
            JsonObject term = walk.next();
            if (TRUNCATED_EXPRESSION_TYPE.equals(
                    optionalString(term, "_type"))
                    && TRUNCATION_AUTHORITY.equals(
                    optionalString(term, "expressionAuthority"))) {
                return true;
            }
        }
        return false;
    }
}
