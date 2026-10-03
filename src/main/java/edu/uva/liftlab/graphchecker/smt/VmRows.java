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
    /** Whether the word a read loaded is the word its version stored. */
    public static final String OBSERVED_EXACT = "observedExact";
    /** Whether a writer the VM's log never named reached the location. */
    public static final String UNNAMED_WRITER = "unnamedWriter";

    /**
     * Whether a read's observed version is the value it read: the VM
     * verified this read (the word it loaded is the word its observed
     * version stored), or the location's writer set is whole.  An
     * incomplete set without that verification leaves the version one
     * candidate among writers nobody stated (SOLR-18406: a list read at its
     * CLEAR version, refilled since by an unmodeled call, was iterated for
     * three names); such a read states no version, a scalar is pinned to
     * what it returned and a container state is refused.  One lost version
     * used to leave every later read of its location unjoined, though each
     * returned exactly what it named (unobs/: 1316 reads after one
     * UNOBSERVED).  An unnamed writer gates alternative writers
     * ({@link #unnamedWriter}); the version bound alone does not.
     */
    public static boolean joinable(JsonObject read) {
        return writerSetComplete(read) || flag(read, OBSERVED_EXACT, false);
    }

    /** The version a read node states it observed, joinable or not, or
     *  -1. */
    public static long recordedVersion(JsonObject read) {
        JsonElement observed = read == null ? null
                : read.get(OBSERVED_VERSION);
        if (observed == null || observed.isJsonNull()) return -1L;
        if (observed.isJsonObject()) {
            JsonElement id = observed.getAsJsonObject().get("fieldVersionId");
            return id == null || !id.isJsonPrimitive() ? -1L : id.getAsLong();
        }
        try {
            return observed.getAsLong();
        } catch (RuntimeException notANumber) {
            return -1L;
        }
    }

    /** Whether a read's location had its whole writer set when it read. */
    private static boolean writerSetComplete(JsonObject read) {
        return flag(read, WRITER_SET_COMPLETE, true);
    }

    /**
     * Whether a writer the VM's log never named had reached a read's
     * location when it read (every incompleteness but the version bound):
     * the read is then paired with the writer it observed and no other.
     */
    public static boolean unnamedWriter(JsonObject read) {
        return flag(read, UNNAMED_WRITER, false);
    }

    private static boolean flag(JsonObject read, String member,
                                boolean absent) {
        JsonElement value = read == null ? null : read.get(member);
        return value == null || !value.isJsonPrimitive() ? absent
                : value.getAsBoolean();
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

    /**
     * Whether a symbol is the VM's placeholder of an object it observed
     * without naming it ({@code P_L'class'_}: {@code PlaceHolderSymbolExp},
     * a container's stored value or a call's argument no shadow names).
     * The VM makes one only for a non-null object -- null is {@code N} --
     * and it names no rid, so it is no particular object.
     */
    public static boolean placeholderObject(String symbol) {
        return symbol != null && symbol.startsWith("P_L'")
                && symbol.endsWith("'_");
    }

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
