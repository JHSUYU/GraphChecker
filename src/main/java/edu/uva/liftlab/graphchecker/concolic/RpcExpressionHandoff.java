package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/** Named vocabulary for the VM symbolic expression handoff bridge. */
public final class RpcExpressionHandoff {

    public static final int SCHEMA_VERSION = 1;

    /** Successful broker call. */
    public static final int OK = 0;

    // Declared VM broker statuses (expressionBroker.hpp).  Their numeric
    // values are the VM's, not ours; they are mirrored here so a Java caller
    // can name a failure without linking against the custom JDK.
    public static final int NO_ACTIVE_REGION = -1;
    public static final int MISSING_METADATA = -2;
    public static final int FIELD_NOT_FOUND = -3;
    public static final int NOT_SYMBOLIC = -4;
    public static final int FOREIGN_HANDLE = -5;
    public static final int UNKNOWN_HANDLE = -6;
    public static final int SORT_MISMATCH = -9;
    public static final int UNSUPPORTED_TARGET = -12;
    // -8, -10, -11 and -13..-15 were the identity/shape/fingerprint refusals
    // of the deleted duplicate validation.  The broker no longer answers
    // them; the numbers stay unassigned because the codes are a shared ABI.

    /** Bridge-local statuses. */
    public static final int INVOCATION_FAILED = -1001;
    public static final int MALFORMED_RESULT = -1002;

    /** Gap family recorded for every failed handoff call. */
    public static final String GAP_KIND = "RPC_HANDOFF_GAP";
    /**
     * The communication port a gap row is about.
     *
     * <p>Carried as a field rather than left inside {@code detail}: the
     * campaign fold decides this row's class by joining the port against
     * the composed formula's handoff phases, and a join that has to parse a
     * sentence is a join that breaks when the sentence is reworded.</p>
     */
    public static final String PORT_FIELD = "portId";
    /** Authority stamped on a gap row. */
    public static final String GAP_AUTHORITY =
            "VM_RPC_EXPRESSION_HANDOFF_GAP_V1";
    /** Stage names used by broker calls and their failure gaps. */
    public static final String STAGE_EXPORT = "EXPORT";
    public static final String STAGE_ATTACH = "ATTACH";

    /**
     * A value the sender put in a message that no decode looked up.
     *
     * <p>Whatever that value feeds on the receiving side is a leaf with no
     * producer, so the chain the message was carrying stops there.</p>
     */
    public static final String LEAVES_UNATTACHED = "WIRE_LEAVES_UNATTACHED";
    /**
     * One capture site, two live occurrences that declare its port.
     *
     * <p>The value crossed the wire once, so it is attached once and the
     * row names one consumer.  Any other activation live at that capture
     * whose own plan declares the same port gets this instead of silence:
     * its planned attach did happen, on the occurrence named here.</p>
     */
    public static final String LEAF_ATTACHED_ELSEWHERE =
            "WIRE_LEAF_ATTACHED_ELSEWHERE";
    /**
     * A selected occurrence sent a message with no request scope to name.
     *
     * <p>The envelope is empty, so nothing of this send carries symbolic
     * state -- and a workload that guards its own fault marker on the
     * envelope being active does not run the marker at all.</p>
     */
    public static final String OUTBOUND_SCOPE_REFUSED =
            "WIRE_OUTBOUND_SCOPE_REFUSED";

    private static final String REASON_PREFIX = "RPC_HANDOFF_";
    /** Reason used for any negative status this build does not declare. */
    public static final String UNDECLARED_REASON =
            REASON_PREFIX + "UNDECLARED_STATUS";

    private RpcExpressionHandoff() {
    }

    /** Names one handoff status. */
    public static String reason(int status) {
        switch (status) {
            case OK:
                return "";
            case NO_ACTIVE_REGION:
                return REASON_PREFIX + "NO_ACTIVE_REGION";
            case MISSING_METADATA:
                return REASON_PREFIX + "MISSING_METADATA";
            case FIELD_NOT_FOUND:
                return REASON_PREFIX + "FIELD_NOT_FOUND";
            case NOT_SYMBOLIC:
                return REASON_PREFIX + "NOT_SYMBOLIC";
            case FOREIGN_HANDLE:
                return REASON_PREFIX + "FOREIGN_HANDLE";
            case UNKNOWN_HANDLE:
                return REASON_PREFIX + "UNKNOWN_HANDLE";
            case SORT_MISMATCH:
                return REASON_PREFIX + "SORT_MISMATCH";
            case UNSUPPORTED_TARGET:
                return REASON_PREFIX + "UNSUPPORTED_TARGET";
            case INVOCATION_FAILED:
                return REASON_PREFIX + "INVOCATION_FAILED";
            case MALFORMED_RESULT:
                return REASON_PREFIX + "MALFORMED_RESULT";
            default:
                return UNDECLARED_REASON;
        }
    }

    /** Builds one named coverage gap. */
    public static JsonObject gap(String stage, int status, long handle,
                                 String detail) {
        if (status == OK) {
            throw new IllegalArgumentException(
                    "a successful handoff is not a gap");
        }
        JsonObject gap = new JsonObject();
        gap.addProperty("kind", GAP_KIND);
        gap.addProperty("schemaVersion", SCHEMA_VERSION);
        gap.addProperty("reason", reason(status));
        gap.addProperty("authority", GAP_AUTHORITY);
        gap.addProperty("stage", nonNull(stage));
        gap.addProperty("statusCode", status);
        gap.addProperty("handle", handle);
        gap.addProperty("detail", nonNull(detail));
        return gap;
    }

    /** Builds one named coverage gap about one communication port. */
    public static JsonObject portGap(String stage, int status, long handle,
                                     String portId, String detail) {
        JsonObject gap = gap(stage, status, handle, detail);
        gap.addProperty(PORT_FIELD, nonNull(portId));
        return gap;
    }

    /** The port a gap row is about, or {@code ""}. */
    public static String portOf(JsonObject row) {
        return row == null || !row.has(PORT_FIELD)
                || !row.get(PORT_FIELD).isJsonPrimitive()
                ? "" : row.get(PORT_FIELD).getAsString();
    }

    /** Builds one named coverage gap under an explicit code. */
    public static JsonObject gap(String code, String stage, int status,
                                 long handle, String detail) {
        JsonObject gap = gap(stage, status, handle, detail);
        gap.addProperty("code", nonNull(code));
        return gap;
    }

    /** One named coverage gap about one port, under an explicit code. */
    public static JsonObject portGap(String code, String stage, int status,
                                     long handle, String portId,
                                     String detail) {
        JsonObject gap = portGap(stage, status, handle, portId, detail);
        gap.addProperty("code", nonNull(code));
        return gap;
    }

    /** Whether {@code row} is a handoff gap this vocabulary produced. */
    public static boolean isGap(JsonObject row) {
        return JsonFields.isGapRow(row, GAP_KIND, GAP_AUTHORITY, OK);
    }
}
