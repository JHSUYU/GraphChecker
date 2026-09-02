package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

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
    /** Authority stamped on a gap row. */
    public static final String GAP_AUTHORITY =
            "VM_RPC_EXPRESSION_HANDOFF_GAP_V1";
    /** Stage names used by broker calls and their failure gaps. */
    public static final String STAGE_EXPORT = "EXPORT";
    public static final String STAGE_ATTACH = "ATTACH";

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

    /** Whether {@code row} is a handoff gap this vocabulary produced. */
    public static boolean isGap(JsonObject row) {
        return row != null
                && GAP_KIND.equals(string(row, "kind"))
                && GAP_AUTHORITY.equals(string(row, "authority"))
                && !string(row, "reason").isEmpty()
                && integer(row, "statusCode", OK) != OK;
    }
}
