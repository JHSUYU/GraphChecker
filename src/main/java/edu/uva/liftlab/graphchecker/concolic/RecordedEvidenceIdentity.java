package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/** Who recorded one piece of VM evidence, in which run, and when. */
public final class RecordedEvidenceIdentity {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "RECORDED_EVIDENCE_IDENTITY";
    /** Member every stamped evidence row carries. */
    public static final String FIELD = "evidenceIdentity";

    /**
     * System property a launcher may set to name one workload execution.
     * Until one does, {@code runId} is empty and says so.
     */
    public static final String RUN_ID_PROPERTY = "causynth.run.id";

    private final String runId;
    private final String sessionId;
    private final String taskId;
    private final String occurrenceId;
    private final String sourceKey;
    private final long snapshotOrdinal;

    private RecordedEvidenceIdentity(String runId, String sessionId,
                                     String taskId, String occurrenceId,
                                     String sourceKey, long snapshotOrdinal) {
        this.runId = nonNull(runId);
        this.sessionId = nonNull(sessionId);
        this.taskId = nonNull(taskId);
        this.occurrenceId = nonNull(occurrenceId);
        this.sourceKey = nonNull(sourceKey);
        this.snapshotOrdinal = snapshotOrdinal;
    }

    public static RecordedEvidenceIdentity of(String runId, String sessionId,
                                              String taskId,
                                              String occurrenceId,
                                              String sourceKey,
                                              long snapshotOrdinal) {
        return new RecordedEvidenceIdentity(runId, sessionId, taskId,
                occurrenceId, sourceKey, snapshotOrdinal);
    }

    /** The run identity a launcher declared, or "" when none did. */
    public static String declaredRunId() {
        return nonNull(System.getProperty(RUN_ID_PROPERTY)).trim();
    }

    /** The cross-run address of one activation. */
    public static String siteKey(String occurrenceId) {
        return nonNull(occurrenceId).trim();
    }

    public JsonObject toJson() {
        JsonObject identity = new JsonObject();
        identity.addProperty("schemaVersion", SCHEMA_VERSION);
        identity.addProperty("kind", KIND);
        identity.addProperty("runId", runId);
        identity.addProperty("sessionId", sessionId);
        identity.addProperty("taskId", taskId);
        identity.addProperty("occurrenceId", occurrenceId);
        identity.addProperty("sourceKey", sourceKey);
        identity.addProperty("snapshotOrdinal", snapshotOrdinal);
        return identity;
    }

    /** Stamps {@code row} in place, and returns it. */
    public JsonObject stamp(JsonObject row) {
        if (row != null) row.add(FIELD, toJson());
        return row;
    }

    /** Names what is missing from one stamp, or "" when it is complete. */
    public static String fault(JsonObject identity) {
        if (identity == null || identity.size() == 0) {
            return "record carries no evidence identity";
        }
        if (!KIND.equals(string(identity, "kind"))
                || integer(identity, "schemaVersion", -1) != SCHEMA_VERSION) {
            return "evidence identity is not an authoritative stamp";
        }
        if (!identity.has("runId")) {
            return "evidence identity omits its run";
        }
        for (String member : new String[]{"sessionId", "taskId",
                "occurrenceId", "sourceKey"}) {
            if (string(identity, member).isEmpty()) {
                return "evidence identity omits " + member;
            }
        }
        if (longInteger(identity, "snapshotOrdinal", 0L) <= 0L) {
            return "evidence identity carries no snapshot ordinal";
        }
        return "";
    }

    /** Whether {@code row} carries a complete identity stamp. */
    public static boolean stamped(JsonObject row) {
        return row != null && fault(object(row, FIELD)).isEmpty();
    }

    /** The snapshot ordinal of one stamped row; 0 when it carries none. */
    public static long snapshotOrdinalOf(JsonObject row) {
        return row == null ? 0L
                : longInteger(object(row, FIELD), "snapshotOrdinal", 0L);
    }
}
