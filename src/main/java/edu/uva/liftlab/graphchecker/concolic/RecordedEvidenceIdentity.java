package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonObject;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Who recorded one piece of VM evidence, in which run, and when.
 *
 * <p>An admitted record used to say what it observed and nothing about the
 * observer. That is enough while a workload runs one activation at a time and
 * exactly once, and wrong as soon as it does not: two activations of one region
 * produce two stores, two runs produce two sessions, and a record with no
 * observer cannot be told apart from either. Every consumer then has to guess -
 * usually by taking the biggest or the last row - which is the recency
 * inference this stamp exists to remove.</p>
 *
 * <p>The stamp is deliberately made of identities that outlive the record:</p>
 *
 * <ul>
 *   <li>{@code runId} - one workload execution. No launcher mints one yet, so
 *   it is honestly empty until one does; the member is always present, because
 *   "no run identity" is a fact about the run and not a missing field.</li>
 *   <li>{@code sessionId} - one same-JVM symbolic lifetime.</li>
 *   <li>{@code taskId}, {@code occurrenceId}, {@code sourceKey} - the exact
 *   activation that read the evidence back.</li>
 *   <li>{@code snapshotOrdinal} - a monotonic counter over read-out batches.
 *   Recency is read from it and never from how many rows a store returned: a
 *   bounded store evicts, so a later snapshot may hold fewer entries than an
 *   earlier one.</li>
 * </ul>
 *
 * <p>{@link #siteKey} is the cross-run join address these identities compose
 * to. Where either half is missing the key is empty, and an empty key decides
 * nothing - a record whose observer cannot be named is evidence about the
 * session, never about a pairing.</p>
 */
public final class RecordedEvidenceIdentity {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "RECORDED_EVIDENCE_IDENTITY";
    /** Member every stamped evidence row carries. */
    public static final String FIELD = "evidenceIdentity";

    /**
     * System property a launcher may set to name one workload execution.
     * Until one does, {@link #runId()} is empty and says so.
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
        this.runId = text(runId);
        this.sessionId = text(sessionId);
        this.taskId = text(taskId);
        this.occurrenceId = text(occurrenceId);
        this.sourceKey = text(sourceKey);
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
        return text(System.getProperty(RUN_ID_PROPERTY)).trim();
    }

    public String runId() {
        return runId;
    }

    public String sessionId() {
        return sessionId;
    }

    public String taskId() {
        return taskId;
    }

    public String occurrenceId() {
        return occurrenceId;
    }

    public String sourceKey() {
        return sourceKey;
    }

    public long snapshotOrdinal() {
        return snapshotOrdinal;
    }

    /** The cross-run address of this activation, or "". */
    public String siteKey() {
        return siteKey(occurrenceId);
    }

    /**
     * The cross-run address of one activation.
     *
     * <p>It is the occurrence id and nothing else, because an occurrence id is
     * minted as {@code sourceKey/region/<regionId>#<ordinal>} and therefore
     * already carries its source. Concatenating a source key onto it a second
     * time would only create a way for the two halves to disagree - and they
     * do disagree in practice: a target activation is re-keyed to the semantic
     * source of the event its failure branch was observed on, while the ports
     * around it still name the source current at root entry. Joining on the
     * minted identity is what keeps those two facts from cancelling the
     * decision out.</p>
     *
     * <p>An empty occurrence is not an address, and decides nothing.</p>
     */
    public static String siteKey(String occurrenceId) {
        return text(occurrenceId).trim();
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

    /**
     * Names what is missing from one stamp, or "" when it is complete.
     *
     * <p>{@code runId} is checked for presence and not for content, which is
     * the one deliberate asymmetry here: no launcher supplies a run identity
     * yet, and refusing every record until one does would delete the evidence
     * instead of naming the gap.</p>
     */
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

    private static String text(String value) {
        return value == null ? "" : value;
    }
}
