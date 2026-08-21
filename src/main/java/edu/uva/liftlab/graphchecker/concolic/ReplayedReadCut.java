package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Whether a replay realised the read-from arm the model selected.
 *
 * <p>The gate was compiled from one execution and the answer has to come from
 * another, so nothing session-local can be used to ask the question. A read
 * event id and a field version id name events of the run that recorded them -
 * a second session restarts the counter, and even within one JVM the second
 * session's first event is again event 1 - so keying validation on them would
 * compare two different runs' event 21. The identity that survives is the one
 * {@link RecordedReadFrom} joins on: the declared field and the two minted
 * activation occurrences. This class re-derives the provenance from the
 * replay's <em>own</em> version store under that key, and never from the
 * reference run's ids.</p>
 *
 * <p>Three things must hold before an arm counts as realised, and each is
 * checked separately so a partial answer says which part is missing:</p>
 *
 * <ul>
 *   <li>the replay's own evidence proves this reader took this writer - a
 *   guarded read proves nothing and stays undecided;</li>
 *   <li>the read observed a concrete version - the value came from the
 *   program, not from anything this checker supplied;</li>
 *   <li>the exchange happened in this run - the selected writer region really
 *   did publish a version of that field here.</li>
 * </ul>
 *
 * <p>Nothing here writes, replaces or supplies a value: validation reads the
 * evidence the run produced. An arm that cannot be decided is an honest
 * coverage gap, never a pass.</p>
 */
public final class ReplayedReadCut {

    public static final int SCHEMA_VERSION = 1;
    public static final String KIND = "REPLAY_READ_CUT_REALISATION";
    public static final String AUTHORITY = "REPLAY_READ_CUT_V1";

    /** The replay's own evidence proves the selected read-from. */
    public static final String REALISED = "REALISED";
    /** The replay's own evidence names a different writer. */
    public static final String NOT_REALISED = "NOT_REALISED";
    /** The replay's evidence does not answer; the arm stays a gap. */
    public static final String UNDECIDED = "UNDECIDED";

    /** The replay took a different writer for this read. */
    public static final String REPLAY_SELECTED_ANOTHER_WRITER =
            "GATE_REPLAY_SELECTED_ANOTHER_WRITER";
    /** The replay watched nothing that decides this pair. */
    public static final String REPLAY_HAS_NO_RECORDED_EVIDENCE =
            "GATE_REPLAY_HAS_NO_RECORDED_EVIDENCE";
    /** The replay's own read of this location stayed guarded. */
    public static final String REPLAY_PROVENANCE_STILL_GUARDED =
            "GATE_REPLAY_PROVENANCE_STILL_GUARDED";
    /** No read of this field by this reader observed a concrete version. */
    public static final String READ_VERSION_NOT_OBSERVED =
            "GATE_READ_VERSION_NOT_OBSERVED";
    /** The selected writer region published no version of this field here. */
    public static final String EXCHANGE_NOT_OBSERVED =
            "GATE_EXCHANGE_NOT_OBSERVED";

    private final List<JsonObject> verdicts = new ArrayList<>();
    private final List<JsonObject> gaps = new ArrayList<>();

    private ReplayedReadCut() {
    }

    /**
     * Validates one replay against the plan it carried.
     *
     * @param plan            the {@code readCutPlan} of the executed task
     * @param recordedMembers the replay's own {@code recordedSharedState}
     *                        members
     */
    public static ReplayedReadCut validate(
            JsonObject plan, Collection<JsonObject> recordedMembers) {
        ReplayedReadCut replayed = new ReplayedReadCut();
        if (!SelectedReadCut.isReplayPlan(plan)) return replayed;
        RecordedReadFrom index = RecordedReadFrom.index(recordedMembers);
        List<JsonObject> versionRecords = versionRecords(recordedMembers);
        for (JsonElement element : array(plan, "gates")) {
            if (!element.isJsonObject()) continue;
            replayed.validateGate(element.getAsJsonObject(), index,
                    versionRecords);
        }
        return replayed;
    }

    private void validateGate(JsonObject gate, RecordedReadFrom index,
                              List<JsonObject> versionRecords) {
        String unsafe = SparseReadCutGate.unsafeGateReason(gate);
        if (!unsafe.isEmpty()) {
            // A row that is not a compiled gate cannot be validated, and
            // treating it as absent would hide that a replay carried it.
            gaps.add(SparseReadCutGate.refusal(unsafe, gate,
                    "the replay carried a gate this authority did not "
                            + "compile, so nothing validates it"));
            verdicts.add(verdict(gate, UNDECIDED, unsafe, false, false));
            return;
        }
        String field = string(gate, "readFromField");
        String writer = string(gate, "writerRegionId");
        String reader = string(gate, "readerRegionId");
        // A compiled gate carries static regions, because that is all the VM
        // expression it was compiled from carried.  The decision is keyed on
        // activations, so the regions are resolved against this replay's own
        // records first; a region the replay activated more than once
        // resolves to nothing and the arm stays an honest gap rather than
        // being credited to whichever activation happened to be indexed.
        RecordedReadFrom.Decision decision = index.decide(field,
                index.siteOfRegion(field, writer),
                index.siteOfRegion(field, reader));
        boolean observedRead = observedConcreteRead(versionRecords, field,
                reader);
        boolean observedExchange = publishedVersion(versionRecords, field,
                writer);
        if (!observedRead) {
            gaps.add(SparseReadCutGate.refusal(READ_VERSION_NOT_OBSERVED,
                    gate, "no read of " + field + " by " + reader
                            + " observed a concrete version in this replay"));
        }
        if (!observedExchange) {
            gaps.add(SparseReadCutGate.refusal(EXCHANGE_NOT_OBSERVED, gate,
                    "writer region " + writer + " published no version of "
                            + field + " in this replay"));
        }
        String state = state(decision, observedRead, observedExchange);
        String reason = reason(decision, observedRead, observedExchange);
        if (!reason.isEmpty() && !READ_VERSION_NOT_OBSERVED.equals(reason)
                && !EXCHANGE_NOT_OBSERVED.equals(reason)) {
            gaps.add(SparseReadCutGate.refusal(reason, gate,
                    detail(decision, field, writer, reader)));
        }
        verdicts.add(verdict(gate, state, reason, observedRead,
                observedExchange));
    }

    /**
     * The verdict of one gate.
     *
     * <p>Only a proven read-from with both observations counts as realised: a
     * decision the replay left guarded says the run could not tell this writer
     * from another, which is exactly the claim the whole mechanism refuses to
     * make on equal values.</p>
     */
    private static String state(RecordedReadFrom.Decision decision,
                                boolean observedRead,
                                boolean observedExchange) {
        if (decision == RecordedReadFrom.Decision.RECORDED_EXCLUDED) {
            return NOT_REALISED;
        }
        return decision == RecordedReadFrom.Decision.RECORDED_EXACT
                && observedRead && observedExchange ? REALISED : UNDECIDED;
    }

    private static String reason(RecordedReadFrom.Decision decision,
                                 boolean observedRead,
                                 boolean observedExchange) {
        switch (decision) {
            case RECORDED_EXCLUDED:
                return REPLAY_SELECTED_ANOTHER_WRITER;
            case NO_RECORDED_EVIDENCE:
                return REPLAY_HAS_NO_RECORDED_EVIDENCE;
            case RECORDED_GUARDED_CANDIDATE:
                return REPLAY_PROVENANCE_STILL_GUARDED;
            default:
                break;
        }
        if (!observedRead) return READ_VERSION_NOT_OBSERVED;
        return observedExchange ? "" : EXCHANGE_NOT_OBSERVED;
    }

    private static String detail(RecordedReadFrom.Decision decision,
                                 String field, String writer, String reader) {
        switch (decision) {
            case RECORDED_EXCLUDED:
                return "the replay's own evidence for " + field + " read by "
                        + reader + " names a writer other than " + writer;
            case NO_RECORDED_EVIDENCE:
                return "the replay recorded nothing that decides " + field
                        + " read by " + reader;
            default:
                return "the replay's read of " + field + " by " + reader
                        + " stayed guarded, so it proves no writer";
        }
    }

    private JsonObject verdict(JsonObject gate, String state, String reason,
                               boolean observedRead,
                               boolean observedExchange) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", SCHEMA_VERSION);
        row.addProperty("kind", KIND);
        row.addProperty("authority", AUTHORITY);
        row.addProperty("gateId", string(gate, "gateId"));
        row.addProperty("selector", string(gate, "selector"));
        row.addProperty("readFromField", string(gate, "readFromField"));
        row.addProperty("writerRegionId", string(gate, "writerRegionId"));
        row.addProperty("readerRegionId", string(gate, "readerRegionId"));
        row.addProperty("state", state);
        row.addProperty("reason", reason);
        row.addProperty("observedReadVersion", observedRead);
        row.addProperty("observedExchange", observedExchange);
        // The gate promised these; the verdict repeats what the validation
        // actually did, so a reader never has to infer it from the promise.
        row.addProperty("changedProgramValue", false);
        row.addProperty("orderEnforced", false);
        return row;
    }

    /**
     * Whether some read of {@code field} by {@code reader} observed a
     * concrete version in this run.
     *
     * <p>A read with no observed fingerprint is a read the store knows of but
     * whose value nothing witnessed, and a gate whose value was not witnessed
     * validates nothing.</p>
     */
    private static boolean observedConcreteRead(
            List<JsonObject> versionRecords, String field, String reader) {
        for (JsonObject record : recordsOf(versionRecords, field)) {
            for (JsonElement element
                    : array(object(record, "envelope"), "reads")) {
                JsonObject read = element.getAsJsonObject();
                String kind = string(read, "observedFingerprintKind");
                if (reader.equals(string(read, "regionId"))
                        && !kind.isEmpty() && !"NONE".equals(kind)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether {@code writer} published a version of {@code field} here. */
    private static boolean publishedVersion(List<JsonObject> versionRecords,
                                            String field, String writer) {
        for (JsonObject record : recordsOf(versionRecords, field)) {
            for (JsonElement element
                    : array(object(record, "envelope"), "versions")) {
                if (writer.equals(string(element.getAsJsonObject(),
                        "regionId"))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static List<JsonObject> recordsOf(List<JsonObject> records,
                                              String field) {
        List<JsonObject> matching = new ArrayList<>();
        for (JsonObject record : records) {
            JsonObject carrier = object(record, "carrier");
            if (field.equals(RecordedReadFrom.fieldKey(
                    string(carrier, "declaringClass"),
                    string(carrier, "fieldName")))) {
                matching.add(record);
            }
        }
        return matching;
    }

    private static List<JsonObject> versionRecords(
            Collection<JsonObject> recordedMembers) {
        List<JsonObject> records = new ArrayList<>();
        if (recordedMembers == null) return records;
        for (JsonObject member : recordedMembers) {
            if (member == null || !SharedStateEvidence.RECORDED_KIND.equals(
                    string(member, "kind"))) {
                continue;
            }
            for (JsonElement element : array(member, "versions")) {
                if (!element.isJsonObject()) continue;
                JsonObject record = element.getAsJsonObject();
                if (SharedStateEvidence.isVersionsRecord(record)) {
                    records.add(record);
                }
            }
        }
        return records;
    }

    /** Whether every gate the replay carried was realised. */
    public boolean allRealised() {
        if (verdicts.isEmpty()) return false;
        for (JsonObject verdict : verdicts) {
            if (!REALISED.equals(string(verdict, "state"))) return false;
        }
        return true;
    }

    /** One verdict per gate the replay carried. */
    public List<JsonObject> verdicts() {
        return Collections.unmodifiableList(verdicts);
    }

    /** Named coverage gaps, in the gate gap family. */
    public List<JsonObject> gaps() {
        return Collections.unmodifiableList(gaps);
    }

    public boolean isEmpty() {
        return verdicts.isEmpty();
    }

    /** The validation as one summary member. */
    public JsonObject toJson() {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", SCHEMA_VERSION);
        result.addProperty("kind", KIND);
        result.addProperty("authority", AUTHORITY);
        result.addProperty("gates", verdicts.size());
        result.addProperty("allRealised", allRealised());
        JsonArray rows = new JsonArray();
        for (JsonObject verdict : verdicts) rows.add(verdict.deepCopy());
        result.add("verdicts", rows);
        return result;
    }
}
