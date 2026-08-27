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

/** Whether a replay realised the read-from arm the model selected. */
public final class ReplayedReadCut {

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
        String reason = reason(decision, observedRead, observedExchange);
        if (!reason.isEmpty() && !READ_VERSION_NOT_OBSERVED.equals(reason)
                && !EXCHANGE_NOT_OBSERVED.equals(reason)) {
            gaps.add(SparseReadCutGate.refusal(reason, gate,
                    detail(decision, field, writer, reader)));
        }
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


    /**
     * Whether some read of {@code field} by {@code reader} observed a
     * concrete version in this run.
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

    /** Named coverage gaps, in the gate gap family. */
    public List<JsonObject> gaps() {
        return Collections.unmodifiableList(gaps);
    }

}
