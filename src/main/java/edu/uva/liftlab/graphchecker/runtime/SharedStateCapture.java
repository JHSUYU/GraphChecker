package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.d3.smt.JsonFields;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.d3.plan.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.d3.plan.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;

import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.d3.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.decodeVmEnvelope;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.diag;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.parseJson;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.workloadSessionId;

/**
 * The write log of one activation, read out by object.
 *
 * <p>A location is tracked because a symbolic value reached it, and the VM
 * files it under the identity of the object actually written.  So the runtime
 * does not name locations at all: it asks for every location the session
 * tracked at or after this activation's entry event, and publishes what comes
 * back.  {@code location#version -> expression}, keyed by
 * {@code (kind, ownerSymRid, slot)} -- the same key the read nodes carry.</p>
 *
 * <p>What this replaces is a whole layer.  The runtime used to declare which
 * locations were worth versioning, select each one in the VM by its declaring
 * class, field and descriptor, and then invent a receiver identity that would
 * survive into the next session, because the VM's own was session-local and
 * the declaration was the only thing both sides shared.  Every part of that
 * existed to answer "which program location is this a version of", and under
 * by-value retention nothing asks: the object is the answer, the VM states
 * it, and a read resolves inside the session that produced it.</p>
 */
final class SharedStateCapture {
    /** Outcome of one recorded shared-state evidence call. */
    static final class SharedStateResult {
        private final String stage;
        private final int status;
        private final String locationKey;
        private final JsonObject record;

        private SharedStateResult(String stage, int status,
                                  String locationKey, JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.locationKey = safe(locationKey);
            this.record = record;
        }

        boolean ok() {
            return status == SharedStateEvidence.OK;
        }

        @Override
        public String toString() {
            return stage + "/" + status
                    + (locationKey.isEmpty() ? "" : " " + locationKey);
        }
    }

    private SharedStateCapture() {
    }

    /**
     * Reads out every location this activation touched, paging until the VM
     * says the answer is complete.
     *
     * <p>Called while the owner thread still holds the VM context; decoding
     * happens afterwards, in {@link #assembleRecordedSharedState}.  A page
     * that stops short states where to resume, and the loop resumes there; a
     * page that stops short and does not say where is a gap, because a write
     * log short of the truth reads as "the location was never written".</p>
     */
    static RawSharedStateReadOut captureRecordedSharedStateRaw(
            ActiveRegion active, ConcolicVmBroker api,
            RecordedEvidenceIdentity identity) {
        java.util.List<String> pages = new java.util.ArrayList<>();
        String fault = "";
        // The activation's own entry event scopes the read-out: every
        // location tracked at or after it is one this activation touched.
        long after = active == null ? 0L : active.vmRegionEnterEventId;
        for (int page = 0; page < MAX_READ_OUT_PAGES; page++) {
            final String serialized;
            try {
                serialized = api.trackedLocationVersions(after,
                        READ_OUT_PAGE_BYTES);
            } catch (Throwable throwable) {
                fault = "tracked-location read-out failed: "
                        + rootCause(throwable);
                break;
            }
            pages.add(serialized);
            JsonElement parsed = parseJson(serialized);
            if (!parsed.isJsonObject()) {
                fault = "tracked-location read-out returned no JSON object";
                break;
            }
            JsonObject document = parsed.getAsJsonObject();
            if (optionalBool(document, "complete", false)) {
                return new RawSharedStateReadOut(pages, identity, "");
            }
            long next = optionalLongInteger(document, "nextAfterEventId", 0L);
            if (next <= after) {
                fault = "a partial tracked-location read-out states no event "
                        + "to resume from after " + after;
                break;
            }
            after = next;
        }
        if (fault.isEmpty()) {
            fault = "tracked-location read-out did not complete in "
                    + MAX_READ_OUT_PAGES + " pages";
        }
        return new RawSharedStateReadOut(pages, identity, fault);
    }

    /**
     * The most pages one activation's read-out may take.
     *
     * <p>Not a cap on what is published: every page is published, and a
     * read-out that has not finished by here is a stated gap rather than a
     * silent truncation.  It exists so a VM that answers without advancing
     * ends the loop instead of the run.</p>
     */
    private static final int MAX_READ_OUT_PAGES = 4096;

    /** The byte budget of one page; the VM stops at a location boundary. */
    private static final int READ_OUT_PAGE_BYTES = 64 * 1024 * 1024;

    /** Decodes and files the read-out after the VM context is closed. */
    static void assembleRecordedSharedState(
            ActiveRegion active, RawSharedStateReadOut raw) {
        if (raw == null) return;
        if (!raw.fault.isEmpty()) {
            fileShared(failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "", raw.fault),
                    active);
        }
        for (String serialized : raw.pages) {
            try {
                decodeTrackedLocations(serialized, raw.identity, active);
            } catch (Throwable throwable) {
                fileShared(failedShared(SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.MALFORMED_ENVELOPE, "",
                        rootCause(throwable)), active);
            }
        }
    }

    /**
     * One page of the read-out: a document of envelopes over one expression
     * table.
     *
     * <p>The table is per document, so the whole document is imported once
     * and every envelope's references resolve against it.  Each envelope is
     * then exactly the one the VM emits for a single location, and is
     * admitted by the same contract that admitted it before.</p>
     */
    private static void decodeTrackedLocations(
            String serialized, RecordedEvidenceIdentity identity,
            ActiveRegion active) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            fileShared(failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "tracked-location read-out returned no JSON object"),
                    active);
            return;
        }
        JsonObject document = decodeVmEnvelope(parsed.getAsJsonObject(),
                active);
        if (!TRACKED_LOCATIONS_KIND.equals(optionalString(document, "kind"))) {
            fileShared(failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "unsupported tracked-location read-out schema"), active);
            return;
        }
        JsonArray locations = array(document, "locations");
        int stated = optionalInteger(document, "locationCount", -1);
        if (stated >= 0 && stated != locations.size()) {
            fileShared(failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "tracked-location read-out states " + stated
                            + " locations and carries " + locations.size()),
                    active);
            return;
        }
        for (JsonElement element : locations) {
            if (!element.isJsonObject()) {
                fileShared(failedShared(SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.MALFORMED_ENVELOPE, "",
                        "tracked location is not an object"), active);
                continue;
            }
            fileShared(decodeVersionsEnvelope(element.getAsJsonObject(),
                    identity), active);
        }
    }

    static final String TRACKED_LOCATIONS_KIND = "SHARED_TRACKED_LOCATIONS";

    /** One tracked location's write log, or the fault that replaced it. */
    static SharedStateResult decodeVersionsEnvelope(
            JsonObject envelope, RecordedEvidenceIdentity identity) {
        String fault = SharedStateEvidence.versionsFault(envelope);
        if (!fault.isEmpty()) {
            return failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.expressionSerializationTruncationFault(
                            fault)
                            ? SharedStateEvidence
                            .EXPRESSION_SERIALIZATION_TRUNCATED
                            : SharedStateEvidence.containerBaseUnstatedFault(
                            fault)
                            ? SharedStateEvidence.CONTAINER_BASE_UNSTATED
                            : SharedStateEvidence.MALFORMED_ENVELOPE,
                    SharedStateEvidence.locationKey(envelope), fault);
        }
        String locationKey = SharedStateEvidence.locationKey(envelope);
        return new SharedStateResult(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.OK, locationKey,
                writeLogRecord(SharedStateEvidence.versionsRecord(
                        locationKey, envelope, identity)));
    }

    /**
     * One location's write log: {@code location#version -> expression}.
     *
     * <p>This is the whole of what a replay says about shared state.  A read
     * inside one replay is determined -- the location had one version when
     * the read ran and one event wrote it -- so the reader needs the version
     * and the expression written at it, and nothing else.</p>
     *
     * <p>The name is the object.  The VM files a version under the identity
     * of the object it was written to, states that identity in the location
     * key, and the read nodes carry the same one, so a read and a write meet
     * without anything in between having to agree about a declaration.  The
     * carrier block that used to travel with every record -- declaring class,
     * field, descriptor, and a receiver identity synthesised to survive into
     * the next session -- named a location for a reader that no longer
     * exists.</p>
     *
     * <p>The version clock is {@code fieldVersionId}, drawn from the
     * session-global event counter at the moment of publish, which is the
     * counter the decisions' {@code vmEventId} is on.  So "the latest write
     * whose event precedes this access" is a comparison between the two,
     * within one {@code sessionId} -- the counter restarts at session
     * teardown, which is why the session is stated.</p>
     *
     * <p>An INITIAL version stays, tagged as one: a value the recording did
     * not watch being produced is still the value, and saying which kind it
     * is keeps "the program computed this" apart from "the recording started
     * after it".  Its content now arrives from the VM, which snapshots a
     * container at the first symbolic write to it; the runtime used to offer
     * that snapshot itself, one declared container at a time.</p>
     */
    private static JsonObject writeLogRecord(JsonObject record) {
        JsonObject envelope = edu.uva.liftlab.graphchecker.d3.smt.JsonFields
                .object(record, "envelope");
        JsonObject published = new JsonObject();
        copyIfPresent(record, published, "kind");
        copyIfPresent(record, published, "authority");
        copyIfPresent(record, published, "locationKey");
        JsonObject publishedEnvelope = new JsonObject();
        copyIfPresent(envelope, publishedEnvelope, "kind");
        copyIfPresent(envelope, publishedEnvelope, "schemaVersion");
        copyIfPresent(envelope, publishedEnvelope, "sessionId");
        copyIfPresent(envelope, publishedEnvelope, "location");
        JsonArray versions = new JsonArray();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(version, entry, "fieldVersionId");
            copyIfPresent(version, entry, "versionKind");
            // Where the store stood, and which region activation it ran
            // inside: the two halves of the WriteRow's endpoint identity
            // (IDENTITY-V3 sec 1).  The reduction dropped both, so every
            // write endpoint published its location as a site and the empty
            // site index while the VM had stated the bytecode site
            // (REPORT-VM21) and the entry event of the activation -- four
            // reads of one location inside one occurrence were then one
            // endpoint.  Small and bounded: four strings and a long.
            copyIfPresent(version, entry, "site");
            copyIfPresent(version, entry, "regionEnterEventId");
            // A container's INITIAL states the contents tracking began from,
            // and every relation over that container stands on them.  The
            // reduction dropped it, so the corpus could not say whether a
            // base was stated, enumerated or truncated -- and an offline
            // re-drive of the admission that reads it
            // (SharedStateEvidence.containerBaseFault) had nothing to read.
            // It is one small object per container INITIAL.
            copyIfPresent(version, entry, "initialSnapshot");
            copyIfPresent(version, entry, "expression");
            versions.add(entry);
        }
        publishedEnvelope.add("versions", versions);
        // The read log, by event id.  A ReadFromExpression node names the
        // read event it is and the site it stood at, but not the activation
        // that ran it; the log record of the same event does, and that is
        // what files the read under a frame journal.  No value travels with
        // it -- the node already carries the version it observed.
        JsonArray reads = new JsonArray();
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            JsonObject entry = new JsonObject();
            copyIfPresent(read, entry, "readEventId");
            copyIfPresent(read, entry, "regionEnterEventId");
            copyIfPresent(read, entry, "site");
            reads.add(entry);
        }
        publishedEnvelope.add("reads", reads);
        copyIfPresent(envelope, publishedEnvelope, "readLogTruncated");
        published.add("envelope", publishedEnvelope);
        return published;
    }

    /** The reduction, for a test that pins what a version publishes. */
    static JsonObject reduceWriteLogForTest(JsonObject record) {
        return writeLogRecord(record);
    }

    private static void copyIfPresent(JsonObject from, JsonObject to,
                                      String field) {
        JsonElement value = from.get(field);
        if (value != null && !value.isJsonNull()) to.add(field, value);
    }

    /** The identity every record of one read-out batch is stamped with. */
    static RecordedEvidenceIdentity evidenceIdentity(ActiveRegion active) {
        if (active == null) return null;
        long session = workloadSessionId;
        return RecordedEvidenceIdentity.of(
                RecordedEvidenceIdentity.declaredRunId(),
                session != 0L ? "workload#" + session
                        : "region#" + active.token,
                active.activation.taskId,
                active.occurrenceId(),
                active.activation.sourceKey, active.evidenceSnapshot());
    }

    private static SharedStateResult failedShared(String stage, int status,
                                                  String locationKey,
                                                  String detail) {
        return new SharedStateResult(stage, status, safe(locationKey),
                SharedStateEvidence.gap(stage, status, locationKey, detail));
    }

    /** Files one shared-state outcome with the active region. */
    private static void fileShared(SharedStateResult result,
                                   ActiveRegion active) {
        diag(result.ok() ? "SHARED_STATE" : SharedStateEvidence.GAP_KIND,
                result.toString());
        if (active == null) return;
        if (!result.ok()) {
            active.sharedStateGaps.add(result.record);
        } else if (!result.locationKey.isEmpty()) {
            active.sharedStateRecords.put(result.locationKey, result.record);
        }
    }

    /** Raw read-out pages frozen before one VM region is finished. */
    static final class RawSharedStateReadOut {
        private final java.util.List<String> pages;
        final RecordedEvidenceIdentity identity;
        private final String fault;

        private RawSharedStateReadOut(java.util.List<String> pages,
                                      RecordedEvidenceIdentity identity,
                                      String fault) {
            this.pages = pages;
            this.identity = identity;
            this.fault = fault;
        }
    }
}
