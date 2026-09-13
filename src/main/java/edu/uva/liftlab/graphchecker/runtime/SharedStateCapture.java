package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SymbolicPropagationClosure;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.AccessorCallContext;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.MissingValue;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.CURRENT_ACCESSOR_CALL_CONTEXT;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.activeRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.decodeVmEnvelope;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.readExactField;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resolveFieldPathLeafOwner;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.resolveFieldPathValue;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.workloadSessionId;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.beginBookkeeping;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.diag;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.endBookkeeping;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.parseJson;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.rootCause;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;

/**
 * Selecting, reading and filing the shared-state evidence of one region.
 */
final class SharedStateCapture {
    /** Outcome of one recorded shared-state evidence call. */
    static final class SharedStateResult {
        private final String stage;
        private final int status;
        private final String locationKey;
        private final JsonObject record;

        private SharedStateResult(String stage, int status, String locationKey,
                                  JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.locationKey = locationKey;
            this.record = record;
        }

        boolean ok() {
            return status == SharedStateEvidence.OK;
        }

        /** Named reason for a failure; empty for an admitted answer. */
        String reason() {
            return SharedStateEvidence.reason(status);
        }

        @Override
        public String toString() {
            return "SharedStateResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " location=" + locationKey + "]";
        }
    }

    /**
     * Selects one instance or static field as a symbolic carrier. Later
     * writes publish candidate expressions and reads capture their bounded
     * candidate snapshot as a guarded value.
     */
    static SharedStateResult selectSharedFieldCarrier(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        beginBookkeeping();
        try {
            return selectedCarrier(SharedCarrier.field(owner, declaringClass,
                    fieldName, descriptor));
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Selects one map as a symbolic carrier of its own whole state.
     *
     * <p>{@code contentMonitor} is the object whose monitor the workload
     * guards the container with - normally the receiver that declares the
     * field - so the initial content can be read without racing a writer.</p>
     */
    static SharedStateResult selectSharedMapCarrier(
            Object map, Object contentMonitor, String declaringClass,
            String fieldName, String descriptor) {
        beginBookkeeping();
        try {
            return selectedCarrier(SharedCarrier.map(map, contentMonitor,
                    declaringClass, fieldName, descriptor));
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Selects one carrier of any shape, publishing the same select-stage
     * evidence for a refused shape, an unavailable VM, a failed invoke and a
     * negative answer whichever shape asked.
     */
    private static SharedStateResult selectedCarrier(SharedCarrier carrier) {
        ActiveRegion active = activeRegion();
        return selectedCarrier(carrier, active == null
                ? null : active.activation, active);
    }

    /** Selects a carrier using the task that declared this exact access. */
    private static SharedStateResult selectedCarrier(
            SharedCarrier carrier, RuntimeTask locator) {
        return selectedCarrier(carrier, locator, activeRegion());
    }

    /** Selects one physical carrier while retaining its declaring task. */
    private static SharedStateResult selectCarrierForTask(
            SharedCarrier carrier, RuntimeTask task) {
        beginBookkeeping();
        try {
            return selectedCarrier(carrier, task);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult selectedCarrier(
            SharedCarrier carrier, RuntimeTask locator,
            ActiveRegion active) {
        carrier.bindPlannedReceiver(locator);
        String missing = carrier.missing();
        if (!missing.isEmpty()) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "", missing),
                    null, active);
        }
        ConcolicVmBroker api = engine();
        // Before the selection, and so before this region's first write to
        // it: the INITIAL version records whatever the container's state root
        // already said, and only a chain installed now is in it.
        stateInitialContent(api, carrier, active);
        long initial;
        try {
            initial = carrier.select(api);
        } catch (Throwable throwable) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, active);
        }
        // The VM returns zero when this exact location is already selected in
        // the current session.  Selection is idempotent: this activation must
        // still retain the carrier so it can read the shared version snapshot.
        if (initial < 0L) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    initial < Integer.MIN_VALUE
                            ? SharedStateEvidence.MALFORMED_ENVELOPE
                            : (int) initial, "",
                    carrier.selectApi() + " returned " + initial), null,
                    active);
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", new JsonObject()),
                carrier, active);
    }

    /**
     * Tells the recorder what this container held, so the carrier's INITIAL
     * version states its content instead of an opaque root.
     *
     * <p>Declining is a first-class answer: an unrecognized class, a
     * container past the VM's entry bound, a walk that raced a writer, or a
     * recorded mutation history whose base cannot be recovered all leave the
     * opaque root in place and publish one {@code INITIAL_SNAPSHOT_SKIPPED}
     * row naming which. A wrong snapshot is a false premise about the
     * recorded execution, so this never guesses.</p>
     *
     * <p>"The VM answered" is not "the content is stated". The offer has
     * several outcomes and only some of them leave the INITIAL version with a
     * base; reading them all as one acceptance is what published carriers
     * with a free initial container as though they were pinned.</p>
     */
    private static void stateInitialContent(ConcolicVmBroker api,
                                            SharedCarrier carrier,
                                            ActiveRegion active) {
        InitialContainerSnapshot.Outcome outcome;
        try {
            outcome = InitialContainerSnapshot.install(
                    api::snapshotContainer, carrier.owner(),
                    carrier.contentMonitor(), carrier.mapState());
        } catch (Throwable unavailable) {
            // A failed install leaves the INITIAL version opaque, exactly as
            // a declined one does -- so it files the same row.  Turning it
            // into a silent null here bypassed the INITIAL_SNAPSHOT_SKIPPED
            // row below and manufactured a free initial container that read
            // as though it had simply never been offered.
            outcome = InitialContainerSnapshot.unavailable(
                    rootCause(unavailable));
        }
        if (outcome == null) return;
        // Whether the initial content was stated is already in the write
        // log: a container this run stated carries a SNAPSHOT_BASE over its
        // members, and one it declined keeps the opaque INITIAL root.  The
        // two telemetry rows that said the same thing a second time were
        // read by nothing.
        if (outcome.stated) {
            diag(outcome.statedEvent(), InitialContainerSnapshot.statedRow(
                    outcome, carrier.describe()).toString());
            return;
        }
        if (!outcome.declined()) return;
        diag(InitialContainerSnapshot.SKIPPED_EVENT,
                InitialContainerSnapshot.skipRow(outcome,
                        carrier.describe()).toString());
    }

    /**
     * Raw VM read-outs already taken while closing the selected occurrence on
     * this thread, keyed by the location they answer for.
     *
     * <p>Several evidence builders may ask for the same selected carrier.</p>
     */
    static final ThreadLocal<Map<String, String>> READ_OUT_MEMO =
            new ThreadLocal<Map<String, String>>();

    // The scope discipline - open, memoize, close, never answer outside a
    // scope - is what keeps a stale read-out from being served for a live
    // location.

    /** The bytes already read for {@code key} in this close, or null. */
    private static String memoizedReadOut(String key) {
        Map<String, String> memo = READ_OUT_MEMO.get();
        return memo == null ? null : memo.get(key);
    }

    /** Files {@code serialized} under {@code key} and returns it unchanged. */
    private static String memoizeReadOut(String key, String serialized) {
        Map<String, String> memo = READ_OUT_MEMO.get();
        if (memo != null && serialized != null) memo.put(key, serialized);
        return serialized;
    }

    /** Reads one VM version envelope. */
    static SharedStateResult decodeVersionsEnvelope(
            String serialized, SharedCarrier carrier,
            RecordedEvidenceIdentity identity, ActiveRegion active) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            return failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "version read-out returned no JSON object");
        }
        JsonObject envelope = decodeVmEnvelope(parsed.getAsJsonObject(),
                active);
        String fault = SharedStateEvidence.versionsFault(envelope);
        if (!fault.isEmpty()) {
            boolean unselected = SharedStateEvidence.VERSIONS_ENVELOPE_KIND
                    .equals(optionalString(envelope, "kind"))
                    && !optionalBool(envelope, "selected", false);
            int status = unselected ? SharedStateEvidence.NOT_SELECTED
                    : SharedStateEvidence
                    .expressionSerializationTruncationFault(fault)
                    ? SharedStateEvidence.EXPRESSION_SERIALIZATION_TRUNCATED
                    : SharedStateEvidence.MALFORMED_ENVELOPE;
            return failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    status,
                    SharedStateEvidence.locationKey(envelope), fault);
        }
        String locationKey = SharedStateEvidence.locationKey(envelope);
        JsonObject record = SharedStateEvidence.versionsRecord(locationKey,
                envelope, identity);
        if (carrier != null) {
            // The VM addresses a location by its own session identity, which
            // is a number that means nothing in the next session.  The
            // carrier is the only name that crosses: the declaring class,
            // field, descriptor and receiver that say which location in the
            // program this is.  One per location -- it describes the slot,
            // not any one write to it.
            record.add("carrier", carrier.toJson());
        }
        return new SharedStateResult(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.OK, locationKey,
                writeLogRecord(record));
    }

    /**
     * One location's write log: {@code location#version -> expression}.
     *
     * <p>This is the whole of what a replay says about shared state.  A read
     * inside one replay is determined -- the location had one version when
     * the read ran and one event wrote it -- so the reader needs the version
     * and the expression written at it, and nothing else.  Everything the
     * envelope used to carry besides that existed for an offline stitcher
     * that merged many replays and therefore had to re-derive, per version,
     * which activation wrote it, under which case, on which node, and which
     * reads elsewhere might have observed it: the writer source key,
     * occurrence and activation closure, the read log with its reader
     * authorities and consumer anchors, the carrier's declared field, the
     * per-version path guard, the evidence identity, and the truncation and
     * selection flags.  None of it is an input to in-session resolution, and
     * publishing it made the write log four times its own size.</p>
     *
     * <p>The carrier stays with it, once per location.  A session-local owner
     * rid is not a name the next session can resolve, so without the
     * declaring class, field, descriptor and receiver the location cannot be
     * matched across sessions at all -- which is what
     * {@code canonicalizeLocations} and {@code RuntimeMapIdentity.of} do with
     * it.  Dropping it cost 18 LOCATION_NOT_NAMED_ACROSS_SESSIONS and 12
     * SHARED_STATE_MAP_STATE_IDENTITY_MISSING.</p>
     *
     * <p>An INITIAL version stays, tagged as one: a value the recording did
     * not watch being produced is still the value, and saying which kind it
     * is what keeps "the program computed this" apart from "the recording
     * started after it".</p>
     */
    private static JsonObject writeLogRecord(JsonObject record) {
        JsonObject envelope = object(record, "envelope");
        JsonObject published = new JsonObject();
        copyIfPresent(record, published, "kind");
        copyIfPresent(record, published, "authority");
        copyIfPresent(record, published, "locationKey");
        copyIfPresent(record, published, "carrier");
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
            copyIfPresent(version, entry, "expression");
            versions.add(entry);
        }
        publishedEnvelope.add("versions", versions);
        published.add("envelope", publishedEnvelope);
        return published;
    }

    private static void copyIfPresent(JsonObject from, JsonObject to,
                                      String field) {
        JsonElement value = from.get(field);
        if (value != null && !value.isJsonNull()) to.add(field, value);
    }

    /** The identity every record of one read-out batch is stamped with. */
    static RecordedEvidenceIdentity evidenceIdentity(
            ActiveRegion active) {
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

    /** One shared location a task asked this activation to select. */
    static final class SharedCarrierRequest {
        final String declaringClass;
        final String fieldName;
        final String descriptor;
        final String sourceKind;
        final int index;
        final boolean element;
        final boolean mapState;
        /** Came from the planner's cross-region shared-state selection. */
        final boolean plannerDeclared;
        final List<String> fieldPath = new ArrayList<>();

        SharedCarrierRequest(JsonObject declaration,
                             boolean plannerDeclared) {
            this.declaringClass = optionalString(declaration, "declaringClass");
            this.fieldName = optionalString(declaration, "fieldName");
            this.descriptor = optionalString(declaration, "descriptor");
            this.sourceKind = optionalString(declaration, "sourceKind");
            this.index = optionalInteger(declaration, "index", -1);
            this.element = "ARRAY_ELEMENT".equals(
                    optionalString(declaration, "kind"));
            this.mapState = SharedStateEvidence.LOCATION_KIND_MAP_STATE
                    .equals(optionalString(declaration, "kind"));
            this.plannerDeclared = plannerDeclared;
            for (JsonElement segment : array(declaration, "fieldPath")) {
                if (segment.isJsonPrimitive()) {
                    fieldPath.add(safe(segment.getAsString()));
                }
            }
        }

        /** How this declaration reads back in a gap. */
        String describe() {
            return (element ? "element " + index
                    : (mapState ? "map state of " : "")
                    + declaringClass + "#" + fieldName + ":" + descriptor)
                    + " via receiver path " + fieldPath;
        }

        /**
         * The object the selection is made on, reached from {@code receiver},
         * or {@link MissingValue#INSTANCE} when the path does not resolve.
         */
        Object resolveOwner(Object receiver) {
            if (fieldPath.isEmpty()) return receiver;
            return element || mapState
                    ? resolveFieldPathValue(receiver, fieldPath)
                    : resolveFieldPathLeafOwner(receiver, fieldPath);
        }

        /**
         * The object that declares this carrier's field, which is the one
         * the workload's {@code synchronized} methods lock when they touch
         * it. Null when this activation cannot name it.
         */
        Object resolveContentMonitor(Object receiver) {
            Object monitor = fieldPath.isEmpty() ? receiver
                    : resolveFieldPathLeafOwner(receiver, fieldPath);
            return monitor == MissingValue.INSTANCE ? null : monitor;
        }

        boolean accessOwnerBound() {
            return "ACTIVATION_FIELD_RECEIVER".equals(sourceKind);
        }

        boolean matchesAccess(String fieldSignature) {
            // Cheapest test first: this hook now stands at every selected
            // field write as well as every selected read, and parsing a
            // signature for a carrier that is not access-bound would be work
            // done per store for nothing.
            if (!accessOwnerBound()) return false;
            DeclaredField field = FieldPathSpec.declaredField(
                    fieldSignature);
            return field != null
                    && declaringClass.equals(field.owner())
                    && fieldName.equals(field.name())
                    && (descriptor.isEmpty() || descriptor.equals(
                    javaTypeDescriptor(field.type())));
        }

        boolean observesSharedRead(String fieldSignature) {
            return plannerDeclared && matchesAccess(fieldSignature);
        }

        /** Activation-local identity of this exact access-bound request. */
        String accessSelectionKey(Object owner) {
            return (mapState ? "MAP" : element ? "ELEMENT" : "FIELD")
                    + "/" + System.identityHashCode(owner) + "/"
                    + declaringClass + "#" + fieldName + ":" + descriptor
                    + "@" + index;
        }

        /**
         * Selects this declared location on its exact access owner.
         *
         * <p>Wave 3: a declared shared location keeps EVERY symbolic write of
         * the session as a version.  There is no producer to admit and no
         * version to pick - the composer enumerates the versions the VM
         * already recorded as read-from arms - so selection is the whole of
         * what the runtime decides here.</p>
         */
        SharedStateResult selectAtAccess(Object owner,
                                         String fieldSignature,
                                         RuntimeTask task,
                                         ConsumerAccessAnchor consumer) {
            SharedCarrier carrier = mapState
                    ? SharedCarrier.map(
                    readExactField(owner, fieldSignature), owner,
                    declaringClass, fieldName, descriptor)
                    : SharedCarrier.field(owner, declaringClass,
                    fieldName, descriptor);
            carrier.recordConsumerAccess(consumer);
            return selectCarrierForTask(carrier, task);
        }

        /** Selects this carrier for {@code active}, or names why it cannot. */
        SharedStateResult select(ActiveRegion active, RuntimeTask task) {
            Object owner = resolveOwner(active.receiver);
            if (owner == MissingValue.INSTANCE) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.MISSING_METADATA, "",
                        "declared carrier owner is unreachable from the "
                                + "region receiver: " + describe()), null,
                        active);
            }
            if (element) {
                return selectCarrierForTask(
                        SharedCarrier.element(owner, index), task);
            }
            // A carrier the plan declares and the region selects at entry is
            // reached through no field access, so it records no access
            // anchor -- and a location the plan never also reads as a
            // symbolic input has no frozen receiver locator either.  With
            // neither, bindPlannedReceiver binds 0 and the read-out refuses
            // the location outright.  That is not a property of the field's
            // shape or width: it is whether the plan happened to freeze a
            // locator, so on one object one field is captured and the next
            // is dropped.  The region entry is itself a replay-stable
            // anchor -- the root method and this activation's occurrence,
            // no object id -- so the carrier is named from it.
            ConsumerAccessAnchor entry = regionEntryAnchor(active);
            if (mapState) {
                SharedCarrier map = SharedCarrier.map(owner,
                        resolveContentMonitor(active.receiver),
                        declaringClass, fieldName, descriptor);
                map.recordEntryAnchor(entry);
                return selectCarrierForTask(map, task);
            }
            SharedCarrier field = SharedCarrier.field(owner,
                    declaringClass, fieldName, descriptor);
            field.recordEntryAnchor(entry);
            return selectCarrierForTask(field, task);
        }
    }

    /** Selects every carrier this activation's task declared. */
    static void selectDeclaredSharedCarriers(ActiveRegion active,
                                                    RuntimeTask task) {
        for (SharedCarrierRequest request : task.sharedCarriers) {
            // This binding is resolved by the exact instrumented field access,
            // where the actual declaring object is available.
            if (request.accessOwnerBound()) continue;
            try {
                request.select(active, task);
            } catch (Throwable throwable) {
                recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        request.describe() + ": " + rootCause(throwable)),
                        null, active);
            }
        }
    }

    /**
     * Stable identity of the getfield this hook immediately precedes.
     * Accessor implementations use the caller site which selected the
     * receiver; direct reads use their own bytecode site.
     */
    static ConsumerAccessAnchor consumerAccessAnchor(
            ActiveRegion active, String method, int unitIndex,
            int occurrence, Object owner) {
        AccessorCallContext accessor = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (accessor != null && active != null
                && accessor.regionToken == active.token
                && accessor.thread == Thread.currentThread()
                && accessor.receiver == owner
                && !accessor.callSiteId.isEmpty()
                && accessor.occurrence > 0) {
            return new ConsumerAccessAnchor(accessor.callSiteId,
                    accessor.occurrence);
        }
        if (safe(method).isEmpty() || unitIndex < 0 || occurrence < 1) {
            return null;
        }
        return new ConsumerAccessAnchor(SiteId.of(method, unitIndex),
                occurrence);
    }

    /**
     * The region entry, as an access anchor.
     *
     * <p>A declared carrier is selected once when the activation starts, at
     * no bytecode access of its own.  Its entry is still an exact site --
     * the region's root method, with this activation's ordinal as the
     * occurrence -- and carries no object id, so it names the receiver as
     * stably across sessions as a field access does.</p>
     */
    private static ConsumerAccessAnchor regionEntryAnchor(
            ActiveRegion active) {
        if (active == null || active.activation == null) return null;
        String root = safe(active.activation.rootMethod);
        if (root.isEmpty()) return null;
        int occurrence = Math.max(1, active.activationOrdinal);
        return new ConsumerAccessAnchor(root, occurrence);
    }

    /** Selects a demanded carrier on its exact field-access owner once. */
    static void selectAccessOwnerSharedCarriers(
            ActiveRegion active, Object owner, String fieldSignature,
            ConsumerAccessAnchor consumer) {
        selectAccessOwnerSharedCarriers(active, active.activation, owner,
                fieldSignature, consumer);
    }

    /** Selects one task's access-owner carriers for this activation. */
    static void selectAccessOwnerSharedCarriers(
            ActiveRegion active, RuntimeTask task, Object owner,
            String fieldSignature, ConsumerAccessAnchor consumer) {
        if (wholeStateAndPointerCarrier(task.sharedCarriers,
                fieldSignature)) {
            // One field is one location.  Selecting it as both a whole
            // container state and a reference slot publishes two independent
            // version chains over the same storage - the selection keys carry
            // the kind, so nothing downstream collapses them - and a reader
            // would then choose its arm from one of two disjoint candidate
            // sets.  Refuse rather than double-count.
            recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    fieldSignature + ": declared as both a whole container"
                            + " state and a reference slot"), null, active);
            return;
        }
        Set<String> visited = new LinkedHashSet<>();
        for (SharedCarrierRequest request : task.sharedCarriers) {
            if (!request.matchesAccess(fieldSignature)) continue;
            String selectionKey = request.accessSelectionKey(owner);
            if (!visited.add(selectionKey)) {
                continue;
            }
            SharedCarrier held = active.sharedCarriers.get(selectionKey);
            if (held != null) {
                held.recordConsumerAccess(consumer);
                continue;
            }
            try {
                request.selectAtAccess(owner, fieldSignature, task,
                        consumer);
            } catch (Throwable throwable) {
                recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        request.describe() + ": " + rootCause(throwable)),
                        null, active);
            }
        }
    }

    /**
     * Whether this task declares one field as both a whole container state
     * and a reference slot.  An array element declaration is a third, genuinely
     * separate location and never conflicts.
     */
    static boolean wholeStateAndPointerCarrier(
            List<SharedCarrierRequest> requests, String fieldSignature) {
        boolean wholeState = false;
        boolean pointer = false;
        for (SharedCarrierRequest request : requests) {
            if (!request.matchesAccess(fieldSignature) || request.element) {
                continue;
            }
            if (request.mapState) {
                wholeState = true;
            } else {
                pointer = true;
            }
        }
        return wholeState && pointer;
    }

    /** One stable region-local consumer access, independent of object ids. */
    static final class ConsumerAccessAnchor {
        final String siteId;
        final int occurrence;

        ConsumerAccessAnchor(String siteId, int occurrence) {
            this.siteId = safe(siteId);
            this.occurrence = occurrence;
        }
    }

    /** One location this activation selected as a symbolic carrier. */
    static final class SharedCarrier {
        /** Selection shapes, which is the only thing a carrier varies in. */
        static final String SHAPE_FIELD = "FIELD";
        static final String SHAPE_ELEMENT = "ELEMENT";
        static final String SHAPE_MAP = "MAP";

        private final Object owner;
        /**
         * The lock the workload guards this carrier's content with, when the
         * declaring receiver is known.  {@code BlockTokenSecretManager}
         * reaches {@code allKeys} only from synchronized methods, so reading
         * the content under the receiver's monitor is what makes the initial
         * snapshot the content that was actually there.
         */
        private final Object contentMonitor;
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final int index;
        private final String shape;
        /** Frozen trace locator from this task's selected causal edge. */
        private long plannedReceiverObjectId;
        /** Reads of this live carrier in the publishing activation. */
        /**
         * The region entry, kept apart from the accesses.
         *
         * <p>It is the last resort for naming this location, never a
         * competitor: a map reached by an access in one activation and
         * selected at entry in another would otherwise take an entry name
         * once and an access name the next time, and one map would have two
         * identities in one replay.  An access names the location better --
         * it is where the program touched it -- so the entry only answers
         * when nothing else does.</p>
         */
        private ConsumerAccessAnchor entryAnchor;
        private final List<ConsumerAccessAnchor> consumerAccesses =
                new ArrayList<>();

        private SharedCarrier(Object owner, Object contentMonitor,
                              String declaringClass,
                              String fieldName, String descriptor, int index,
                              String shape) {
            this.owner = owner;
            this.contentMonitor = contentMonitor;
            this.declaringClass = declaringClass;
            this.fieldName = fieldName;
            this.descriptor = descriptor;
            this.index = index;
            this.shape = shape;
        }

        static SharedCarrier field(Object owner, String declaringClass,
                                   String fieldName, String descriptor) {
            return new SharedCarrier(owner, null, safe(declaringClass),
                    safe(fieldName), safe(descriptor), -1, SHAPE_FIELD);
        }

        static SharedCarrier element(Object array, int index) {
            return new SharedCarrier(array, null, "", "", "", index,
                    SHAPE_ELEMENT);
        }

        /** One map selected as the carrier of its own whole state. */
        static SharedCarrier map(Object map, String declaringClass,
                                 String fieldName, String descriptor) {
            return map(map, null, declaringClass, fieldName, descriptor);
        }

        /**
         * The same carrier, naming the receiver whose monitor the workload
         * guards the content with.
         */
        static SharedCarrier map(Object map, Object contentMonitor,
                                 String declaringClass, String fieldName,
                                 String descriptor) {
            return new SharedCarrier(map, contentMonitor,
                    safe(declaringClass), safe(fieldName), safe(descriptor),
                    -1, SHAPE_MAP);
        }

        boolean mapState() {
            return SHAPE_MAP.equals(shape);
        }

        Object owner() {
            return owner;
        }

        Object contentMonitor() {
            return contentMonitor;
        }

        void bindPlannedReceiver(RuntimeTask task) {
            if (!requiresPlannedReceiver()
                    || plannedReceiverObjectId > 0L) {
                // One activation reads a carrier out once per snapshot and
                // holds more of its access anchors at each later one.  The
                // receiver identity must be the same in every snapshot of
                // one activation, so the first one that answers is kept.
                return;
            }
            long planned = task == null ? 0L
                    : task.plannedReceiverObjectId(declaringClass, fieldName,
                    consumerAccesses);
            // A per-instance receiver the plan never named still has one
            // replay-stable identity of its own: the access anchor this
            // carrier was selected on.  Naming it from that anchor keeps the
            // location joinable across sessions instead of refusing it.
            //
            // This used to exclude a map, on the ground that "a map's content
            // address stays on the frozen plan locator alone" -- but the
            // frozen locators are indexed out of inputActions
            // (ConcolicTaskPlan.indexPlannedReceiverObjectIds), so a location
            // the plan declares as a shared carrier and never reads as a
            // symbolic input has none, and a map was the one shape with no
            // second answer.  On 17960 that is exactly
            // DirectorySnapshottableFeature#snapshotsByNames, the bug's own
            // map and one of the four locations the slice keeps: it bound 0,
            // captureRecordedSharedStateRaw refused it, and no version of it
            // was read out at all.  The anchor identity is as replay-stable
            // for a map as for a scalar -- it is a static site, an
            // activation-local occurrence and the planned occurrence, none of
            // them an object id -- so the exclusion bought nothing and cost
            // the location.
            bindPlannedReceiver(planned > 0L ? planned
                    : accessAnchorReceiverObjectId(task == null ? ""
                    : task.occurrenceId));
        }

        /**
         * Tag distinguishing an anchor-derived receiver identity from the
         * plan's frozen locators, which are recorded trace object ids and so
         * never reach the high bits of a {@code long}.
         */
        private static final long ACCESS_ANCHOR_RECEIVER_TAG =
                1L << 62;

        /**
         * A replay-stable receiver identity built from this carrier's own
         * access anchor, inside the activation that selected it.
         *
         * <p>The smallest anchor is used rather than the first observed one
         * so that two sessions which read the same receiver at the same set
         * of sites name it alike whatever order the reads ran in.</p>
         *
         * <p>The anchor alone is not an identity.  One static access site
         * read once per activation names its receiver the same way in every
         * activation, so six calls of {@code PBHelper.convert(BlockKeyProto)}
         * -- six freshly allocated {@code BlockKey}s, each read at that one
         * site as its first occurrence -- collapsed onto a single receiver
         * id, and with it onto a single versioned location whose versions
         * came from six different objects.  A read could then take a value
         * one of the other five objects held.  The planned occurrence that
         * published this carrier is what separates them: it is the same
         * name in every replay of that occurrence, and different for each
         * of the six calls, so the identity stays joinable across sessions
         * and stops joining distinct allocations.</p>
         */
        private long accessAnchorReceiverObjectId(String occurrenceId) {
            String canonical = "";
            List<ConsumerAccessAnchor> naming = consumerAccesses.isEmpty()
                    && entryAnchor != null
                    ? Collections.singletonList(entryAnchor)
                    : consumerAccesses;
            for (ConsumerAccessAnchor access : naming) {
                if (access == null || access.siteId.isEmpty()
                        || access.occurrence < 1) {
                    continue;
                }
                String anchor = access.siteId + "\n" + access.occurrence;
                if (canonical.isEmpty() || anchor.compareTo(canonical) < 0) {
                    canonical = anchor;
                }
            }
            if (canonical.isEmpty()) return 0L;
            return ACCESS_ANCHOR_RECEIVER_TAG
                    | (stableHash(declaringClass + "#" + fieldName + ":"
                    + descriptor + "\n" + safe(occurrenceId) + "\n"
                    + canonical)
                    & (ACCESS_ANCHOR_RECEIVER_TAG - 1L));
        }

        /** FNV-1a over UTF-16 units: identical in every JVM and session. */
        private static long stableHash(String value) {
            long hash = 0xcbf29ce484222325L;
            for (int index = 0; index < value.length(); index++) {
                hash ^= value.charAt(index);
                hash *= 0x100000001b3L;
            }
            return hash;
        }

        void bindPlannedReceiver(long receiverObjectId) {
            plannedReceiverObjectId = Math.max(0L, receiverObjectId);
        }

        boolean requiresPlannedReceiver() {
            return !SHAPE_ELEMENT.equals(shape)
                    && !declaringClass.isEmpty() && !fieldName.isEmpty();
        }

        long plannedReceiverObjectId() {
            return plannedReceiverObjectId;
        }

        /**
         * Notes one read of this live carrier in the publishing activation.
         *
         * <p>A map is recorded like a scalar.  The anchor is a static access
         * site and an activation-local occurrence -- a fact about the read,
         * not about the shape of what was read -- and it is the only
         * replay-stable receiver identity available to a location the plan
         * froze no locator for.  Refusing to keep it for a map made
         * {@link #accessAnchorReceiverObjectId} unable to answer for exactly
         * the shape that had no other answer.</p>
         *
         * <p>An element carrier is still excluded: its identity is the array
         * and the index, and it does not go through the receiver rule at all
         * ({@link #requiresPlannedReceiver}).</p>
         */
        void recordConsumerAccess(ConsumerAccessAnchor consumer) {
            if (consumer != null && !SHAPE_ELEMENT.equals(shape)
                    && !consumer.siteId.isEmpty()
                    && consumer.occurrence > 0) {
                consumerAccesses.add(consumer);
            }
        }

        void recordEntryAnchor(ConsumerAccessAnchor entry) {
            if (entry != null && !SHAPE_ELEMENT.equals(shape)
                    && !entry.siteId.isEmpty() && entry.occurrence > 0
                    && entryAnchor == null) {
                entryAnchor = entry;
            }
        }

        List<ConsumerAccessAnchor> consumerAccesses() {
            return consumerAccesses;
        }

        String describe() {
            return shape + " " + declaringClass + "#" + fieldName + ":"
                    + descriptor;
        }

        /** Activation-local dedupe key; never a cross-run address. */
        String key() {
            return shape + "/" + System.identityHashCode(owner) + "/"
                    + declaringClass + "#" + fieldName + ":" + descriptor
                    + "@" + index;
        }

        JsonObject toJson() {
            JsonObject carrier = new JsonObject();
            carrier.addProperty("kind", SHAPE_ELEMENT.equals(shape)
                    ? "ARRAY_ELEMENT"
                    : SHAPE_MAP.equals(shape)
                    ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                    : "DECLARED_FIELD");
            carrier.addProperty("declaringClass", declaringClass);
            carrier.addProperty("fieldName", fieldName);
            carrier.addProperty("descriptor", descriptor);
            carrier.addProperty("index", index);
            // A replay-local object id is not a cross-session identity.  The
            // frozen causal edge's receiver locator is the one stable name
            // every worker in this campaign shares.
            carrier.addProperty("receiverObjectId",
                    plannedReceiverObjectId);
            if (!SHAPE_ELEMENT.equals(shape) && !declaringClass.isEmpty()
                    && !fieldName.isEmpty()) {
                carrier.addProperty("fieldKey",
                        declaringClass + "#" + fieldName + ":" + descriptor);
            }
            return carrier;
        }

        /** Native read-out only; JSON decoding belongs to publication. */
        String rawVersions(ConcolicVmBroker api) throws Exception {
            if (SHAPE_ELEMENT.equals(shape)) {
                return api.sharedElementVersions(owner, index);
            }
            if (SHAPE_MAP.equals(shape)) {
                return api.sharedMapVersions(owner);
            }
            return api.sharedFieldVersions(owner, declaringClass, fieldName,
                    descriptor);
        }
        /** Native selection only; the answer's meaning belongs to the caller. */
        long select(ConcolicVmBroker api) throws Exception {
            if (SHAPE_ELEMENT.equals(shape)) {
                return api.selectSharedElementCarrier(owner, index);
            }
            if (SHAPE_MAP.equals(shape)) {
                return api.selectSharedMapCarrier(owner);
            }
            return api.selectSharedFieldCarrier(owner, declaringClass,
                    fieldName, descriptor);
        }

        /** The VM entry point {@link #select} calls, named for a failure. */
        String selectApi() {
            return SHAPE_ELEMENT.equals(shape) ? "selectSharedElementCarrier"
                    : SHAPE_MAP.equals(shape) ? "selectSharedMapCarrier"
                    : "selectSharedFieldCarrier";
        }

        /** Why this shape cannot name a carrier, or empty when it can. */
        String missing() {
            if (SHAPE_MAP.equals(shape)) {
                // Two different absences, and only the first was tested.
                // readExactField answers MissingValue.INSTANCE when the field
                // is not declared on the object it was handed or the read
                // threw -- a sentinel, not null -- so that case passed this
                // test and was handed to selectSharedMapCarrier as though it
                // were the container.  Both are refusals, and the row says
                // which, because they call for different fixes: a null field
                // is a live container that does not exist yet, an unreadable
                // one is a receiver that never declared it.
                if (owner == MissingValue.INSTANCE) {
                    return "a map carrier needs the map it selects, and "
                            + "this receiver does not declare a readable "
                            + declaringClass + "#" + fieldName;
                }
                return owner == null
                        ? "a map carrier needs the map it selects, and this "
                        + "receiver held null in " + declaringClass + "#"
                        + fieldName : "";
            }
            if (SHAPE_ELEMENT.equals(shape)) {
                return owner == null || index < 0
                        ? "an element carrier needs an array and a "
                        + "non-negative index" : "";
            }
            return missingCarrierMetadata(owner, declaringClass, fieldName,
                    descriptor);
        }

    }

    private static String missingCarrierMetadata(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        if (owner == null) return "shared carrier has no owner";
        return firstNonBlank(declaringClass).isEmpty()
                || firstNonBlank(fieldName).isEmpty()
                || firstNonBlank(descriptor).isEmpty()
                ? "shared carrier has no exact declaring class, field name "
                + "and type descriptor" : "";
    }

    private static SharedStateResult failedShared(String stage, int status,
                                                  String locationKey,
                                                  String detail) {
        return new SharedStateResult(stage, status, safe(locationKey),
                SharedStateEvidence.gap(stage, status,
                        locationKey, detail));
    }

    /** Files one shared-state outcome with the active region. */
    private static SharedStateResult recordShared(SharedStateResult result,
                                                  SharedCarrier carrier,
                                                  ActiveRegion active) {
        fileShared(result, carrier, active);
        diag(result.ok() ? "SHARED_STATE" : SharedStateEvidence.GAP_KIND,
                result.toString());
        return result;
    }

    /** Files an already-decoded outcome without touching the closed VM. */
    private static void fileShared(SharedStateResult result,
                                   SharedCarrier carrier,
                                   ActiveRegion active) {
        if (active != null) {
            if (!result.ok()) {
                active.sharedStateGaps.add(result.record);
            } else if (carrier != null) {
                active.sharedCarriers.put(carrier.key(), carrier);
            } else if (!result.locationKey.isEmpty()) {
                active.sharedStateRecords.put(result.locationKey,
                        result.record);
            }
        }
    }

    /**
     * Captures every native shared-state envelope while the owner thread still
     * owns the VM context.
     */
    static RawSharedStateReadOut captureRecordedSharedStateRaw(
            ActiveRegion active, ConcolicVmBroker api,
            RecordedEvidenceIdentity identity) {
        List<RawSharedCarrierReadOut> carriers = new ArrayList<>();
        for (SharedCarrier carrier
                : new ArrayList<>(active.sharedCarriers.values())) {
            carrier.bindPlannedReceiver(active.activation);
            // Every field carrier needs one receiver identity: a map-state
            // expression to address its own content and a scalar read to be
            // named across replay sessions at all.  A carrier that has
            // neither a frozen plan locator nor an access anchor to build
            // one from cannot be named, and publishing it with a receiver of
            // 0 would silently drop it out of every cross-session family.
            if ((carrier.mapState() || carrier.requiresPlannedReceiver())
                    && carrier.plannedReceiverObjectId() <= 0L) {
                carriers.add(RawSharedCarrierReadOut.failure(carrier,
                        failedShared(SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.MISSING_METADATA, "",
                                "selected task has no frozen receiver"
                                        + " locator and no replay access"
                                        + " anchor for "
                                        + carrier.describe())));
                continue;
            }
            try {
                String serialized = memoizedReadOut(carrier.key());
                if (serialized == null) {
                    serialized = memoizeReadOut(carrier.key(),
                            carrier.rawVersions(api));
                }
                carriers.add(new RawSharedCarrierReadOut(carrier,
                        serialized, null));
            } catch (Throwable throwable) {
                carriers.add(RawSharedCarrierReadOut.failure(carrier,
                        failedShared(SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.INVOCATION_FAILED, "",
                                rootCause(throwable))));
            }
        }

        return new RawSharedStateReadOut(carriers, identity);
    }

    /** Decodes and files raw envelopes after the VM context is closed. */
    static void assembleRecordedSharedState(
            ActiveRegion active, RawSharedStateReadOut raw) {
        if (raw == null) return;
        for (RawSharedCarrierReadOut carrier : raw.carriers) {
            SharedStateResult decoded = carrier.failure;
            if (decoded == null) {
                try {
                    decoded = decodeVersionsEnvelope(carrier.serialized,
                            carrier.carrier, raw.identity, active);
                } catch (Throwable throwable) {
                    decoded = failedShared(
                            SharedStateEvidence.STAGE_VERSIONS,
                            SharedStateEvidence.MALFORMED_ENVELOPE, "",
                            rootCause(throwable));
                }
            }
            fileShared(decoded, null, active);
        }
    }

    /** One carrier's exact VM envelope, or the failure that replaced it. */
    private static final class RawSharedCarrierReadOut {
        private final SharedCarrier carrier;
        private final String serialized;
        private final SharedStateResult failure;

        private RawSharedCarrierReadOut(SharedCarrier carrier,
                                         String serialized,
                                         SharedStateResult failure) {
            this.carrier = carrier;
            this.serialized = serialized;
            this.failure = failure;
        }

        private static RawSharedCarrierReadOut failure(
                SharedCarrier carrier, SharedStateResult failure) {
            return new RawSharedCarrierReadOut(carrier, null, failure);
        }
    }

    /** Raw shared-state batch frozen before one VM region is finished. */
    static final class RawSharedStateReadOut {
        private final List<RawSharedCarrierReadOut> carriers;
        final RecordedEvidenceIdentity identity;

        private RawSharedStateReadOut(
                List<RawSharedCarrierReadOut> carriers,
                RecordedEvidenceIdentity identity) {
            this.carriers = carriers;
            this.identity = identity;
        }
    }
}
