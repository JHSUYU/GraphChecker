package edu.uva.liftlab.graphchecker.runtime;

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
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.WriterActivationIdentity;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import java.util.ArrayList;
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
import static edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.contextActivation;
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

    /** Selects one map as a symbolic carrier of its own whole state. */
    static SharedStateResult selectSharedMapCarrier(
            Object map, String declaringClass, String fieldName,
            String descriptor) {
        beginBookkeeping();
        try {
            return selectedCarrier(SharedCarrier.map(map, declaringClass,
                    fieldName, descriptor));
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
            // The VM addresses a location by its own session identity; the
            // slice and the composer address one by its declared Java field.
            record.add("carrier", carrier.toJson());
        }
        // Publication can run after the owner thread has left ACTIVE.
        addActivationIdentity(object(record, "envelope"), active, carrier);
        return new SharedStateResult(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.OK, locationKey, record);
    }

    /**
     * Gives every write and read in one envelope the activation address the
     * rest of the pipeline joins on.
     *
     * <p>The VM stamps writes and reads with their task, region and thread
     * context; reads additionally carry the exact region-entry event.</p>
     */
    private static void addActivationIdentity(JsonObject envelope,
                                              ActiveRegion active,
                                              SharedCarrier carrier) {
        ConcolicTaskPlan config = configuration();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            // Wave 3 concurrency: every symbolic write of the session is a
            // version the composer may read from, so each one is addressed
            // by the write that produced it and the thread that ran it.
            RuntimeTask writer = config.taskById(
                    optionalString(version, "taskId"));
            if (writer == null) continue;
            WriterActivationIdentity exact = contextActivation(
                    optionalLongInteger(version, "writerContextId", 0L),
                    optionalLongInteger(version, "regionEnterEventId", 0L), writer);
            if (exact != null && exact.owns(writer)) {
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                        exact.sourceKey);
                version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                        exact.occurrenceId);
                version.add(SymbolicPropagationClosure
                        .WRITER_ACTIVATION_CLOSURE, exact.caseClosure());
            } else {
                // A writer without its exact region-entry binding has no
                // activation owner. Leave it unnamed rather than collapsing
                // loop activations to their common planned address.
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY, "");
                version.addProperty(
                        SharedStateEvidence.WRITER_OCCURRENCE_ID, "");
            }
        }
        List<JsonObject> ownedReads = new ArrayList<>();
        for (JsonElement element : array(envelope, "reads")) {
            if (element.isJsonObject()
                    && activeOwnsRead(element.getAsJsonObject(), active)) {
                ownedReads.add(element.getAsJsonObject());
            }
        }
        ownedReads.sort(Comparator.comparingLong(
                read -> optionalLongInteger(read, "readEventId", Long.MAX_VALUE)));
        if (carrier != null
                && ownedReads.size() == carrier.consumerAccesses().size()) {
            for (int index = 0; index < ownedReads.size(); index++) {
                ConsumerAccessAnchor anchor =
                        carrier.consumerAccesses().get(index);
                ownedReads.get(index).addProperty(
                        SharedStateEvidence.CONSUMER_SITE_ID, anchor.siteId);
                ownedReads.get(index).addProperty(
                        SharedStateEvidence.CONSUMER_SITE_OCCURRENCE,
                        anchor.occurrence);
            }
        }
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            if (active == null) {
                read.addProperty(READER_AUTHORITY_FIELD,
                        READER_OUTSIDE_SELECTED_REGION);
                continue;
            }
            RuntimeTask reader = active.activation;
            // A session envelope contains reads from every task that touched
            // this location.  A row may claim only the reads issued by the
            // activation currently closing: native task, context and region
            // entry together are the exact dynamic owner.
            if (!activeOwnsRead(read, active)) {
                read.addProperty(READER_AUTHORITY_FIELD,
                        READER_FOREIGN_REGION);
                continue;
            }
            read.addProperty(SharedStateEvidence.READER_SOURCE_KEY,
                    reader.sourceKey);
            read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                    active.occurrenceId());
            read.addProperty(READER_AUTHORITY_FIELD,
                    READER_ACTIVE_REGION_AUTHORITY);
        }
    }

    /** Whether this native read belongs to the activation publishing it. */
    private static boolean activeOwnsRead(JsonObject read,
                                           ActiveRegion active) {
        if (read == null || active == null
                || active.vmRegionEnterEventId <= 0L) {
            return false;
        }
        RuntimeTask reader = active.activation;
        return active.vmContextId == optionalLongInteger(read,
                "readerContextId", 0L)
                && reader.taskId.equals(optionalString(read, "taskId"))
                && reader.regionId.equals(optionalString(read, "regionId"))
                && active.vmRegionEnterEventId == optionalLongInteger(read,
                "regionEnterEventId", 0L);
    }

    /** Member naming where one read's activation address came from. */
    static final String READER_AUTHORITY_FIELD = "readerAuthority";
    /** Authority of a reader address taken from the running activation. */
    static final String READER_ACTIVE_REGION_AUTHORITY =
            "ACTIVE_REGION_READER_IDENTITY_V1";
    /** Marker for a read read out while no selected region was running. */
    static final String READER_OUTSIDE_SELECTED_REGION =
            "READER_OUTSIDE_SELECTED_REGION";
    /** Marker for a read whose static region is not the running one. */
    static final String READER_FOREIGN_REGION =
            "READER_REGION_NOT_ACTIVE_ACTIVATION";

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
                    readExactField(owner, fieldSignature),
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
            if (mapState) {
                return selectCarrierForTask(SharedCarrier.map(owner,
                        declaringClass, fieldName, descriptor), task);
            }
            return selectCarrierForTask(SharedCarrier.field(owner,
                    declaringClass, fieldName, descriptor), task);
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
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final int index;
        private final String shape;
        /** Frozen trace locator from this task's selected causal edge. */
        private long plannedReceiverObjectId;
        /** Reads of this live carrier in the publishing activation. */
        private final List<ConsumerAccessAnchor> consumerAccesses =
                new ArrayList<>();

        private SharedCarrier(Object owner, String declaringClass,
                              String fieldName, String descriptor, int index,
                              String shape) {
            this.owner = owner;
            this.declaringClass = declaringClass;
            this.fieldName = fieldName;
            this.descriptor = descriptor;
            this.index = index;
            this.shape = shape;
        }

        static SharedCarrier field(Object owner, String declaringClass,
                                   String fieldName, String descriptor) {
            return new SharedCarrier(owner, safe(declaringClass),
                    safe(fieldName), safe(descriptor), -1, SHAPE_FIELD);
        }

        static SharedCarrier element(Object array, int index) {
            return new SharedCarrier(array, "", "", "", index, SHAPE_ELEMENT);
        }

        /** One map selected as the carrier of its own whole state. */
        static SharedCarrier map(Object map, String declaringClass,
                                 String fieldName, String descriptor) {
            return new SharedCarrier(map, safe(declaringClass),
                    safe(fieldName), safe(descriptor), -1, SHAPE_MAP);
        }

        boolean mapState() {
            return SHAPE_MAP.equals(shape);
        }

        void bindPlannedReceiver(RuntimeTask task) {
            if (!requiresPlannedReceiver()) {
                return;
            }
            long planned = task == null ? 0L
                    : task.plannedReceiverObjectId(declaringClass, fieldName,
                    consumerAccesses);
            // A per-instance receiver the plan never named still has one
            // replay-stable identity of its own: the access anchor this
            // carrier was selected on.  Naming it from that anchor keeps the
            // location joinable across sessions instead of refusing it,
            // while a map's content address stays on the frozen plan
            // locator alone.
            bindPlannedReceiver(planned > 0L || mapState() ? planned
                    : accessAnchorReceiverObjectId());
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
         * access anchor.
         *
         * <p>The smallest anchor is used rather than the first observed one
         * so that two sessions which read the same receiver at the same set
         * of sites name it alike whatever order the reads ran in.</p>
         */
        private long accessAnchorReceiverObjectId() {
            String canonical = "";
            for (ConsumerAccessAnchor access : consumerAccesses) {
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
                    + descriptor + "\n" + canonical)
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

        void recordConsumerAccess(ConsumerAccessAnchor consumer) {
            if (consumer != null && SHAPE_FIELD.equals(shape)
                    && !consumer.siteId.isEmpty()
                    && consumer.occurrence > 0) {
                consumerAccesses.add(consumer);
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
                return owner == null
                        ? "a map carrier needs the map it selects" : "";
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
