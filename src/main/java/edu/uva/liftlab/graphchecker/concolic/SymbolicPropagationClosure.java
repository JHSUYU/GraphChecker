package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OccurrenceId;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.TreeMap;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Closes receiver-owned symbolic values before SMT lowering.
 *
 * <p>The VM has already propagated each value through ordinary Java
 * operations. It leaves a transparent {@code ConsumerBoundaryExpression} at
 * every RPC attach and shared-state read. This pass gives those dynamic
 * observations a replay-independent family identity and merges the payloads
 * observed for that family. It never recovers a value from a graph edge,
 * output port, or producer capture.</p>
 *
 * <p>A written arm is selected by the exact producer case named by runtime
 * evidence, so its selector implies that case's PC through normal relation
 * lowering. An INITIAL arm names the pre-write source value and therefore
 * uses a content-addressed source case with the empty PC. Nested boundary
 * references are resolved recursively, so an A<-B<-C chain contains two
 * shared merge nodes instead of a product of B and C cases.</p>
 */
public final class SymbolicPropagationClosure {
    public static final int SCHEMA_VERSION = 2;
    public static final String ITE_TYPE = "CaseMergeExpression";
    /** A physical replay refines a local case only when its propagated
     *  evidence cannot be folded into the case's replay-independent value. */
    public static final String OBSERVATION_SELECTOR =
            "replayObservationSelector";
    public static final String OBSERVATION_SCOPE =
            "replayObservationScope";
    public static final String DEPENDENCY_KIND =
            "CONSUMER_BOUNDARY_CASE_DEPENDENCY";
    /** Stable producer-case join carried by a ReadFrom candidate. */
    public static final String WRITER_CASE_FAMILY =
            "writerCaseFamilyKey";
    public static final String WRITER_CASE_OWNER = "writerCaseOwner";
    public static final String WRITER_CASE_SELECTOR = "writerCaseSelector";
    public static final String WRITER_CASE_REGION_ID = "writerCaseRegionId";
    public static final String WRITER_CASE_OCCURRENCE_ID =
            "writerCaseOccurrenceId";
    /**
     * Exact selected-region stack captured when a physical writer region was
     * entered. Runtime entries carry task/region/occurrence addresses; this
     * pass resolves them to replay-independent local cases.
     */
    public static final String WRITER_ACTIVATION_CLOSURE =
            "writerActivationClosure";
    public static final String WRITER_ACTIVATION_CLOSURE_AUTHORITY =
            "ACTIVE_REGION_STACK_AT_WRITER_ENTRY_V1";
    /** Stable local cases which physically enclosed one writer event. */
    public static final String WRITER_CASE_CLOSURE = "writerCaseClosure";
    /** Replay-independent identity of one arm in a guarded read. */
    public static final String READ_CANDIDATE_IDENTITY =
            "readCandidateIdentity";
    /**
     * Stable identity of one recorded read choice.  VM event ids are local to
     * a replay, so path queries must never join a guarded expression to a cut
     * by the bare numeric id.
     */
    /**
     * Cases one shared read may be consumed by before the closure stops
     * naming it.  A read every case in a wave consumes is a sign the
     * boundary address is wrong, not a value worth a family.
     */
    private static final int MAX_BOUNDARY_CONSUMERS = 32;

    public static final String READ_CHOICE_IDENTITY = "readChoiceIdentity";
    public static final String READ_CHOICE_OWNER = "readChoiceOwner";
    public static final String READ_CHOICE_OCCURRENCE_ID =
            "readChoiceOccurrenceId";
    /** Dependency rows with this policy are enabled by an RF arm. */
    public static final String READ_FROM_DEPENDENCY_POLICY =
            "READ_FROM_ARM_IMPLIES_CASE";
    /** An INITIAL version is an observed source value, not a region write. */
    /**
     * A whole-state carrier whose INITIAL version stayed opaque, so its
     * initial membership is a free container const rather than content.
     */
    public static final String INITIAL_CONTAINER_SNAPSHOT_TRUNCATED =
            "INITIAL_CONTAINER_SNAPSHOT_TRUNCATED";
    /**
     * One RPC attach whose sender-side expression did not reach the join.
     *
     * <p>Raised where a referenced attach family carries no usable payload
     * arm at all, and where its only payload observation was truncated.
     * Named apart from the field-read cases because the two have different
     * causes and different fixes: a field read with no writer case is an
     * incomplete read-from snapshot, while an attach with no payload means
     * the value the wire carried never reached the join, so the receiver's
     * leaf is left equal to nothing.</p>
     */
    public static final String RPC_ATTACH_SENDER_EXPRESSION_MISSING =
            "RPC_ATTACH_SENDER_EXPRESSION_MISSING";
    /**
     * How many wires a resolved boundary sits behind the fatal cone.
     *
     * <p>Zero is a boundary the target reads directly. One is a boundary that
     * arrived inside another boundary's payload -- the client's cached key
     * inside what the client then sent on -- and so on, because NN to client
     * to DN is one chain and the walk follows it.</p>
     */
    public static final String BOUNDARY_DEPTH = "boundaryDepth";
    public static final String INITIAL_SOURCE_CASE_PREFIX =
            "INITIAL_SOURCE.";
    public static final String GAP_KIND = "SYMBOLIC_PROPAGATION_GAP";
    public static final String GAP_AUTHORITY =
            "CONSUMER_BOUNDARY_CLOSURE_V1";

    private SymbolicPropagationClosure() {
    }

    /** Stable identity shape of a source case created from an INITIAL value. */
    static boolean isInitialSourceCase(String owner, String region,
                                       String occurrence) {
        return owner != null && owner.equals(occurrence)
                && hasInitialSourceDigest(owner)
                && hasInitialSourceDigest(region);
    }

    private static boolean hasInitialSourceDigest(String value) {
        if (value == null || !value.startsWith(INITIAL_SOURCE_CASE_PREFIX)
                || value.length() != INITIAL_SOURCE_CASE_PREFIX.length()
                + 64) {
            return false;
        }
        for (int index = INITIAL_SOURCE_CASE_PREFIX.length();
             index < value.length(); index++) {
            char digit = value.charAt(index);
            if (!((digit >= '0' && digit <= '9')
                    || (digit >= 'a' && digit <= 'f'))) return false;
        }
        return true;
    }

    /**
     * The stable family key one consumer boundary carries.
     *
     * <p>A boundary is addressed by the planned occurrence that consumed it,
     * within its topology epoch, by kind, by the slot the kind names -- a
     * port for an RPC attach, a replay-stable location for a field read --
     * and by which occurrence of that slot this is.  Both the importer, which
     * stamps RPC boundaries as it admits a result, and this closure, which
     * addresses field reads, key on the same five parts in the same order.
     * </p>
     *
     * <p>The topology epoch is the campaign's refinement iteration
     * ({@code iteration-NNNN}), and it stays in the key on purpose.  It is
     * not a per-run counter: the refinement loop is deterministic, so two
     * campaigns over one obligation walk the same iterations and mint the
     * same epochs.  It is also load-bearing, because the epoch is what the
     * family is addressed <em>within</em>: the same planned occurrence
     * consuming the same slot is a different obligation once refinement has
     * changed the topology around it, and dropping the epoch would join two
     * families that were never the same one.  Every other component here is
     * already content-addressed, and this key reaches no published plan row;
     * it names boundary families inside the importer and the closure.</p>
     */
    public static String boundaryFamilyKey(String topologyEpoch,
                                           String plannedOccurrenceId,
                                           String boundaryKind, String slot,
                                           int ordinal) {
        return "CBF." + CanonicalJson.sha256(topologyEpoch + "\n"
                + plannedOccurrenceId + "\n" + boundaryKind + "\n" + slot
                + "\n" + ordinal);
    }

    public static Result rewrite(
            Collection<RelationSummary> selectedSummaries,
            JsonObject fatal,
            Collection<JsonObject> caseRows) {
        return new Resolver(selectedSummaries, caseRows).rewrite(fatal);
    }

    /** Shared entry point for final composition and linked path flipping. */
    public static Result rewrite(
            Collection<RelationSummary> closureSummaries,
            JsonObject fatal) {
        return rewrite(closureSummaries, fatal,
                caseRows(closureSummaries, fatal));
    }

    /** JSON carrier used by the linked-replay planner. */
    public static Result rewriteSummaryRows(
            Collection<JsonObject> closureSummaryRows) {
        return new Resolver(closureSummaryRows).rewrite(new JsonObject());
    }

    public static final class Result {
        private final boolean complete;
        private final JsonObject fatal;
        private final List<JsonObject> summaries;
        private final List<JsonObject> dependencies;
        private final List<JsonObject> gaps;

        private Result(boolean complete, JsonObject fatal,
                       List<JsonObject> summaries,
                       List<JsonObject> dependencies,
                       List<JsonObject> gaps) {
            this.complete = complete;
            this.fatal = fatal;
            this.summaries = summaries;
            this.dependencies = dependencies;
            this.gaps = gaps;
        }

        public boolean complete() { return complete; }
        public JsonObject fatal() { return fatal; }
        public List<JsonObject> summaries() {
            return Collections.unmodifiableList(new ArrayList<>(summaries));
        }
        public JsonArray caseDependencies() { return jsonRows(dependencies); }
        public JsonArray gaps() { return jsonRows(gaps); }

        private static JsonArray jsonRows(Collection<JsonObject> source) {
            JsonArray result = new JsonArray();
            for (JsonObject row : source) result.add(row);
            return result;
        }
    }

    private static final class Resolver {
        private final List<JsonObject> inputSummaryRows = new ArrayList<>();
        private final Map<String, CaseInfo> casesByOwner =
                new LinkedHashMap<>();
        /** All execution observations which realized one local case. */
        private final Map<String, List<CaseInfo>> caseObservationsByOwner =
                new LinkedHashMap<>();
        private final Map<String, List<CaseInfo>> casesByExecution =
                new LinkedHashMap<>();
        /** Consuming cases of one shared read, for provenance only. */
        private final Map<String, List<String>> boundaryConsumers =
                new LinkedHashMap<>();
        private final Map<DynamicKey, String> dynamicFamilies =
                new LinkedHashMap<>();
        /** Boundary kind of every family the evidence named. */
        /** How deep in the chain each family was first reached. */
        private final Map<String, Integer> depthByFamily =
                new LinkedHashMap<>();
        private int chainDepth;
        /** Families a resolve-time or payload gap already named once. */
        private final Set<String> namedEmptyFamilies = new LinkedHashSet<>();
        /** Declared wire port and receiving occurrence, per attach family. */
        private final Map<String, String> familyPorts =
                new LinkedHashMap<>();
        private final Map<String, String> familyReceivers =
                new LinkedHashMap<>();
        private final Map<String, String> familyKinds =
                new LinkedHashMap<>();
        /** One immutable payload observation per VM boundary event. */
        private final Map<DynamicKey, ArmLineage> dynamicArmLineages =
                new LinkedHashMap<>();
        private final Map<DynamicKey, Arm> dynamicArms =
                new LinkedHashMap<>();
        /** Events seen only through a lossy serialization copy. */
        private final Map<DynamicKey, String> truncatedDynamicArms =
                new LinkedHashMap<>();
        /** Exact field-read lineage, indexed before any payload is scanned. */
        private final Map<DynamicKey, FieldRead> fieldReads =
                new LinkedHashMap<>();
        /** Exact version metadata used to recover each RF arm's local case. */
        private final Map<ReadCandidateKey, JsonObject> readCandidateVersions =
                new LinkedHashMap<>();
        private final Set<ReadCandidateKey> ambiguousReadCandidateVersions =
                new LinkedHashSet<>();
        /** Writer versions addressed by the VM location every snapshot of
         *  that location shares inside one replay session. */
        private final Map<LocationVersionKey, JsonObject> locationVersions =
                new LinkedHashMap<>();
        private final Set<LocationVersionKey> ambiguousLocationVersions =
                new LinkedHashSet<>();
        /** Producer cases referenced by RF arms, grouped by occurrence. */
        private final Map<String, Map<String, CaseInfo>> readFromWriterCases =
                new LinkedHashMap<>();
        /** Dynamic boundary event -> the case that owns its VM evidence. */
        private final Map<DynamicKey, CaseInfo> boundaryOwners =
                new LinkedHashMap<>();
        private final Set<DynamicKey> ambiguousBoundaryOwners =
                new LinkedHashSet<>();
        private final Map<String, Family> families = new LinkedHashMap<>();
        private final Map<String, JsonElement> resolved =
                new LinkedHashMap<>();
        private final Set<String> active = new LinkedHashSet<>();
        private final Map<String, JsonObject> dependencies =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> gaps = new LinkedHashMap<>();
        /** One closed PC per stable local-case owner. */
        private final Map<String, JsonElement> closedPathConditions =
                new LinkedHashMap<>();
        private final Set<String> missingPathConditions =
                new LinkedHashSet<>();
        /** Owners whose PC or propagated value retains physical replays. */
        private final Set<String> observationOwners =
                new LinkedHashSet<>();
        private final Map<JsonElement, Map<String, JsonElement>> rewritten =
                new IdentityHashMap<>();
        private final Map<JsonElement, Map<String, String>> semanticIdentities =
                new IdentityHashMap<>();
        /**
         * Boundary payload nodes the arm scan has entered, per session scope.
         *
         * <p>A propagated value is a shared DAG, and a boundary shell occurs in
         * thousands of downstream copies, so the former descent re-entered the
         * same node once per referencing edge and once per row that carried it.
         * Re-entering one node under one scope can only repeat what the first
         * entry already did: a gap is keyed by its rendered row, an arm by its
         * dynamic event, and both ignore a second identical claim. Recording
         * the entry therefore drops the repetition and not its effect.</p>
         */
        private final Map<JsonElement, Set<String>> scannedBoundaries =
                new IdentityHashMap<>();
        /**
         * Subtree digests that no allocated-reference alpha name reached.
         *
         * <p>Summary rows share one propagated expression DAG, so every root
         * hashed here re-descends the same upstream history. A subtree that
         * never consults the per-root oop naming table hashes to a pure
         * function of its node and owner, so it is hashed once for the whole
         * closure instead of once per root. Subtrees that do consult that
         * table stay private to their root, where the naming order that
         * produced them still holds.</p>
         */
        private final Map<JsonElement, Map<String, String>> stableIdentities =
                new IdentityHashMap<>();
        /** The same, for arms hashed as ordinary objects by a case merge. */
        private final Map<JsonElement, Map<String, String>> stableArms =
                new IdentityHashMap<>();

        private Resolver(Collection<RelationSummary> summaries,
                         Collection<JsonObject> caseRows) {
            if (summaries != null) {
                for (RelationSummary summary : summaries) {
                    if (summary == null) continue;
                    inputSummaryRows.add(summary.immutableJson());
                    indexSummaryCases(summary);
                }
            }
            index(caseRows);
        }

        /** Direct raw-summary constructor used by linked replay. */
        private Resolver(Collection<JsonObject> rawSummaries) {
            List<JsonObject> caseRows = new ArrayList<>();
            for (JsonObject expanded : SharedExpressionTable.expandAll(
                    rawSummaries)) {
                RelationSummary decoded =
                        RelationSummary.decodeExpanded(expanded);
                JsonObject summary = decoded.immutableJson();
                inputSummaryRows.add(summary);
                JsonObject oneCase = rawCase(decoded);
                caseRows.add(oneCase);
            }
            index(caseRows);
        }

        /**
         * The one indexing pass both constructors run: cases first, then the
         * boundary evidence they own, then the payloads that name it, then
         * the reads no snapshot addressed.
         */
        private void index(Collection<JsonObject> caseRows) {
            List<JsonObject> indexedRows = shallowCopies(caseRows);
            for (JsonObject row : indexedRows) indexCaseRow(row);
            for (JsonObject row : indexedRows) indexBoundaryEvidence(row);
            for (JsonObject row : indexedRows) scanFieldBoundaries(row);
            claimUnsnapshottedFieldReads(indexedRows);
            validateDynamicArms();
        }

        private static List<JsonObject> shallowCopies(
                Collection<JsonObject> rows) {
            List<JsonObject> copies = new ArrayList<>();
            if (rows == null) return copies;
            for (JsonObject row : rows) {
                if (row == null) continue;
                copies.add(JsonFields.shallowCopy(row));
            }
            return copies;
        }

        private JsonObject rawCase(RelationSummary decoded) {
            JsonObject summary = decoded.immutableJson();
            JsonObject row = decoded.pathCaseView();
            annotateCase(summary, row, 0);
            return row;
        }

        private void annotateCase(JsonObject summary, JsonObject row,
                                  int index) {
            String occurrence = first(optionalString(row, "occurrenceId"),
                    optionalString(summary, "occurrenceId"));
            String region = optionalString(summary, "regionId");
            row.addProperty("occurrenceId", occurrence);
            row.addProperty("toOccurrenceId", occurrence);
            row.addProperty("regionId", region);
            row.addProperty("caseRegionId", region);
            row.addProperty("taskId", first(optionalString(row, "taskId"),
                    first(optionalString(row, "sourceTaskId"),
                            optionalString(summary, "taskId"))));
            row.addProperty("boundarySessionScope", first(
                    optionalString(row, "boundarySessionScope"),
                    optionalString(summary, "boundarySessionScope")));
            row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                    first(optionalString(row, VmExpressionIr.TOPOLOGY_EPOCH),
                            optionalString(summary, VmExpressionIr.TOPOLOGY_EPOCH)));
            String caseId = first(optionalString(row, "caseId"),
                    optionalString(summary, LocalCaseIdentity.FIELD));
            String owner = LocalCaseIdentity.owner(region, occurrence,
                    caseId, index);
            LocalCaseIdentity.stamp(row, owner);
        }

        private void indexSummaryCases(RelationSummary summary) {
            JsonObject row = summary.pathCaseView();
            JsonObject summaryRow = summary.immutableJson();
            String occurrence = optionalString(row, "occurrenceId");
            String owner = LocalCaseIdentity.owner(summaryRow);
            CaseInfo info = new CaseInfo(owner,
                    LocalCaseIdentity.selector(owner),
                    summary.regionId(), occurrence,
                    first(optionalString(row, "taskId"),
                            first(optionalString(row, "sourceTaskId"),
                                    optionalString(summaryRow, "taskId"))),
                    first(optionalString(row, "boundarySessionScope"),
                            optionalString(summaryRow,
                                    "boundarySessionScope")),
                    first(optionalString(row, VmExpressionIr.TOPOLOGY_EPOCH),
                            optionalString(summaryRow,
                                    VmExpressionIr.TOPOLOGY_EPOCH)),
                    object(row, "guard").get("conditions"));
            putCase(info);
        }

        private void indexCaseRow(JsonObject row) {
            if (row == null) return;
            String owner = optionalString(row, LocalCaseIdentity.OWNER);
            // Stamped by this class, a few statements above: the selector is
            // a pure function of the owner and is not rechecked here.
            String selector = optionalString(row, LocalCaseIdentity.SELECTOR);
            if (owner.isEmpty() || selector.isEmpty()) {
                gap("CASE_CLOSURE_IDENTITY_MISSING", owner,
                        "case row has no exact owner/selector identity");
                return;
            }
            CaseInfo held = casesByOwner.get(owner);
            CaseInfo info = new CaseInfo(owner, selector,
                    first(optionalString(row, "regionId"),
                            optionalString(row, "caseRegionId")),
                    first(optionalString(row, "toOccurrenceId"),
                            optionalString(row, "occurrenceId")),
                    first(optionalString(row, "taskId"),
                            optionalString(row, "sourceTaskId")),
                    optionalString(row, "boundarySessionScope"),
                    first(optionalString(row, VmExpressionIr.TOPOLOGY_EPOCH),
                            held == null ? "" : held.epoch),
                    object(row, "guard").get("conditions"));
            putCase(info);
        }

        private void putCase(CaseInfo info) {
            CaseInfo prior = casesByOwner.putIfAbsent(info.owner, info);
            if (prior != null && !prior.sameLocalIdentity(info)) {
                gap("CASE_CLOSURE_IDENTITY_AMBIGUOUS", info.owner,
                        "two local control cases claim one case owner");
                return;
            }
            List<CaseInfo> observations = caseObservationsByOwner
                    .computeIfAbsent(info.owner,
                            ignored -> new ArrayList<>());
            boolean heldObservation = false;
            for (CaseInfo observation : observations) {
                if (observation.sameExecution(info)) {
                    heldObservation = true;
                    break;
                }
            }
            if (!heldObservation) observations.add(info);
            String key = executionKey(info.sessionScope, info.task,
                    info.occurrence);
            List<CaseInfo> values = casesByExecution.computeIfAbsent(key,
                    ignored -> new ArrayList<>());
            for (CaseInfo value : values) {
                if (value.owner.equals(info.owner)) return;
            }
            values.add(info);
        }

        /** Exact execution observation which owns one case evidence row. */
        private CaseInfo caseForRow(JsonObject row) {
            String owner = optionalString(row, LocalCaseIdentity.OWNER);
            String occurrence = first(optionalString(row, "toOccurrenceId"),
                    optionalString(row, "occurrenceId"));
            String task = first(optionalString(row, "taskId"),
                    optionalString(row, "sourceTaskId"));
            String scope = optionalString(row, "boundarySessionScope");
            for (CaseInfo candidate : casesByExecution.getOrDefault(
                    executionKey(scope, task, occurrence),
                    Collections.emptyList())) {
                if (candidate.owner.equals(owner)) return candidate;
            }
            return null;
        }

        private CaseInfo caseForSummary(JsonObject row) {
            if (row == null) return null;
            String owner;
            try {
                owner = LocalCaseIdentity.owner(row);
            } catch (IllegalArgumentException ignored) {
                return null;
            }
            String key = executionKey(optionalString(row, "boundarySessionScope"),
                    first(optionalString(row, "taskId"),
                            optionalString(row, "sourceTaskId")),
                    optionalString(row, "occurrenceId"));
            for (CaseInfo candidate : casesByExecution.getOrDefault(key,
                    Collections.emptyList())) {
                if (candidate.owner.equals(owner)) return candidate;
            }
            return null;
        }

        private void indexBoundaryEvidence(JsonObject row) {
            if (row == null) return;
            String scope = optionalString(row, "boundarySessionScope");
            String epoch = optionalString(row, VmExpressionIr.TOPOLOGY_EPOCH);
            CaseInfo receiver = caseForRow(row);
            for (JsonObject event : VmHandoffEvidence.eventsOf(row)) {
                indexRpcBoundary(event, scope, epoch, receiver);
            }
            indexFieldReadEvidence(row, scope, epoch, receiver);
        }

        private static boolean sameJavaType(String left, String right) {
            return !left.isEmpty() && !right.isEmpty()
                    && JavaPrimitiveSmtSemantics.javaTypeDescriptor(left)
                    .equals(JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                            right));
        }

        private void scanFieldBoundaries(JsonObject row) {
            if (row == null || fieldReads.isEmpty()) return;
            scanFieldBoundaryPayloads(row,
                    optionalString(row, "boundarySessionScope"));
        }

        private void indexRpcBoundary(JsonObject event, String rowScope,
                                      String rowEpoch,
                                      CaseInfo receiverCase) {
            String familyKey = optionalString(event,
                    VmHandoffEvidence.BOUNDARY_FAMILY_KEY);
            String scope = first(optionalString(event, "boundarySessionScope"),
                    rowScope);
            String epoch = first(optionalString(event,
                    VmHandoffEvidence.TOPOLOGY_EPOCH), rowEpoch);
            long eventId = optionalLongInteger(event,
                    VmHandoffEvidence.ATTACH_EVENT_ID, -1L);
            JsonElement encoded = event.get(VmHandoffEvidence.EXPRESSION);
            String fault = boundaryFault(encoded,
                    VmExpressionIr.RPC_ATTACH, eventId);
            if (familyKey.isEmpty() || scope.isEmpty() || epoch.isEmpty()
                    || !fault.isEmpty()) {
                gap("RPC_CONSUMER_BOUNDARY_MALFORMED",
                        familyKey, fault.isEmpty()
                                ? "stable family/session/epoch is missing"
                                : fault);
                return;
            }
            if (!addDynamic(scope, eventId, familyKey)) return;
            // The kind is known from the evidence even when no arm lands, and
            // a family that never gets one is exactly the case whose gap has
            // to say which kind of boundary was left open.
            familyKinds.putIfAbsent(familyKey, VmExpressionIr.RPC_ATTACH);
            String declaredPort = optionalString(event, "portId");
            if (!declaredPort.isEmpty()) {
                familyPorts.putIfAbsent(familyKey, declaredPort);
            }
            String declaredReceiver = optionalString(event,
                    "consumerOccurrenceId");
            if (!declaredReceiver.isEmpty()) {
                familyReceivers.putIfAbsent(familyKey, declaredReceiver);
            }
            DynamicKey dynamic = new DynamicKey(scope, eventId);
            indexBoundaryOwner(dynamic, receiverCase, familyKey);
            CaseInfo producer = uniqueProducerCase(scope, optionalString(event,
                    VmHandoffEvidence.PRODUCER_TASK_ID), optionalString(event,
                    VmHandoffEvidence.PRODUCER_OCCURRENCE_ID), familyKey);
            JsonElement payload = encoded.getAsJsonObject().get(
                    VmExpressionIr.EXPRESSION);
            addArm(familyKey, VmExpressionIr.RPC_ATTACH, epoch, scope,
                    producer, receiverCase == null ? ""
                            : receiverCase.owner, payload,
                    optionalString(encoded.getAsJsonObject(), "_java_type"), eventId);
        }

        private void indexFieldReadEvidence(JsonObject row, String scope,
                                            String epoch,
                                            CaseInfo readerCase) {
            JsonObject recorded = object(row,
                    SharedStateEvidence.RECORDED_FIELD);
            String receiverOwner = readerCase == null ? ""
                    : readerCase.owner;
            Map<String, Integer> ordinals = new LinkedHashMap<>();
            for (JsonElement encoded : array(recorded, "versions")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject record = encoded.getAsJsonObject();
                JsonObject envelope = object(record, "envelope");
                String envelopeFault = SharedStateEvidence.versionsFault(
                        envelope);
                boolean complete = envelopeFault.isEmpty()
                        && SharedStateEvidence.writerSetComplete(envelope)
                        && !SharedStateEvidence.readLogTruncated(envelope);
                if (!complete) {
                    gap("READ_FROM_SNAPSHOT_INCOMPLETE",
                            optionalString(record, "locationKey"),
                            envelopeFault.isEmpty()
                                    ? "read-time writer/read retention is open"
                                    : envelopeFault);
                }
                // A snapshot is a session-wide view of one VM location, so
                // its retained writer versions name the same writes for any
                // read of that location in this replay session.
                String snapshotLocation = SharedStateEvidence.locationKey(
                        envelope);
                for (JsonElement versionElement : array(envelope,
                        "versions")) {
                    if (!versionElement.isJsonObject()) continue;
                    JsonObject version = versionElement.getAsJsonObject();
                    putLocationVersion(new LocationVersionKey(scope,
                                    snapshotLocation,
                                    optionalLongInteger(version,
                                            "fieldVersionId", -1L)),
                            version);
                }
                for (JsonElement readElement : array(envelope, "reads")) {
                    if (!readElement.isJsonObject()) continue;
                    JsonObject read = readElement.getAsJsonObject();
                    String readerOccurrence = optionalString(read,
                            SharedStateEvidence.READER_OCCURRENCE_ID);
                    // A VM version-store snapshot is session-wide. It can
                    // therefore repeat reads owned by outer, inner, or prior
                    // activations. Only the case named by the read's exact
                    // activation identity may claim it. In particular, an
                    // empty/foreign reader identity must not inherit this
                    // summary row's planned occurrence.
                    if (readerCase == null || readerCase.task.isEmpty()
                            || !scope.equals(readerCase.sessionScope)
                            || !readerCase.occurrence.equals(
                            readerOccurrence)) {
                        continue;
                    }
                    long eventId = optionalLongInteger(read, "readEventId", -1L);
                    String location = stableReadLocation(record, read,
                            readerCase);
                    // A session-local VM owner is not a replay identity. If
                    // neither a unique frozen receiver nor the runtime
                    // consumer site names this read, it has no replay-stable
                    // address: say so rather than dropping the claimed read
                    // and leaving the boundary to be addressed by something
                    // else.
                    if (location.isEmpty()) {
                        gap("CONSUMER_BOUNDARY_LOCATION_UNSTABLE",
                                optionalString(record, "locationKey"),
                                "a claimed read has no replay-stable"
                                        + " location");
                        continue;
                    }
                    int ordinal = ordinals.merge(location, 1, Integer::sum);
                    String family = boundaryFamilyKey(epoch,
                            OccurrenceId.parse(readerOccurrence).planned(),
                            VmExpressionIr.FIELD_READ, location, ordinal);
                    if (!addDynamic(scope, eventId, family)) continue;
                    DynamicKey dynamic = new DynamicKey(scope, eventId);
                    indexBoundaryOwner(dynamic, readerCase, family);
                    JsonArray retainedWriters = array(envelope, "versions");
                    for (JsonElement versionElement : retainedWriters) {
                        if (!versionElement.isJsonObject()) continue;
                        JsonObject version = versionElement.getAsJsonObject();
                        putReadCandidateVersion(new ReadCandidateKey(
                                        scope, eventId,
                                        optionalLongInteger(version,
                                                "fieldVersionId", -1L)),
                                version);
                    }
                    putFieldRead(new DynamicKey(scope, eventId),
                            new FieldRead(family, readerCase, receiverOwner,
                                    scope, epoch,
                                    // The envelope is session-wide; this row
                                    // records the exact read-time snapshot.
                                    optionalInteger(read, "candidateCount", -1),
                                    location,
                                    object(record, "carrier"), read));
                }
            }
        }

        private void putReadCandidateVersion(ReadCandidateKey key,
                                             JsonObject version) {
            if (key.readEvent <= 0L || key.version <= 0L
                    || version == null
                    || ambiguousReadCandidateVersions.contains(key)) {
                return;
            }
            JsonObject held = readCandidateVersions.putIfAbsent(key, version);
            if (held != null && !sameWriterCaseIdentity(held, version)) {
                readCandidateVersions.remove(key);
                ambiguousReadCandidateVersions.add(key);
                gap("READ_FROM_WRITER_VERSION_AMBIGUOUS", key.toString(),
                        "one guarded read candidate names two writer"
                                + " activation identities");
            }
        }

        private boolean sameWriterCaseIdentity(JsonObject left,
                                               JsonObject right) {
            return optionalString(left, "taskId").equals(optionalString(right, "taskId"))
                    && optionalString(left, "regionId").equals(
                    optionalString(right, "regionId"))
                    && optionalString(left, SharedStateEvidence.WRITER_OCCURRENCE_ID)
                    .equals(optionalString(right,
                            SharedStateEvidence.WRITER_OCCURRENCE_ID))
                    && optionalString(left, SharedStateEvidence.WRITER_SOURCE_KEY)
                    .equals(optionalString(right,
                            SharedStateEvidence.WRITER_SOURCE_KEY))
                    && optionalString(left, "versionKind").equals(
                    optionalString(right, "versionKind"))
                    && semanticIdentity(left.get("expression"), "").equals(
                    semanticIdentity(right.get("expression"), ""))
                    && semanticIdentity(left.get("pathGuard"), "").equals(
                    semanticIdentity(right.get("pathGuard"), ""))
                    && semanticIdentity(left.get(WRITER_ACTIVATION_CLOSURE),
                    "").equals(semanticIdentity(
                    right.get(WRITER_ACTIVATION_CLOSURE), ""));
        }

        private void putLocationVersion(LocationVersionKey key,
                                        JsonObject version) {
            if (key.location.isEmpty() || key.version <= 0L
                    || version == null
                    || ambiguousLocationVersions.contains(key)) {
                return;
            }
            JsonObject held = locationVersions.putIfAbsent(key, version);
            if (held != null && !sameWriterCaseIdentity(held, version)) {
                locationVersions.remove(key);
                ambiguousLocationVersions.add(key);
                gap("READ_FROM_WRITER_VERSION_AMBIGUOUS", key.toString(),
                        "one location version names two writer activation"
                                + " identities");
            }
        }

        /**
         * The writer version some read-time snapshot of this exact VM
         * location recorded.  A location and a version id are session-global,
         * so a snapshot another activation of the same replay session
         * published names the same write.  This resolves a read whose own
         * activation never selected the location as a carrier and therefore
         * published no snapshot of its own.
         */
        private JsonObject locationVersion(String scope, JsonObject read,
                                           long versionId) {
            String location = SharedStateEvidence.locationKey(read);
            if (location.isEmpty()) return null;
            LocationVersionKey key = new LocationVersionKey(scope, location,
                    versionId);
            return ambiguousLocationVersions.contains(key) ? null
                    : locationVersions.get(key);
        }

        private void indexBoundaryOwner(DynamicKey dynamic, CaseInfo owner,
                                        String family) {
            if (owner == null) {
                gap("CONSUMER_BOUNDARY_OWNER_CASE_MISSING", family,
                        "dynamic boundary has no exact evidence-owner case");
                return;
            }
            if (ambiguousBoundaryOwners.contains(dynamic)) return;
            CaseInfo prior = boundaryOwners.putIfAbsent(dynamic, owner);
            if (prior != null && !prior.owner.equals(owner.owner)) {
                boundaryOwners.remove(dynamic);
                ambiguousBoundaryOwners.add(dynamic);
                gap("CONSUMER_BOUNDARY_OWNER_CASE_AMBIGUOUS",
                        dynamic.toString(), "one dynamic boundary is claimed "
                                + "by two selected cases");
            }
        }

        private void putFieldRead(DynamicKey key, FieldRead read) {
            FieldRead prior = fieldReads.putIfAbsent(key, read);
            if (prior == null) return;
            if (!prior.sameLineage(read)) {
                gap("CONSUMER_BOUNDARY_EVENT_AMBIGUOUS", key.toString(),
                        "one dynamic field read maps to two exact lineages");
                return;
            }
        }

        /** Told one field-read boundary; answers whether to walk into it. */
        private interface FieldBoundaryVisitor {
            boolean visit(JsonObject boundary, long eventId);
        }

        /**
         * Walks one propagated value for field-read boundaries.  A propagated
         * field value can itself contain earlier field boundaries: their read
         * evidence is owned by earlier rows, but the exact payload may only
         * surface in this downstream row, so the walk continues into a hit
         * unless its visitor says it is finished with it.
         */
        /**
         * Walks one row's propagated value, announcing each field-read
         * boundary.
         *
         * <p>A propagated value is a shared DAG, so a boundary shell occurs in
         * many downstream copies and this descent would re-enter one node once
         * per referencing edge.  {@code entered} records the nodes this walk
         * has already gone through, and how far it may be carried is the
         * caller's to say: a visitor whose effects are idempotent may reuse
         * one across rows, while a visitor that reports per row needs its
         * own.</p>
         */
        private void walkFieldBoundaries(JsonElement element, String scope,
                                         FieldBoundaryVisitor visitor,
                                         Map<JsonElement, Set<String>> entered) {
            if (element == null || element.isJsonNull()) return;
            if (!element.isJsonPrimitive()
                    && !entered.computeIfAbsent(element,
                            ignored -> new HashSet<String>()).add(scope)) {
                return;
            }
            if (element.isJsonArray()) {
                for (JsonElement child : element.getAsJsonArray()) {
                    walkFieldBoundaries(child, scope, visitor, entered);
                }
                return;
            }
            if (!element.isJsonObject()) return;
            JsonObject node = element.getAsJsonObject();
            if (VmExpressionIr.isConsumerBoundary(node)
                    && VmExpressionIr.FIELD_READ.equals(optionalString(node,
                    VmExpressionIr.BOUNDARY_KIND))) {
                if (visitor.visit(node, optionalLongInteger(node,
                        VmExpressionIr.EVENT_ID, -1L))) {
                    walkFieldBoundaries(node.get(VmExpressionIr.EXPRESSION),
                            scope, visitor, entered);
                }
                return;
            }
            for (Map.Entry<String, JsonElement> field : node.entrySet()) {
                if (evidenceField(field.getKey())) continue;
                walkFieldBoundaries(field.getValue(), scope, visitor, entered);
            }
        }

        private void scanFieldBoundaryPayloads(
                JsonElement element, String scope) {
            // Re-entering one node under one scope can only repeat what the
            // first entry did: a gap is keyed by its rendered row and an arm
            // by its dynamic event, and both ignore an identical repeat.  So
            // this walk carries its entries across every row of the closure.
            walkFieldBoundaries(element, scope, (node, eventId) -> {
                FieldRead read = fieldReads.get(new DynamicKey(scope,
                        eventId));
                if (read == null) return true;
                JsonElement payload = node.get(VmExpressionIr.EXPRESSION);
                String fault = payload != null && payload.isJsonObject()
                        ? SharedStateEvidence.guardedReadFault(
                        payload.getAsJsonObject())
                        : "field boundary payload is not a guarded read";
                if (fault.isEmpty() && read.candidateCount
                        != array(payload.getAsJsonObject(),
                        "candidates").size()) {
                    fault = "recorded read-time candidate count does not "
                            + "match the propagated guarded read";
                }
                if (!fault.isEmpty()) {
                    gap("READ_FROM_SNAPSHOT_MISMATCH", read.family, fault);
                    return false;
                }
                addArm(read.family, VmExpressionIr.FIELD_READ,
                        read.epoch, read.scope, read.producer,
                        read.receiverOwner, payload,
                        optionalString(node, "_java_type"), eventId);
                return true;
            }, scannedBoundaries);
        }

        /**
         * Claims one case's own guarded read when no activation published its
         * read-time version-store snapshot.
         *
         * <p>A replay may take a branch its planned occurrence never took in
         * the seed run and then read a shared location that occurrence never
         * selected as a carrier.  No snapshot names that read, so the exact
         * lineage scan cannot address it.  The VM still propagated a complete
         * guarded read: it names its own location, states that its writer set
         * is complete, and carries every candidate version with its write
         * guard.  Only the stable family address is missing, and the read's
         * own VM location together with the case which carries it name that
         * exactly.</p>
         *
         * <p>A boundary two selected cases carry is a propagated value rather
         * than one case's own read.  Its reader is then not named by anything
         * here, so it stays unclaimed and the boundary is still refused.</p>
         */
        /** Stable, run-independent name of one consuming case. */
        private static String consumerKey(CaseInfo consumer) {
            return OccurrenceId.parse(consumer.occurrence).planned()
                    + "\u0000" + consumer.owner;
        }

        /**
         * Records which cases consume one read, so the composition manifest
         * and the result chain can say where a shared value travelled rather
         * than only which case happened to name it.
         */
        private void noteBoundaryConsumers(String family,
                                           Collection<CaseInfo> consumers) {
            if (family.isEmpty() || consumers.size() < 2) return;
            List<String> rendered = new ArrayList<>();
            for (CaseInfo consumer : consumers) {
                rendered.add(OccurrenceId.parse(consumer.occurrence).planned()
                        + " case " + consumer.owner);
            }
            boundaryConsumers.put(family, rendered);
        }

        private void claimUnsnapshottedFieldReads(List<JsonObject> rows) {
            Map<DynamicKey, JsonObject> boundaries = new LinkedHashMap<>();
            Map<DynamicKey, CaseInfo> readers = new LinkedHashMap<>();
            // Every case whose expressions contain the boundary.  More than
            // one is not ambiguity: one physical read of a shared location is
            // exactly the value several cases go on to consume, and that
            // sharing is the cross-region flow this tool exists to expose.
            // The read's own writers are its candidates, each already tagged
            // with its writer case, so nothing here has to order writes.
            Map<DynamicKey, Map<String, CaseInfo>> consumers =
                    new LinkedHashMap<>();
            for (JsonObject row : rows) {
                CaseInfo reader = caseForRow(row);
                if (reader == null) continue;
                Map<DynamicKey, JsonObject> found = new LinkedHashMap<>();
                collectFieldBoundaries(row,
                        optionalString(row, "boundarySessionScope"), found);
                for (Map.Entry<DynamicKey, JsonObject> boundary
                        : found.entrySet()) {
                    boundaries.putIfAbsent(boundary.getKey(),
                            boundary.getValue());
                    readers.putIfAbsent(boundary.getKey(), reader);
                    consumers.computeIfAbsent(boundary.getKey(),
                            ignored -> new TreeMap<String, CaseInfo>())
                            .put(consumerKey(reader), reader);
                }
            }
            List<DynamicKey> keys = new ArrayList<>(boundaries.keySet());
            keys.sort(Comparator.comparing((DynamicKey key) -> key.scope)
                    .thenComparingLong(key -> key.event));
            Map<String, Integer> ordinals = new LinkedHashMap<>();
            for (DynamicKey key : keys) {
                if (dynamicFamilies.containsKey(key)) continue;
                Map<String, CaseInfo> carrying = consumers.get(key);
                if (carrying == null || carrying.isEmpty()) continue;
                if (carrying.size() > MAX_BOUNDARY_CONSUMERS) {
                    gap("CONSUMER_BOUNDARY_ARM_BOUND", key.toString(),
                            "one read is consumed by " + carrying.size()
                                    + " cases, past the bound of "
                                    + MAX_BOUNDARY_CONSUMERS);
                    continue;
                }
                // The read belongs to the read, not to whichever case we
                // happened to see it in first.  Its consumers are sorted, so
                // the representative below is the same in every run.
                CaseInfo reader = carrying.values().iterator().next();
                JsonObject boundary = boundaries.get(key);
                JsonElement payload = boundary.get(VmExpressionIr.EXPRESSION);
                if (reader == null || payload == null
                        || !payload.isJsonObject()) {
                    continue;
                }
                JsonObject read = payload.getAsJsonObject();
                if (!SharedStateEvidence.guardedReadFault(read).isEmpty()) {
                    continue;
                }
                String location = SharedStateEvidence.locationKey(read);
                if (location.isEmpty()) continue;
                // A VM location key is `kind/ownerSymRid#slot`: the owner rid
                // is minted per VM session and the slot names no session, so
                // the same string addresses unrelated locations in two
                // boundary sessions of one planned occurrence.  The session
                // scope is therefore part of the slot this claim addresses;
                // without it two sessions' reads would join one family.
                String slot = "session:" + key.scope + "\u0000" + location;
                int ordinal;
                if (carrying.size() > 1) {
                    // Several cases consume this one read, so its address
                    // cannot be counted per consumer: the physical read event
                    // is already unique inside its session scope, and naming
                    // it directly is what makes every consumer resolve to the
                    // same family.  The marker also keeps such a key from ever
                    // colliding with a single-consumer read's ordinal.
                    slot = "session:" + key.scope + "\u0000read:" + key.event
                            + "\u0000" + location;
                    ordinal = 1;
                } else {
                    ordinal = ordinals.merge(reader.owner + "\n" + slot,
                            1, Integer::sum);
                }
                String family = boundaryFamilyKey(reader.epoch,
                        OccurrenceId.parse(reader.occurrence).planned(),
                        VmExpressionIr.FIELD_READ, slot, ordinal);
                if (!addDynamic(key.scope, key.event, family)) continue;
                indexBoundaryOwner(key, reader, family);
                noteBoundaryConsumers(family, carrying.values());
                addArm(family, VmExpressionIr.FIELD_READ, reader.epoch,
                        key.scope, reader, reader.owner, read,
                        optionalString(boundary, "_java_type"), key.event);
            }
        }

        /**
         * Collects every field-read boundary one row propagated itself.
         *
         * <p>Which rows report a boundary is what separates one case's own
         * read from a value two cases carry, so this walk starts with no
         * entries: a node another row already went through must still be
         * reported for this one.</p>
         */
        private void collectFieldBoundaries(JsonElement element, String scope,
                                            Map<DynamicKey, JsonObject> out) {
            walkFieldBoundaries(element, scope, (node, eventId) -> {
                if (!scope.isEmpty() && eventId > 0L) {
                    out.putIfAbsent(new DynamicKey(scope, eventId), node);
                }
                return true;
            }, new IdentityHashMap<JsonElement, Set<String>>());
        }

        private boolean addDynamic(String scope, long eventId,
                                   String family) {
            if (scope.isEmpty() || eventId <= 0L || family.isEmpty()) {
                gap("CONSUMER_BOUNDARY_FAMILY_MISSING",
                        scope + ":" + eventId,
                        "a boundary event carries no addressable session"
                                + " scope, event id or family");
                return false;
            }
            DynamicKey key = new DynamicKey(scope, eventId);
            String prior = dynamicFamilies.putIfAbsent(key, family);
            if (prior != null && !prior.equals(family)) {
                gap("CONSUMER_BOUNDARY_EVENT_AMBIGUOUS", key.toString(),
                        "one dynamic event maps to two stable families");
                return false;
            }
            return true;
        }

        private CaseInfo uniqueProducerCase(String scope, String task,
                                            String occurrence,
                                            String subject) {
            List<CaseInfo> candidates = new ArrayList<>();
            if (!task.isEmpty()) {
                candidates.addAll(casesByExecution.getOrDefault(
                        executionKey(scope, task, occurrence),
                        Collections.emptyList()));
            } else {
                for (List<CaseInfo> values : casesByExecution.values()) {
                    for (CaseInfo value : values) {
                        if (scope.equals(value.sessionScope)
                                && occurrence.equals(value.occurrence)) {
                            candidates.add(value);
                        }
                    }
                }
            }
            Map<String, CaseInfo> unique = new LinkedHashMap<>();
            for (CaseInfo candidate : candidates) {
                unique.put(candidate.owner, candidate);
            }
            if (unique.size() != 1) {
                gap(unique.isEmpty()
                                ? "CONSUMER_BOUNDARY_PRODUCER_CASE_MISSING"
                                : "CONSUMER_BOUNDARY_PRODUCER_CASE_AMBIGUOUS",
                        subject, "runtime producer execution maps to "
                                + unique.size() + " selected cases");
                return null;
            }
            return unique.values().iterator().next();
        }

        private void addArm(String familyKey, String kind, String epoch,
                            String scope, CaseInfo producer,
                            String receiverOwner, JsonElement expression,
                            String javaType, long eventId) {
            if (producer == null || expression == null
                    || expression.isJsonNull()) {
                gap("CONSUMER_BOUNDARY_ARM_INCOMPLETE", familyKey,
                        "arm has no exact producer case or payload");
                return;
            }
            if (javaType.isEmpty()) {
                gap("CONSUMER_BOUNDARY_FAMILY_TYPE_MISSING", familyKey,
                        "boundary arm names no Java type");
                return;
            }
            Family family = families.computeIfAbsent(familyKey,
                    ignored -> new Family(familyKey, kind, epoch, javaType));
            if (!family.kind.equals(kind) || !family.epoch.equals(epoch)) {
                gap("CONSUMER_BOUNDARY_FAMILY_EPOCH_CONFLICT", familyKey,
                        "one family crosses a kind or topology epoch");
                return;
            }
            if (!sameJavaType(family.javaType, javaType)) {
                gap("CONSUMER_BOUNDARY_FAMILY_TYPE_CONFLICT", familyKey,
                        "one family crosses incompatible Java types");
                return;
            }
            DynamicKey dynamic = new DynamicKey(scope, eventId);
            ArmLineage lineage = new ArmLineage(familyKey, producer,
                    receiverOwner);
            ArmLineage priorLineage = dynamicArmLineages.putIfAbsent(
                    dynamic, lineage);
            if (priorLineage != null && !priorLineage.same(lineage)) {
                gap("CONSUMER_BOUNDARY_EVENT_AMBIGUOUS",
                        dynamic.toString(), "one dynamic boundary event maps "
                                + "to two producer/receiver lineages");
                return;
            }

            // A boundary shell propagates unchanged through downstream
            // expressions.  Large state expressions can contain thousands of
            // copies of that shell, and a later serialization may truncate a
            // copy even though the original event payload was complete.  The
            // VM event is the observation anchor: retain one complete payload
            // and never let a lossy copy compete with it as another arm.
            if (dynamicArms.containsKey(dynamic)) return;
            if (SharedStateEvidence.containsVmSerializationTruncation(
                    expression)) {
                truncatedDynamicArms.putIfAbsent(dynamic, familyKey);
                return;
            }
            Arm arm = new Arm(producer, receiverOwner, scope, eventId,
                    expression);
            dynamicArms.put(dynamic, arm);
            family.add(arm);
        }

        private void validateDynamicArms() {
            for (Map.Entry<DynamicKey, String> observation
                    : truncatedDynamicArms.entrySet()) {
                if (dynamicArms.containsKey(observation.getKey())) continue;
                namedEmptyFamilies.add(observation.getValue());
                gap(VmExpressionIr.RPC_ATTACH.equals(
                                familyKinds.get(observation.getValue()))
                                ? RPC_ATTACH_SENDER_EXPRESSION_MISSING
                                : "CONSUMER_BOUNDARY_PAYLOAD_TRUNCATED",
                        observation.getValue(), "dynamic boundary "
                                + observation.getKey()
                                + " has no complete payload observation");
            }
        }

        private Result rewrite(JsonObject fatal) {
            JsonObject fatalCopy = fatal == null ? new JsonObject()
                    : JsonFields.shallowCopy(fatal);
            JsonObject rewrittenFatal = rewriteObject(fatalCopy,
                    scopeOf(fatalCopy));
            List<JsonObject> summaries = new ArrayList<>();
            for (JsonObject encodedSummary
                    : shallowCopies(inputSummaryRows)) {
                // Map ownership is a fact about the VM's raw state trees.
                // Preserve that fact before rewriting nested consumer
                // boundaries into multi-case expressions; recorded evidence
                // deliberately remains raw.
                CaseInfo observation = caseForSummary(encodedSummary);
                summaries.add(rewriteObject(encodedSummary,
                        optionalString(encodedSummary, "boundarySessionScope"),
                        observation));
            }
            List<String> owners = new ArrayList<>(
                    caseObservationsByOwner.keySet());
            Collections.sort(owners);
            for (String owner : owners) closedPathCondition(owner);
            for (JsonObject summary : summaries) {
                CaseInfo observation = caseForSummary(summary);
                if (observation != null
                        && observationOwners.contains(observation.owner)) {
                    stampObservation(summary, observation);
                }
            }
            // Family resolution closes values.  Publish the selector-to-PC
            // relation only after every local PC has been closed once; doing
            // this recursively from resolveFamily used to expand and render
            // the same upstream PC for every consumer arm.
            List<String> resolvedFamilies = new ArrayList<>(
                    resolved.keySet());
            Collections.sort(resolvedFamilies);
            for (String familyKey : resolvedFamilies) {
                Family family = families.get(familyKey);
                JsonElement merge = resolved.get(familyKey);
                if (family != null && merge != null
                        && merge.isJsonObject()) {
                    dependency(family, array(merge.getAsJsonObject(),
                            "arms"));
                }
            }
            // Closing one PC can reveal another nested RF dependency. Drain
            // the stable-key work set instead of assuming a one-hop chain.
            Set<String> emittedWriterCases = new LinkedHashSet<>();
            while (!emittedWriterCases.containsAll(
                    readFromWriterCases.keySet())) {
                List<String> pending = new ArrayList<>();
                for (String family : readFromWriterCases.keySet()) {
                    if (!emittedWriterCases.contains(family)) {
                        pending.add(family);
                    }
                }
                Collections.sort(pending);
                for (String family : pending) {
                    readFromWriterCaseDependency(family,
                            readFromWriterCases.get(family));
                    emittedWriterCases.add(family);
                }
            }
            reportUnreferencedAttachFamilies();
            return new Result(gaps.isEmpty(), rewrittenFatal, summaries,
                    orderedValues(dependencies),
                    orderedValues(gaps));
        }

        /**
         * Declared wire handoffs that ended the closure with nothing in them.
         *
         * <p>{@link #resolveFamily} names an attach family whose arms are
         * empty, and {@link #validateDynamicArms} names one whose payload was
         * truncated. A family with no arm that no consumer leaf ever
         * referenced falls between the two and used to leave no trace at all
         * -- which is the shape of a declared flow whose producer side the
         * closure never walked. Every attach family is a declared wire
         * handoff by construction: the kind is set only where a
         * {@code communicationHandoffs} port produced the boundary evidence.
         * So the sweep needs no port list to know these are the experiment's
         * own flows.</p>
         */
        private void reportUnreferencedAttachFamilies() {
            List<String> keys = new ArrayList<>(familyKinds.keySet());
            Collections.sort(keys);
            for (String key : keys) {
                if (!VmExpressionIr.RPC_ATTACH.equals(familyKinds.get(key))
                        || resolved.containsKey(key)
                        || namedEmptyFamilies.contains(key)) {
                    continue;
                }
                Family family = families.get(key);
                if (family != null && !family.arms.isEmpty()) {
                    continue;
                }
                String port = familyPorts.get(key);
                gap(RPC_ATTACH_SENDER_EXPRESSION_MISSING,
                        port == null || port.isEmpty() ? key : port,
                        "declared value handoff reached no arm and no"
                                + " consumer reference, so the value the wire"
                                + " carried never entered the formula"
                                + " (receiver "
                                + JsonFields.firstNonBlank(
                                        familyReceivers.get(key), "unknown")
                                + ")");
            }
        }

        private JsonObject rewriteObject(JsonObject input, String scope) {
            return rewriteObject(input, scope, null);
        }

        private JsonObject rewriteObject(JsonObject input, String scope,
                                         CaseInfo observation) {
            JsonElement rewritten = rewriteElement(input, scope,
                    observation);
            return rewritten != null && rewritten.isJsonObject()
                    ? rewritten.getAsJsonObject() : new JsonObject();
        }

        /**
         * Closes an expression in one physical case observation.  A boundary
         * owned by that exact execution is already the propagated value for
         * this observation, so keep its payload directly.  Other boundaries
         * remain symbolic case merges and preserve upstream exploration.
         */
        private JsonElement rewriteElement(JsonElement value, String scope,
                                           CaseInfo observation) {
            if (value == null || value.isJsonNull()
                    || value.isJsonPrimitive()) {
                return value;
            }
            String exactScope = safe(scope);
            String rewriteScope = observation == null
                    ? exactScope : exactScope + "\u0000"
                    + observation.observationSelector;
            Map<String, JsonElement> scoped = rewritten.get(value);
            if (scoped != null && scoped.containsKey(rewriteScope)) {
                return scoped.get(rewriteScope);
            }
            JsonElement result;
            if (value.isJsonArray()) {
                JsonArray array = new JsonArray();
                for (JsonElement child : value.getAsJsonArray()) {
                    array.add(rewriteElement(child, exactScope,
                            observation));
                }
                result = array;
            } else {
                JsonObject node = value.getAsJsonObject();
                if (SharedStateEvidence.claimsGuardedRead(node)) {
                    result = rewriteGuardedRead(node, exactScope,
                            observation);
                } else if (VmExpressionIr.isConsumerBoundary(node)
                    || VmExpressionIr.isConsumerBoundaryReference(node)) {
                    result = resolveBoundary(node, exactScope, observation);
                } else {
                    String localScope = first(optionalString(node,
                            "boundarySessionScope"), exactScope);
                    JsonObject object = new JsonObject();
                    for (Map.Entry<String, JsonElement> field
                            : node.entrySet()) {
                        if (evidenceField(field.getKey())) {
                            object.add(field.getKey(), field.getValue());
                        } else {
                            object.add(field.getKey(), rewriteElement(
                                    field.getValue(), localScope,
                                    observation));
                        }
                    }
                    result = object;
                }
            }
            rewritten.computeIfAbsent(value,
                    ignored -> new LinkedHashMap<>()).put(rewriteScope,
                    result);
            return result;
        }

        /**
         * Keeps the VM-propagated writer value and adds its stable local-case
         * closure. The raw {@code pathGuard} still means branches taken at the
         * write itself; enclosing region reachability comes from the exact
         * runtime activation stack.
         */
        private JsonElement rewriteGuardedRead(JsonObject source,
                                               String scope,
                                               CaseInfo observation) {
            JsonObject result = new JsonObject();
            for (Map.Entry<String, JsonElement> field : source.entrySet()) {
                if (!"candidates".equals(field.getKey())) {
                    result.add(field.getKey(), rewriteElement(
                            field.getValue(), scope, observation));
                    continue;
                }
                JsonArray candidates = new JsonArray();
                for (JsonElement encoded : array(source, "candidates")) {
                    if (!encoded.isJsonObject()) {
                        candidates.add(rewriteElement(encoded, scope,
                                observation));
                        continue;
                    }
                    JsonObject rawCandidate = encoded.getAsJsonObject();
                    JsonObject candidate = rewriteObject(rawCandidate, scope,
                            observation);
                    attachWriterCase(source, rawCandidate, candidate, scope);
                    candidates.add(candidate);
                }
                result.add("candidates", candidates);
            }
            attachReadChoiceIdentity(source, result, scope);
            stampCandidateSelectors(result);
            return result;
        }

        /** One logical read is stable across physical replay sessions. */
        private void attachReadChoiceIdentity(JsonObject source,
                                              JsonObject target,
                                              String scope) {
            if (!SharedStateEvidence.claimsGuardedRead(source)) return;
            long eventId = optionalLongInteger(source, "readEventId", -1L);
            DynamicKey dynamic = new DynamicKey(scope, eventId);
            CaseInfo owner = ambiguousBoundaryOwners.contains(dynamic)
                    ? null : boundaryOwners.get(dynamic);
            String family = dynamicFamilies.get(dynamic);
            if (eventId <= 0L || family == null || family.isEmpty()
                    || owner == null) {
                gap("READ_CHOICE_IDENTITY_MISSING",
                        safe(scope) + ":" + eventId,
                        "guarded read has no stable boundary family and exact"
                                + " reader case");
                return;
            }
            String identity = "RFC." + CanonicalJson.sha256(family + "\n"
                    + owner.owner);
            target.addProperty(READ_CHOICE_IDENTITY, identity);
            target.addProperty(READ_CHOICE_OWNER, owner.owner);
            target.addProperty(READ_CHOICE_OCCURRENCE_ID, owner.occurrence);
            FieldRead read = fieldReads.get(dynamic);
            if (read != null) {
                target.addProperty("replayReadDescriptor", read.descriptor);
            }
        }

        private void stampCandidateSelectors(JsonObject read) {
            String readIdentity = optionalString(read, READ_CHOICE_IDENTITY);
            if (readIdentity.isEmpty()) return;
            Map<String, Integer> duplicates = new LinkedHashMap<>();
            JsonArray selectors = new JsonArray();
            List<String> uncovered = new ArrayList<>();
            for (JsonElement encoded : array(read, "candidates")) {
                if (!encoded.isJsonObject()) continue;
                JsonObject candidate = encoded.getAsJsonObject();
                String owner = optionalString(candidate, WRITER_CASE_OWNER);
                if (owner.isEmpty()) {
                    // Say which recorded write the cover is short of: the
                    // composer only sees the short array and can name no
                    // more than the read itself.
                    uncovered.add("writer=" + optionalLongInteger(
                            candidate, "fieldVersionId", -1L));
                    continue;
                }
                String base = owner + "\n" + optionalString(candidate, "versionKind")
                        + "\n" + semanticIdentity(candidate.get("expression"),
                        owner) + "\n" + semanticIdentity(
                        candidate.get("pathGuard"), owner) + "\n"
                        + semanticIdentity(candidate.get(
                        WRITER_CASE_CLOSURE), owner);
                int ordinal = duplicates.merge(base, 1, Integer::sum);
                String candidateIdentity = "RFC_ARM."
                        + CanonicalJson.sha256(base + "\n" + ordinal);
                String selector = GuardedReadNaming.selector(readIdentity,
                        candidateIdentity);
                candidate.addProperty(READ_CANDIDATE_IDENTITY,
                        candidateIdentity);
                candidate.addProperty("selector", selector);
                selectors.add(selector);
            }
            if (selectors.size() != array(read, "candidates").size()) {
                gap("READ_FROM_CANDIDATE_IDENTITY_MISSING", readIdentity,
                        "not every candidate has a stable writer case: "
                                + uncovered);
            }
            read.add("exactlyOne", selectors);
        }

        private void attachWriterCase(JsonObject read,
                                      JsonObject rawCandidate,
                                      JsonObject candidate,
                                      String scope) {
            long readEvent = optionalLongInteger(read, "readEventId", -1L);
            long versionId = optionalLongInteger(rawCandidate,
                    "fieldVersionId", -1L);
            if (readEvent <= 0L || versionId <= 0L) {
                gap("READ_FROM_WRITER_CASE_MISSING", scope,
                        "guarded read arm has no exact read/version identity");
                return;
            }
            ReadCandidateKey key = new ReadCandidateKey(scope, readEvent,
                    versionId);
            JsonObject version = ambiguousReadCandidateVersions.contains(key)
                    ? null : readCandidateVersions.get(key);
            if (version == null) {
                version = locationVersion(scope, read, versionId);
            }
            if (version == null) {
                gap("READ_FROM_WRITER_CASE_MISSING", key.toString(),
                        "guarded read candidate has no unique admitted writer"
                                + " version metadata");
                return;
            }
            if (!sameReadCandidate(read, rawCandidate, version)) {
                gap("READ_FROM_CANDIDATE_SNAPSHOT_MISMATCH", key.toString(),
                        "guarded-read arm disagrees with its read-time writer"
                                + " snapshot");
                return;
            }
            boolean initialVersion = "INITIAL".equals(optionalString(version,
                    "versionKind"));
            CaseInfo producer = initialVersion
                    ? initialSourceCase(read, version, scope, key)
                    : uniqueProducerCase(scope,
                    optionalString(version, "taskId"),
                    optionalString(version,
                            SharedStateEvidence.WRITER_OCCURRENCE_ID),
                    key.toString());
            if (producer == null) return;
            List<CaseInfo> closure = initialVersion
                    ? Collections.singletonList(producer)
                    : writerCaseClosure(scope, version, producer,
                    key.toString());
            if (closure.isEmpty()) return;
            for (CaseInfo owner : closure) registerWriterCase(owner);
            String family = writerCaseFamily(producer);
            candidate.addProperty(WRITER_CASE_FAMILY, family);
            candidate.addProperty(WRITER_CASE_OWNER, producer.owner);
            candidate.addProperty(WRITER_CASE_SELECTOR, producer.selector);
            candidate.addProperty(WRITER_CASE_REGION_ID, producer.region);
            candidate.addProperty(WRITER_CASE_OCCURRENCE_ID,
                    producer.occurrence);
            // The propagated value is the exact writer observation's value.
            // Keep its JVM scope with the arm so allocation ids embedded in
            // that value are interpreted in the replay that produced them.
            stampObservation(candidate, producer);
            JsonArray encodedClosure = new JsonArray();
            for (CaseInfo owner : closure) {
                JsonObject encoded = new JsonObject();
                encoded.addProperty(WRITER_CASE_FAMILY,
                        writerCaseFamily(owner));
                encoded.addProperty(WRITER_CASE_OWNER, owner.owner);
                encoded.addProperty(WRITER_CASE_SELECTOR, owner.selector);
                encoded.addProperty(WRITER_CASE_REGION_ID, owner.region);
                encoded.addProperty(WRITER_CASE_OCCURRENCE_ID,
                        owner.occurrence);
                encodedClosure.add(encoded);
            }
            candidate.add(WRITER_CASE_CLOSURE, encodedClosure);
        }

        private void registerWriterCase(CaseInfo owner) {
            String family = writerCaseFamily(owner);
            Map<String, CaseInfo> cases = readFromWriterCases.computeIfAbsent(
                    family, ignored -> new LinkedHashMap<>());
            CaseInfo held = cases.putIfAbsent(owner.owner, owner);
            if (held != null && !held.sameLocalIdentity(owner)) {
                gap("READ_FROM_WRITER_CASE_AMBIGUOUS", family,
                        "one writer-case dependency names two local cases");
            }
        }

        /** Resolves a physical writer's selected-region stack to local cases. */
        private List<CaseInfo> writerCaseClosure(
                String scope, JsonObject version, CaseInfo producer,
                String subject) {
            JsonObject recorded = object(version, WRITER_ACTIVATION_CLOSURE);
            if (!WRITER_ACTIVATION_CLOSURE_AUTHORITY.equals(
                    optionalString(recorded, "authority"))
                    || !optionalBool(recorded, "complete", false)) {
                gap("READ_FROM_WRITER_CASE_CLOSURE_MISSING", subject,
                        "writer version has no complete physical activation"
                                + " closure");
                return Collections.emptyList();
            }
            JsonArray addresses = array(recorded, "cases");
            if (addresses.size() == 0) {
                gap("READ_FROM_WRITER_CASE_CLOSURE_EMPTY", subject,
                        "writer activation closure names no local case");
                return Collections.emptyList();
            }
            Map<String, CaseInfo> resolvedCases = new LinkedHashMap<>();
            boolean valid = true;
            for (JsonElement element : addresses) {
                if (!element.isJsonObject()) {
                    valid = false;
                    continue;
                }
                JsonObject address = element.getAsJsonObject();
                String task = optionalString(address, "taskId");
                String region = optionalString(address, "regionId");
                String occurrence = optionalString(address, "occurrenceId");
                CaseInfo owner = uniqueProducerCase(scope, task, occurrence,
                        subject + ":" + occurrence);
                if (owner == null || region.isEmpty()
                        || !region.equals(owner.region)) {
                    valid = false;
                    if (owner != null) {
                        gap("READ_FROM_WRITER_CASE_CLOSURE_MISMATCH", subject,
                                "writer activation address resolves to a"
                                        + " different region");
                    }
                    continue;
                }
                resolvedCases.put(owner.owner, owner);
            }
            if (!resolvedCases.containsKey(producer.owner)) {
                valid = false;
                gap("READ_FROM_WRITER_CASE_CLOSURE_OMITS_WRITER", subject,
                        "physical activation closure omits the writer case");
            }
            return valid ? new ArrayList<>(resolvedCases.values())
                    : Collections.emptyList();
        }

        /**
         * The VM creates an INITIAL version from the value already present when
         * a location becomes symbolic.  Its expression and explicit pathGuard
         * are complete value authority; requiring a later relation summary for
         * the activation that installed the snapshot would turn source
         * propagation into a fictitious write-case dependency.
         */
        private CaseInfo initialSourceCase(JsonObject read, JsonObject version,
                                           String scope,
                                           ReadCandidateKey key) {
            DynamicKey readKey = new DynamicKey(scope,
                    optionalLongInteger(read, "readEventId", -1L));
            CaseInfo reader = ambiguousBoundaryOwners.contains(readKey)
                    ? null : boundaryOwners.get(readKey);
            String location = SharedStateEvidence.locationKey(read);
            JsonElement expression = version.get("expression");
            if (reader == null || location.isEmpty() || expression == null
                    || expression.isJsonNull()) {
                gap("READ_FROM_INITIAL_SOURCE_MISSING", key.toString(),
                        "initial candidate has no stable reader, location, or"
                                + " propagated expression");
                return null;
            }
            // Telemetry, not a refusal: an opaque or truncated INITIAL still
            // lowers, as the free container const it has always been, and the
            // reader is told that membership over it stays undecidable.
            if (SharedStateEvidence.isMapState(location)
                    && SharedStateEvidence.initialSnapshotTruncated(version)) {
                gap(INITIAL_CONTAINER_SNAPSHOT_TRUNCATED, location,
                        "whole-state carrier published no complete initial"
                                + " content snapshot, so membership over its"
                                + " initial state stays undecidable");
            }
            String writerOccurrence = OccurrenceId.parse(
                    optionalString(version,
                            SharedStateEvidence.WRITER_OCCURRENCE_ID))
                    .planned();
            String source = first(optionalString(version,
                    SharedStateEvidence.WRITER_SOURCE_KEY), writerOccurrence);
            String identity = reader.epoch + "\n" + location + "\n" + source
                    + "\n" + writerOccurrence + "\n"
                    + semanticIdentity(expression, "");
            String digest = CanonicalJson.sha256(identity);
            String owner = INITIAL_SOURCE_CASE_PREFIX + digest;
            CaseInfo initial = new CaseInfo(owner,
                    LocalCaseIdentity.selector(owner),
                    INITIAL_SOURCE_CASE_PREFIX
                            + CanonicalJson.sha256(location),
                    owner, INITIAL_SOURCE_CASE_PREFIX + digest,
                    reader.sessionScope, reader.epoch,
                    new JsonArray());
            putCase(initial);
            return casesByOwner.get(owner);
        }

        /**
         * The propagated arm must be derived from the exact value in the
         * read-time row. Scalar reads carry that value directly. A container
         * read carries the query applied to the recorded whole-state value,
         * so its receiver -- rather than the query result -- is the snapshot.
         */
        private boolean sameReadCandidate(JsonObject read,
                                          JsonObject candidate,
                                          JsonObject version) {
            return optionalLongInteger(candidate, "fieldVersionId", -1L)
                    == optionalLongInteger(version, "fieldVersionId", -2L)
                    && optionalString(candidate, "versionKind").equals(
                    optionalString(version, "versionKind"))
                    && sameReadCandidateValue(read,
                    candidate.get("expression"), version.get("expression"))
                    && semanticIdentity(candidate.get("pathGuard"), "")
                    .equals(semanticIdentity(version.get("pathGuard"), ""));
        }

        private boolean sameReadCandidateValue(JsonObject read,
                                               JsonElement candidate,
                                               JsonElement version) {
            String versionIdentity = semanticIdentity(version, "");
            if (!SharedStateEvidence.isMapState(
                    SharedStateEvidence.locationKey(read))) {
                return semanticIdentity(candidate, "")
                        .equals(versionIdentity);
            }
            if (candidate == null || !candidate.isJsonObject()) return false;
            JsonObject query = candidate.getAsJsonObject();
            return "ContainerRelation".equals(optionalString(query, "_type"))
                    && semanticIdentity(query.get("receiver"), "")
                    .equals(versionIdentity);
        }

        private static String writerCaseFamily(CaseInfo producer) {
            return "CBF." + CanonicalJson.sha256(
                    READ_FROM_DEPENDENCY_POLICY + "\n" + producer.epoch
                            + "\n" + producer.region + "\n"
                            + producer.occurrence);
        }

        private JsonElement resolveBoundary(JsonObject boundary,
                                            String scope,
                                            CaseInfo observation) {
            String family = optionalString(boundary, VmExpressionIr.FAMILY_KEY);
            long eventId = optionalLongInteger(boundary, VmExpressionIr.EVENT_ID,
                    -1L);
            DynamicKey dynamic = new DynamicKey(scope, eventId);
            Arm exact = dynamicArms.get(dynamic);
            if (observation != null && exact != null
                    && exact.producer.sameExecution(observation)
                    && exact.producer.owner.equals(observation.owner)) {
                return rewriteElement(exact.expression, scope, observation);
            }
            if (family.isEmpty()) {
                family = dynamicFamilies.get(dynamic);
            }
            if (family == null || family.isEmpty()) {
                gap("CONSUMER_BOUNDARY_FAMILY_MISSING",
                        scope + ":" + eventId,
                        "dynamic boundary has no exact stable-family join");
                return JsonFields.shallowCopy(boundary);
            }
            return resolveFamily(family);
        }

        private JsonElement resolveFamily(String key) {
            JsonElement held = resolved.get(key);
            if (held != null) return held;
            Family family = families.get(key);
            if (family == null || family.arms.isEmpty()) {
                // A referenced family with no arm leaves the consumer's leaf
                // equal to nothing.  For a wire that is the sender's
                // expression having failed to reach the join, which is a
                // different fact from a field read with no writer case.
                namedEmptyFamilies.add(key);
                gap(VmExpressionIr.RPC_ATTACH.equals(familyKinds.get(key))
                                ? RPC_ATTACH_SENDER_EXPRESSION_MISSING
                                : "CONSUMER_BOUNDARY_FAMILY_UNOBSERVED",
                        key, "stable family has no receiver-owned payload"
                                + " arms");
                return missingReference(key);
            }
            if (!active.add(key)) {
                gap("CONSUMER_BOUNDARY_FAMILY_CYCLE", key,
                        "boundary families form a value cycle");
                return missingReference(key);
            }
            // The depth a family is first reached at is the one that answers
            // "how far behind the target is this wire"; reaching it again
            // through a longer path does not move it further away.
            Integer heldDepth = depthByFamily.get(key);
            if (heldDepth == null || chainDepth < heldDepth) {
                depthByFamily.put(key, chainDepth);
            }
            chainDepth++;
            try {
                JsonObject merge = new JsonObject();
                merge.addProperty("_type", ITE_TYPE);
                merge.addProperty("_java_type", family.javaType);
                merge.addProperty("mergeId", "CONSUMER."
                        + CanonicalJson.sha256(key));
                merge.addProperty(VmExpressionIr.FAMILY_KEY, key);
                merge.addProperty(VmExpressionIr.TOPOLOGY_EPOCH,
                        family.epoch);
                JsonArray arms = new JsonArray();
                List<String> selectors = new ArrayList<>(
                        family.arms.keySet());
                Collections.sort(selectors);
                for (String selector : selectors) {
                    List<Arm> observations = family.arms.get(selector);
                    observations.sort(Comparator.comparing(Arm::identity));
                    Map<String, Arm> armByObservation =
                            new LinkedHashMap<>();
                    Map<String, JsonElement> valueByObservation =
                            new LinkedHashMap<>();
                    Map<String, String> identityByObservation =
                            new LinkedHashMap<>();
                    for (Arm observation : observations) {
                        JsonElement candidate = rewriteElement(
                                observation.expression,
                                observation.sessionScope,
                                observation.producer);
                        String observationSelector = observation.producer
                                .observationSelector;
                        String semantic = semanticIdentity(candidate,
                                observation.producer.owner);
                        String heldIdentity = identityByObservation.putIfAbsent(
                                observationSelector, semantic);
                        if (heldIdentity != null
                                && !heldIdentity.equals(semantic)) {
                            gap("CONSUMER_BOUNDARY_OBSERVATION_AMBIGUOUS",
                                    family.key, "one physical case observation"
                                            + " carries two propagated values");
                            continue;
                        }
                        armByObservation.putIfAbsent(observationSelector,
                                observation);
                        valueByObservation.putIfAbsent(observationSelector,
                                candidate);
                    }
                    Set<String> payloads = new LinkedHashSet<>(
                            identityByObservation.values());
                    if (valueByObservation.isEmpty()) {
                        gap("CONSUMER_BOUNDARY_OBSERVATION_MISSING",
                                family.key, "case has no usable physical"
                                        + " propagation observation");
                        continue;
                    }
                    if (payloads.size() <= 1) {
                        Arm arm = observations.get(0);
                        JsonElement expression = valueByObservation.values()
                                .iterator().next();
                        arms.add(encodedArm(arm, arm.producer.selector,
                                expression, false));
                        continue;
                    }
                    Arm seed = observations.get(0);
                    observationOwners.add(seed.producer.owner);
                    List<String> physical = new ArrayList<>(
                            armByObservation.keySet());
                    Collections.sort(physical);
                    for (String observationSelector : physical) {
                        Arm arm = armByObservation.get(observationSelector);
                        if (observationSelector.isEmpty()) {
                            gap("CONSUMER_BOUNDARY_OBSERVATION_SCOPE_MISSING",
                                    family.key, "different replay values have"
                                            + " no exact session scope");
                            continue;
                        }
                        arms.add(encodedArm(arm, observationSelector,
                                valueByObservation.get(observationSelector),
                                true));
                    }
                }
                merge.add("arms", arms);
                resolved.put(key, merge);
                return merge;
            } finally {
                chainDepth--;
                active.remove(key);
            }
        }

        private static JsonObject encodedArm(Arm arm, String selector,
                                             JsonElement expression,
                                             boolean observed) {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("selector", selector);
            encoded.addProperty("caseSelector", arm.producer.selector);
            encoded.addProperty("caseOwner", arm.producer.owner);
            encoded.addProperty("regionId", arm.producer.region);
            encoded.addProperty("occurrenceId", arm.producer.occurrence);
            // Even when equal payloads from several replays collapse onto
            // the replay-independent case selector, the retained expression
            // still contains VM allocation ids from one concrete replay.
            // Keep that representative's scope so structural witnesses are
            // interpreted in the JVM which produced them.
            stampExecutionScope(encoded, arm.producer);
            if (observed) {
                encoded.addProperty(OBSERVATION_SELECTOR,
                        arm.producer.observationSelector);
            }
            encoded.add("expression", expression);
            return encoded;
        }

        private static void stampObservation(JsonObject row,
                                             CaseInfo observation) {
            row.addProperty(OBSERVATION_SELECTOR,
                    observation.observationSelector);
            row.addProperty(OBSERVATION_SCOPE,
                    observation.sessionScope);
        }

        private void dependency(Family family, JsonArray arms) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", SCHEMA_VERSION);
            row.addProperty("kind", DEPENDENCY_KIND);
            row.addProperty("authority", "REGION_CASE_PC_V1");
            row.addProperty(VmExpressionIr.FAMILY_KEY, family.key);
            row.addProperty("boundaryKind", family.kind);
            row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, family.epoch);
            Integer depth = depthByFamily.get(family.key);
            row.addProperty(BOUNDARY_DEPTH, depth == null ? 0 : depth);
            JsonArray encoded = new JsonArray();
            for (JsonElement element : arms) {
                JsonObject arm = element.getAsJsonObject();
                String observationSelector = optionalString(arm,
                        OBSERVATION_SELECTOR);
                if (!observationSelector.isEmpty()) {
                    JsonObject item = dependencyArm(arm,
                            observationSelector);
                    copyObservationIdentity(arm, item);
                    CaseInfo observation = caseObservation(
                            optionalString(arm, "caseOwner"), observationSelector);
                    JsonElement pathCondition = observation == null ? null
                            : rewriteElement(observation.pathCondition,
                            observation.sessionScope, observation);
                    if (observation != null
                            && observation.pathCondition == null) {
                        gap("LOCAL_CASE_OBSERVATION_PC_MISSING",
                                observation.owner,
                                "replay-specific propagated value has no"
                                        + " matching path condition");
                    }
                    if (pathCondition != null) {
                        item.add("pathCondition", pathCondition);
                    }
                    encoded.add(item);
                    continue;
                }

                String owner = optionalString(arm, "caseOwner");
                // Composer stamps every summary of an observation-owned
                // case with its physical selector.  Publish the dependency
                // in that same flat identity space even when this family's
                // payload happens to be equal in every replay and therefore
                // still uses the base selector in the value merge.
                if (observationOwners.contains(owner)) {
                    for (JsonElement observed : pathObservations(owner)) {
                        JsonObject observation = observed.getAsJsonObject();
                        String selector = optionalString(observation, "selector");
                        JsonObject item = dependencyArm(arm, selector);
                        copyObservationIdentity(observation, item);
                        item.add("pathCondition",
                                observation.get("pathCondition"));
                        encoded.add(item);
                    }
                    continue;
                }

                JsonObject item = dependencyArm(arm,
                        optionalString(arm, "selector"));
                copyObservationIdentity(arm, item);
                JsonElement pathCondition = closedPathCondition(owner);
                if (pathCondition != null) {
                    item.add("pathCondition", pathCondition);
                }
                encoded.add(item);
            }
            row.add("arms", encoded);
            dependencies.put(family.key, row);
        }

        private static JsonObject dependencyArm(JsonObject source,
                                                String selector) {
            JsonObject item = new JsonObject();
            item.addProperty("selector", selector);
            item.addProperty("caseSelector", first(
                    optionalString(source, "caseSelector"),
                    optionalString(source, "selector")));
            item.addProperty("caseOwner", optionalString(source, "caseOwner"));
            item.addProperty("regionId", optionalString(source, "regionId"));
            item.addProperty("occurrenceId",
                    optionalString(source, "occurrenceId"));
            return item;
        }

        private static void copyObservationIdentity(JsonObject source,
                                                    JsonObject target) {
            for (String field : new String[]{OBSERVATION_SELECTOR,
                    OBSERVATION_SCOPE}) {
                JsonElement value = source.get(field);
                if (value != null) target.add(field, value);
            }
        }

        /** Carries the JVM scope needed to lower execution-local witnesses. */
        private static void stampExecutionScope(JsonObject target,
                                                CaseInfo observation) {
            if (observation.sessionScope.isEmpty()) return;
            target.addProperty(OBSERVATION_SCOPE,
                    observation.sessionScope);
        }

        private CaseInfo caseObservation(String owner, String selector) {
            for (CaseInfo observation : caseObservationsByOwner.getOrDefault(
                    owner, Collections.emptyList())) {
                if (selector.equals(observation.observationSelector)) {
                    return observation;
                }
            }
            gap("LOCAL_CASE_OBSERVATION_MISSING", owner,
                    "dependency arm has no exact case observation");
            return null;
        }

        /** Publishes one shared PC definition for all RF arms of one case. */
        private void readFromWriterCaseDependency(
                String family, Map<String, CaseInfo> referenced) {
            if (referenced == null || referenced.isEmpty()) return;
            CaseInfo seed = referenced.values().iterator().next();
            Map<String, CaseInfo> partition = new LinkedHashMap<>();
            for (CaseInfo candidate : casesByOwner.values()) {
                if (seed.region.equals(candidate.region)
                        && seed.epoch.equals(candidate.epoch)
                        && seed.occurrence.equals(candidate.occurrence)) {
                    partition.put(candidate.owner, candidate);
                }
            }
            if (!partition.keySet().containsAll(referenced.keySet())) {
                gap("READ_FROM_WRITER_CASE_PARTITION_INCOMPLETE", family,
                        "writer-case occurrence partition omits a referenced"
                                + " producer case");
                return;
            }
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", SCHEMA_VERSION);
            row.addProperty("kind", DEPENDENCY_KIND);
            row.addProperty("authority", "REGION_CASE_PC_V1");
            row.addProperty(VmExpressionIr.FAMILY_KEY, family);
            row.addProperty("boundaryKind", VmExpressionIr.FIELD_READ);
            row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, seed.epoch);
            row.addProperty("selectionPolicy",
                    READ_FROM_DEPENDENCY_POLICY);
            JsonArray arms = new JsonArray();
            List<String> owners = new ArrayList<>(partition.keySet());
            Collections.sort(owners);
            for (String owner : owners) {
                CaseInfo producer = partition.get(owner);
                JsonElement pathCondition = closedPathCondition(owner);
                if (pathCondition == null) {
                    gap("READ_FROM_WRITER_CASE_PC_MISSING", family,
                            "writer case has no closed local path condition: "
                                    + owner);
                    continue;
                }
                if (observationOwners.contains(owner)) {
                    for (JsonElement encoded : pathObservations(owner)) {
                        JsonObject observation = encoded.getAsJsonObject();
                        JsonObject arm = new JsonObject();
                        arm.addProperty("selector", optionalString(observation,
                                "selector"));
                        arm.addProperty("caseSelector", producer.selector);
                        arm.addProperty("caseOwner", producer.owner);
                        arm.addProperty("regionId", producer.region);
                        arm.addProperty("occurrenceId",
                                producer.occurrence);
                        copyObservationIdentity(observation, arm);
                        arm.add("pathCondition",
                                observation.get("pathCondition"));
                        arms.add(arm);
                    }
                } else {
                    JsonObject arm = new JsonObject();
                    arm.addProperty("selector", producer.selector);
                    arm.addProperty("caseSelector", producer.selector);
                    arm.addProperty("caseOwner", producer.owner);
                    arm.addProperty("regionId", producer.region);
                    arm.addProperty("occurrenceId", producer.occurrence);
                    stampExecutionScope(arm, producer);
                    arm.add("pathCondition", pathCondition);
                    arms.add(arm);
                }
            }
            row.add("arms", arms);
            JsonObject held = dependencies.putIfAbsent(family, row);
            if (held != null
                    && !semanticIdentity(held, "").equals(
                    semanticIdentity(row, ""))) {
                gap("READ_FROM_WRITER_CASE_AMBIGUOUS", family,
                        "writer-case dependency disagrees across"
                                + " observations");
            }
        }

        /**
         * Collapses equivalent executions of one local case after closing
         * all consumer anchors in its PC.  Distinct physical PCs refine the
         * value-independent case with observation selectors.
         */
        private JsonElement closedPathCondition(String owner) {
            if (closedPathConditions.containsKey(owner)) {
                return closedPathConditions.get(owner);
            }
            if (missingPathConditions.contains(owner)) return null;
            List<CaseInfo> observations = caseObservationsByOwner.get(owner);
            if (observations == null || observations.isEmpty()) {
                missingPathConditions.add(owner);
                return null;
            }
            List<CaseInfo> ordered = new ArrayList<>(observations);
            Collections.sort(ordered, Comparator.comparing(
                    CaseInfo::executionIdentity));
            Map<String, JsonElement> distinct = new LinkedHashMap<>();
            Map<String, String> identityByObservation =
                    new LinkedHashMap<>();
            for (CaseInfo info : ordered) {
                if (info.pathCondition == null) continue;
                JsonElement closed = rewriteElement(info.pathCondition,
                        info.sessionScope, info);
                String semantic = semanticIdentity(closed, owner);
                String held = identityByObservation.putIfAbsent(
                        info.observationSelector, semantic);
                if (held != null && !held.equals(semantic)) {
                    gap("LOCAL_CASE_OBSERVATION_AMBIGUOUS", owner,
                            "one physical case observation carries two path"
                                    + " conditions");
                    continue;
                }
                distinct.putIfAbsent(semantic, closed);
            }
            if (distinct.size() > 1) {
                observationOwners.add(owner);
            }
            if (distinct.isEmpty()) {
                missingPathConditions.add(owner);
                return null;
            }
            JsonElement result = distinct.values().iterator().next();
            closedPathConditions.put(owner, result);
            return result;
        }

        /** Exact PC alternatives for one value-independent local case. */
        private JsonArray pathObservations(String owner) {
            JsonArray result = new JsonArray();
            List<CaseInfo> observations = new ArrayList<>(
                    caseObservationsByOwner.getOrDefault(owner,
                            Collections.emptyList()));
            observations.sort(Comparator.comparing(
                    CaseInfo::executionIdentity));
            Set<String> emitted = new LinkedHashSet<>();
            for (CaseInfo observation : observations) {
                if (observation.pathCondition == null
                        || observation.observationSelector.isEmpty()
                        || !emitted.add(observation.observationSelector)) {
                    continue;
                }
                JsonObject encoded = new JsonObject();
                encoded.addProperty("selector",
                        observation.observationSelector);
                encoded.addProperty("caseSelector", observation.selector);
                encoded.addProperty(OBSERVATION_SELECTOR,
                        observation.observationSelector);
                encoded.addProperty(OBSERVATION_SCOPE,
                        observation.sessionScope);
                encoded.add("pathCondition", rewriteElement(
                        observation.pathCondition,
                        observation.sessionScope, observation));
                result.add(encoded);
            }
            if (result.size() == 0) {
                gap("LOCAL_CASE_OBSERVATION_SCOPE_MISSING", owner,
                        "replay-specific path conditions have no exact"
                                + " observation selector");
            }
            return result;
        }

        /**
         * Canonical identity for a PC shell whose expression nodes are Merkle
         * addressed.  This compares the same JSON content as the former full
         * render without serializing an expanded causal chain at every use.
         */
        private String semanticIdentity(JsonElement value, String caseOwner) {
            String owner = safe(caseOwner);
            Map<String, String> cached = semanticIdentities.get(value);
            String held = cached == null ? null : cached.get(owner);
            if (held != null) return held;
            String result = new ReplaySemanticHasher(owner, stableIdentities,
                    stableArms).identity(value);
            if (value != null && !value.isJsonNull()
                    && !value.isJsonPrimitive()) {
                semanticIdentities.computeIfAbsent(value,
                        ignored -> new LinkedHashMap<>()).put(owner, result);
            }
            return result;
        }

        /**
         * Cross-replay equality for a propagated value. The full expression
         * is retained for guarded SMT selection; this digest only
         * alpha-renames identities which the VM mints afresh on every replay.
         * In particular, a guarded read keeps its complete candidate values,
         * writer cases and cut shape while numeric event ids and rfN names are
         * represented by their roles inside that one read.
         */
        private static final class ReplaySemanticHasher {
            private final String rootOwner;
            private final Map<String, Map<String, String>> oopNames =
                    new LinkedHashMap<>();
            private final Map<JsonElement, Map<String, String>> memo =
                    new IdentityHashMap<>();
            /** Cross-root digests for subtrees free of allocated references. */
            private final Map<JsonElement, Map<String, String>> stable;
            private final Map<JsonElement, Map<String, String>> stableArms;
            /**
             * Counts every alpha name this root has read or minted. A subtree
             * that leaves it untouched did not depend on the naming order.
             */
            private long alphaReads;

            private ReplaySemanticHasher(String rootOwner,
                    Map<JsonElement, Map<String, String>> stable,
                    Map<JsonElement, Map<String, String>> stableArms) {
                this.rootOwner = safe(rootOwner);
                this.stable = stable;
                this.stableArms = stableArms;
            }

            private static String held(
                    Map<JsonElement, Map<String, String>> cache,
                    JsonElement value, String scope) {
                Map<String, String> scoped = cache.get(value);
                return scoped == null ? null : scoped.get(scope);
            }

            private static void keep(
                    Map<JsonElement, Map<String, String>> cache,
                    JsonElement value, String scope, String digest) {
                cache.computeIfAbsent(value,
                        ignored -> new LinkedHashMap<>()).put(scope, digest);
            }

            private String identity(JsonElement value) {
                return hash(value, rootOwner);
            }

            private String hash(JsonElement value, String owner) {
                if (value == null || value.isJsonNull()
                        || value.isJsonPrimitive()) {
                    return CanonicalJson.render(value);
                }
                String scope = safe(owner);
                // Every alpha-free digest is kept in both caches, so a hit
                // that only the private memo holds is one whose subtree read
                // the naming table.  Reusing it has to age the counter too,
                // or an ancestor would read its own descent as alpha-free
                // and publish a digest that only this root's naming order
                // justifies.
                String cached = held(stable, value, scope);
                if (cached != null) return cached;
                cached = held(memo, value, scope);
                if (cached != null) {
                    alphaReads++;
                    return cached;
                }
                long before = alphaReads;
                String result;
                if (value.isJsonArray()) {
                    StringBuilder encoded = new StringBuilder("[");
                    for (JsonElement child : value.getAsJsonArray()) {
                        appendFramed(encoded, hash(child, scope));
                    }
                    result = digest(encoded.append(']').toString());
                } else {
                    JsonObject object = value.getAsJsonObject();
                    result = SharedStateEvidence.claimsGuardedRead(object)
                            ? guardedRead(object, scope)
                            : ordinaryObject(object, scope);
                }
                keep(memo, value, scope, result);
                if (alphaReads == before) {
                    keep(stable, value, scope, result);
                }
                return result;
            }

            private String ordinaryObject(JsonObject object, String owner) {
                StringBuilder encoded = new StringBuilder("{");
                List<String> names = new ArrayList<>(object.keySet());
                Collections.sort(names);
                String type = optionalString(object, "_type");
                String expressionOwner = owner;
                if (ITE_TYPE.equals(type)) {
                    // Each arm's expression belongs to its producer case, not
                    // to the receiver which happens to reference the merge.
                    return caseMerge(object, owner);
                }
                for (String name : names) {
                    appendFramed(encoded, name);
                    JsonElement child = object.get(name);
                    if ("_exp".equals(name)
                            && "SymbolExpression".equals(type)
                            && child != null && child.isJsonPrimitive()) {
                        appendFramed(encoded, allocatedSymbol(
                                child.getAsString(), expressionOwner));
                    } else {
                        appendFramed(encoded, hash(child, expressionOwner));
                    }
                }
                return digest(encoded.append('}').toString());
            }

            private String caseMerge(JsonObject object, String owner) {
                StringBuilder encoded = new StringBuilder("{merge");
                List<String> names = new ArrayList<>(object.keySet());
                Collections.sort(names);
                for (String name : names) {
                    appendFramed(encoded, name);
                    if (!"arms".equals(name)) {
                        appendFramed(encoded, hash(object.get(name), owner));
                        continue;
                    }
                    JsonArray arms = array(object, name);
                    StringBuilder armList = new StringBuilder("[");
                    for (JsonElement element : arms) {
                        if (!element.isJsonObject()) {
                            appendFramed(armList, hash(element, owner));
                            continue;
                        }
                        JsonObject arm = element.getAsJsonObject();
                        String armOwner = first(optionalString(arm, "caseOwner"),
                                owner);
                        appendFramed(armList, mergeArm(arm, armOwner));
                    }
                    appendFramed(encoded,
                            digest(armList.append(']').toString()));
                }
                return digest(encoded.append('}').toString());
            }

            /**
             * One merge arm, hashed as an ordinary object under its producer
             * case. Shares the same alpha-free reuse rule as {@link #hash}.
             */
            private String mergeArm(JsonObject value, String owner) {
                String scope = safe(owner);
                String cached = held(stableArms, value, scope);
                if (cached != null) return cached;
                long before = alphaReads;
                String result = ordinaryObject(value, scope);
                if (alphaReads == before) {
                    keep(stableArms, value, scope, result);
                }
                return result;
            }

            private String guardedRead(JsonObject read, String owner) {
                JsonArray candidates = array(read, "candidates");
                StringBuilder encoded = new StringBuilder("{read");
                for (String name : new String[]{"_type", "_java_type",
                        "expressionAuthority", "writerSetComplete", READ_CHOICE_OWNER,
                        READ_CHOICE_OCCURRENCE_ID}) {
                    if (!read.has(name)) continue;
                    appendFramed(encoded, name);
                    appendFramed(encoded, hash(read.get(name), owner));
                }
                JsonObject location = object(read, "location");
                StringBuilder locationShape = new StringBuilder();
                appendFramed(locationShape, optionalString(location, "locationKind"));
                appendFramed(locationShape, CanonicalJson.render(
                        location.get("slot")));
                appendFramed(encoded, "location");
                appendFramed(encoded, digest(locationShape.toString()));
                StringBuilder arms = new StringBuilder("[");
                for (int index = 0; index < candidates.size(); index++) {
                    JsonElement element = candidates.get(index);
                    if (!element.isJsonObject()) {
                        appendFramed(arms, hash(element, owner));
                        continue;
                    }
                    appendFramed(arms, readCandidate(
                            element.getAsJsonObject(), owner, index));
                }
                appendFramed(encoded, "candidates");
                appendFramed(encoded, digest(arms.append(']').toString()));
                return digest(encoded.append('}').toString());
            }

            private String readCandidate(JsonObject candidate, String owner,
                                         int index) {
                String writerOwner = first(optionalString(candidate,
                        WRITER_CASE_OWNER), owner);
                StringBuilder encoded = new StringBuilder("{candidate");
                appendField(encoded, "selector", "arm:" + index);
                for (String name : new String[]{"regionId", "versionKind",
                        "volatileWrite", WRITER_CASE_FAMILY,
                        WRITER_CASE_OWNER, WRITER_CASE_SELECTOR,
                        WRITER_CASE_CLOSURE}) {
                    if (candidate.has(name)) {
                        appendField(encoded, name,
                                hash(candidate.get(name), writerOwner));
                    }
                }
                for (String name : new String[]{"expression", "pathGuard"}) {
                    if (candidate.has(name)) {
                        appendField(encoded, name,
                                hash(candidate.get(name), writerOwner));
                    }
                }
                return digest(encoded.append('}').toString());
            }

            private String allocatedSymbol(String raw, String owner) {
                String identity = VmExpressionIr.allocatedReferenceIdentity(
                        raw);
                if (identity.isEmpty() || identity.startsWith("map-state:")) {
                    return raw;
                }
                Map<String, String> names = oopNames.computeIfAbsent(
                        safe(owner), ignored -> new LinkedHashMap<>());
                String alpha = names.computeIfAbsent(identity,
                        ignored -> "o" + names.size());
                alphaReads++;
                return VmExpressionIr.alphaAllocatedReference(raw, alpha);
            }

            private static void appendField(StringBuilder encoded,
                                            String name, String value) {
                appendFramed(encoded, name);
                appendFramed(encoded, value);
            }

            private static String digest(String value) {
                return CanonicalJson.sha256(value);
            }
        }

        private static void appendFramed(StringBuilder target,
                                         String value) {
            String safeValue = value == null ? "" : value;
            target.append(safeValue.length()).append(':')
                    .append(safeValue);
        }

        private void gap(String reason, String subject, String detail) {
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", SCHEMA_VERSION);
            row.addProperty("kind", GAP_KIND);
            row.addProperty("authority", GAP_AUTHORITY);
            row.addProperty("reason", safe(reason));
            row.addProperty("subject", safe(subject));
            row.addProperty("detail", safe(detail));
            gaps.put(CanonicalJson.render(row), row);
        }

    }

    private static final class CaseInfo {
        private final String owner;
        private final String selector;
        private final String region;
        private final String occurrence;
        private final String task;
        private final String sessionScope;
        private final String epoch;
        private final JsonElement pathCondition;
        private final String observationSelector;

        private CaseInfo(String owner, String selector, String region,
                         String occurrence, String task,
                         String sessionScope, String epoch,
                         JsonElement pathCondition) {
            this.owner = safe(owner);
            this.selector = safe(selector);
            this.region = safe(region);
            this.occurrence = safe(occurrence);
            this.task = safe(task);
            this.sessionScope = safe(sessionScope);
            this.epoch = safe(epoch);
            this.pathCondition = pathCondition;
            this.observationSelector = this.sessionScope.isEmpty()
                    ? "" : observationSelector(this.owner,
                    executionIdentity());
        }

        private boolean sameLocalIdentity(CaseInfo other) {
            return selector.equals(other.selector)
                    && region.equals(other.region)
                    && occurrence.equals(other.occurrence);
        }

        private boolean sameExecution(CaseInfo other) {
            return sameLocalIdentity(other)
                    && task.equals(other.task)
                    && sessionScope.equals(other.sessionScope);
        }

        private String executionIdentity() {
            return sessionScope + "\n" + task + "\n" + occurrence;
        }
    }

    private static final class Family {
        private final String key;
        private final String kind;
        private final String epoch;
        private final String javaType;
        private final Map<String, List<Arm>> arms = new LinkedHashMap<>();

        private Family(String key, String kind, String epoch,
                       String javaType) {
            this.key = key;
            this.kind = kind;
            this.epoch = epoch;
            this.javaType = javaType;
        }

        private void add(Arm arm) {
            arms.computeIfAbsent(arm.producer.selector,
                    ignored -> new ArrayList<>()).add(arm);
        }
    }

    private static final class Arm {
        private final CaseInfo producer;
        private final String receiverOwner;
        private final String sessionScope;
        private final long eventId;
        private final JsonElement expression;

        private Arm(CaseInfo producer, String receiverOwner,
                    String sessionScope, long eventId,
                    JsonElement expression) {
            this.producer = producer;
            this.receiverOwner = safe(receiverOwner);
            this.sessionScope = safe(sessionScope);
            this.eventId = eventId;
            this.expression = expression;
        }

        private String identity() {
            return producer.owner + "\n" + receiverOwner + "\n"
                    + sessionScope + "\n" + eventId;
        }
    }

    private static final class ArmLineage {
        private final String family;
        private final String producerOwner;
        private final String receiverOwner;

        private ArmLineage(String family, CaseInfo producer,
                           String receiverOwner) {
            this.family = safe(family);
            this.producerOwner = producer == null ? "" : producer.owner;
            this.receiverOwner = safe(receiverOwner);
        }

        private boolean same(ArmLineage other) {
            return other != null && family.equals(other.family)
                    && producerOwner.equals(other.producerOwner)
                    && receiverOwner.equals(other.receiverOwner);
        }
    }

    private static final class DynamicKey {
        private final String scope;
        private final long event;

        private DynamicKey(String scope, long event) {
            this.scope = safe(scope);
            this.event = event;
        }

        @Override public boolean equals(Object other) {
            return other instanceof DynamicKey
                    && scope.equals(((DynamicKey) other).scope)
                    && event == ((DynamicKey) other).event;
        }
        @Override public int hashCode() {
            return 31 * scope.hashCode() + Long.valueOf(event).hashCode();
        }
        @Override public String toString() { return scope + ":" + event; }
    }

    /** One writer version of one VM location inside one replay session. */
    private static final class LocationVersionKey {
        private final String scope;
        private final String location;
        private final long version;

        private LocationVersionKey(String scope, String location,
                                   long version) {
            this.scope = safe(scope);
            this.location = safe(location);
            this.version = version;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof LocationVersionKey)) return false;
            LocationVersionKey key = (LocationVersionKey) other;
            return scope.equals(key.scope) && location.equals(key.location)
                    && version == key.version;
        }

        @Override public int hashCode() {
            int value = scope.hashCode();
            value = 31 * value + location.hashCode();
            return 31 * value + Long.valueOf(version).hashCode();
        }

        @Override public String toString() {
            return scope + ":" + location + ":v" + version;
        }
    }

    /** One candidate version inside one exact replay-local guarded read. */
    private static final class ReadCandidateKey {
        private final String scope;
        private final long readEvent;
        private final long version;

        private ReadCandidateKey(String scope, long readEvent, long version) {
            this.scope = safe(scope);
            this.readEvent = readEvent;
            this.version = version;
        }

        @Override public boolean equals(Object other) {
            if (!(other instanceof ReadCandidateKey)) return false;
            ReadCandidateKey key = (ReadCandidateKey) other;
            return scope.equals(key.scope) && readEvent == key.readEvent
                    && version == key.version;
        }

        @Override public int hashCode() {
            int value = scope.hashCode();
            value = 31 * value + Long.valueOf(readEvent).hashCode();
            return 31 * value + Long.valueOf(version).hashCode();
        }

        @Override public String toString() {
            return scope + ":read=" + readEvent + ":writer=" + version;
        }
    }

    private static final class FieldRead {
        private final String family;
        private final CaseInfo producer;
        private final String receiverOwner;
        private final String scope;
        private final String epoch;
        private final int candidateCount;
        private final String stableLocation;
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final String consumerSiteId;
        private final int consumerSiteOccurrence;

        private FieldRead(String family, CaseInfo producer,
                          String receiverOwner, String scope, String epoch,
                          int candidateCount,
                          String stableLocation, JsonObject carrier,
                          JsonObject read) {
            this.family = family;
            this.producer = producer;
            this.receiverOwner = safe(receiverOwner);
            this.scope = safe(scope);
            this.epoch = safe(epoch);
            this.candidateCount = candidateCount;
            this.stableLocation = safe(stableLocation);
            this.declaringClass = optionalString(carrier, "declaringClass");
            this.fieldName = optionalString(carrier, "fieldName");
            this.descriptor = optionalString(carrier, "descriptor");
            this.consumerSiteId = optionalString(read,
                    SharedStateEvidence.CONSUMER_SITE_ID);
            this.consumerSiteOccurrence = optionalInteger(read,
                    SharedStateEvidence.CONSUMER_SITE_OCCURRENCE, -1);
        }

        private boolean sameLineage(FieldRead other) {
            return family.equals(other.family)
                    && receiverOwner.equals(other.receiverOwner)
                    && scope.equals(other.scope)
                    && epoch.equals(other.epoch)
                    && candidateCount == other.candidateCount
                    && stableLocation.equals(other.stableLocation)
                    && declaringClass.equals(other.declaringClass)
                    && fieldName.equals(other.fieldName)
                    && descriptor.equals(other.descriptor)
                    && consumerSiteId.equals(other.consumerSiteId)
                    && consumerSiteOccurrence == other.consumerSiteOccurrence
                    && (producer == null ? other.producer == null
                    : other.producer != null
                    && producer.owner.equals(other.producer.owner));
        }
    }

    /** Builds the exact case evidence view without consulting graph ports. */
    private static List<JsonObject> caseRows(
            Collection<RelationSummary> summaries, JsonObject fatal) {
        List<JsonObject> rows = new ArrayList<>();
        if (summaries != null) {
            for (RelationSummary summary : summaries) {
                JsonObject top = summary.immutableJson();
                JsonObject row = summary.pathCaseView();
                String occurrence = optionalString(row, "occurrenceId");
                row.addProperty("toOccurrenceId", occurrence);
                row.addProperty("regionId", summary.regionId());
                row.addProperty("caseRegionId", summary.regionId());
                row.addProperty("sourceKey", summary.sourceKey());
                row.addProperty("taskId", first(optionalString(row, "taskId"),
                        first(optionalString(row, "sourceTaskId"),
                                optionalString(top, "taskId"))));
                row.addProperty("boundarySessionScope", first(
                        optionalString(row, "boundarySessionScope"),
                        optionalString(top, "boundarySessionScope")));
                row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, first(
                        optionalString(row, VmExpressionIr.TOPOLOGY_EPOCH),
                        optionalString(top, VmExpressionIr.TOPOLOGY_EPOCH)));
                String owner = LocalCaseIdentity.owner(top);
                LocalCaseIdentity.stamp(row, owner);
                rows.add(row);
            }
        }
        if (fatal != null) {
            JsonArray paths = array(fatal, "paths");
            for (int index = 0; index < paths.size(); index++) {
                if (!paths.get(index).isJsonObject()) continue;
                JsonObject row = JsonFields.shallowCopy(
                        paths.get(index).getAsJsonObject());
                String plannedOccurrence = optionalString(fatal, "occurrenceId");
                String occurrence = first(optionalString(row, "occurrenceId"),
                        plannedOccurrence);
                row.addProperty("toOccurrenceId", occurrence);
                row.addProperty("occurrenceId", occurrence);
                row.addProperty("regionId", optionalString(fatal, "regionId"));
                row.addProperty("caseRegionId", optionalString(fatal, "regionId"));
                row.addProperty("sourceTaskId", first(
                        optionalString(row, "sourceTaskId"),
                        first(optionalString(fatal, "sourceTaskId"),
                                optionalString(fatal, "taskId"))));
                row.addProperty("taskId", first(optionalString(row, "taskId"),
                        optionalString(fatal, "taskId")));
                row.addProperty("boundarySessionScope", first(
                        optionalString(row, "boundarySessionScope"),
                        optionalString(fatal, "boundarySessionScope")));
                row.addProperty(VmExpressionIr.TOPOLOGY_EPOCH, first(
                        optionalString(row, VmExpressionIr.TOPOLOGY_EPOCH),
                        optionalString(fatal, VmExpressionIr.TOPOLOGY_EPOCH)));
                String owner = LocalCaseIdentity.owner(
                        optionalString(fatal, "regionId"), occurrence,
                        first(optionalString(row, "caseId"),
                                "TARGET_PATH." + index), index);
                LocalCaseIdentity.stamp(row, owner);
                rows.add(row);
            }
        }
        return rows;
    }

    private static boolean evidenceField(String field) {
        return "edgeBindings".equals(field)
                || "seedReplayContract".equals(field)
                || "manualSymbolicInputObservations".equals(field)
                || VmHandoffEvidence.FIELD.equals(field)
                || SharedStateEvidence.RECORDED_FIELD.equals(field)
                || SymbolicSourceEvidence.FIELD.equals(field)
                ;
    }

    private static JsonObject missingReference(String family) {
        JsonObject row = new JsonObject();
        row.addProperty("_type",
                VmExpressionIr.CONSUMER_BOUNDARY_REFERENCE_TYPE);
        row.addProperty(VmExpressionIr.FAMILY_KEY, family);
        return row;
    }

    private static String boundaryFault(JsonElement encoded, String kind,
                                        long eventId) {
        if (VmExpressionIr.isConsumerBoundaryReference(encoded)) {
            JsonObject raw = new JsonObject();
            for (Map.Entry<String, JsonElement> field
                    : encoded.getAsJsonObject().entrySet()) {
                raw.add(field.getKey(), field.getValue());
            }
            raw.addProperty("_type", VmExpressionIr.CONSUMER_BOUNDARY_TYPE);
            return VmExpressionIr.consumerBoundaryFault(raw, kind, eventId);
        }
        return VmExpressionIr.consumerBoundaryFault(encoded, kind, eventId);
    }

    private static String scopeOf(JsonObject row) {
        return row == null ? "" : optionalString(row, "boundarySessionScope");
    }

    private static String executionKey(String scope, String task,
                                       String occurrence) {
        return safe(scope) + "\u0000" + safe(task) + "\u0000"
                + safe(occurrence);
    }

    /** One atom for a concrete case observation inside a replay session. */
    static String observationSelector(String owner,
                                      String executionIdentity) {
        if (safe(owner).isEmpty() || safe(executionIdentity).isEmpty()) {
            return "";
        }
        return "case_observation__" + CanonicalJson.sha256(
                owner + "\n" + executionIdentity);
    }

    /** Removes VM object ids while retaining the declared field/read slot. */
    private static String stableReadLocation(JsonObject record,
                                             JsonObject read,
                                             CaseInfo readerCase) {
        JsonObject carrier = object(record, "carrier");
        String declared = optionalString(carrier, "declaringClass") + "#"
                + optionalString(carrier, "fieldName");
        long plannedReceiver = optionalLongInteger(carrier, "receiverObjectId", 0L);
        String location = optionalString(record, "locationKey");
        String kind = SharedStateEvidence.locationKindOf(location);
        int slot = location.lastIndexOf('#');
        String stableSlot = slot < 0 ? "" : location.substring(slot + 1);
        if (!"#".equals(declared)
                && !declared.startsWith("#")
                && !declared.endsWith("#")) {
            String consumerSite = optionalString(read,
                    SharedStateEvidence.CONSUMER_SITE_ID);
            int consumerOccurrence = optionalInteger(read,
                    SharedStateEvidence.CONSUMER_SITE_OCCURRENCE, -1);
            if (!consumerSite.isEmpty() && consumerOccurrence > 0) {
                return kind + "/consumer:"
                        + CanonicalJson.sha256(consumerSite) + "#"
                        + consumerOccurrence + "/" + declared + "#"
                        + stableSlot;
            }
            if (plannedReceiver <= 0L) {
                // Reads performed inside an uninstrumented accessor (for
                // example AtomicInteger RMW) have no replay access site, and
                // a trace may have no stable receiver id for the accessor's
                // private field.  The exact reader local case is still an
                // authoritative replay-independent owner.  Partition this
                // fallback by that case and the declared field/slot; the
                // caller's per-location ordinal distinguishes repeated reads
                // within the same local path.  Missing case or structural
                // field identity remains a hard gap.
                String owner = readerCase == null ? "" : readerCase.owner;
                String structural = stableWriterLocation(record);
                return owner.isEmpty() || structural.isEmpty() ? ""
                        : structural + "/case:"
                        + CanonicalJson.sha256(owner);
            }
            return kind + "/receiver:" + plannedReceiver + "/"
                    + declared + "#" + stableSlot;
        }
        // Fail-closed fallback for carrier kinds without a declared field:
        // preserve the kind and structural slot only, never the owner rid or
        // canonical @receiver object id.
        return kind + "/slot#" + stableSlot;
    }

    /** Stable output position for one writer occurrence and local ordinal. */
    private static String stableWriterLocation(JsonObject record) {
        JsonObject carrier = object(record, "carrier");
        String declaring = optionalString(carrier, "declaringClass");
        String field = optionalString(carrier, "fieldName");
        String descriptor = JavaPrimitiveSmtSemantics.javaTypeDescriptor(
                optionalString(carrier, "descriptor"));
        String location = optionalString(record, "locationKey");
        String kind = SharedStateEvidence.locationKindOf(location);
        int slot = location.lastIndexOf('#');
        String stableSlot = slot < 0 ? "" : location.substring(slot + 1);
        if (!declaring.isEmpty() && !field.isEmpty()) {
            return kind + "/" + declaring + "#" + field + ":"
                    + descriptor + "#" + stableSlot;
        }
        return kind.isEmpty() || stableSlot.isEmpty()
                ? "" : kind + "/slot#" + stableSlot;
    }

    private static String first(String value, String fallback) {
        return value == null || value.isEmpty() ? safe(fallback) : value;
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    /**
     * Returns map values in their already-computed stable-key order.
     *
     * <p>Ledger and dependency values can contain the complete propagated
     * expression and path condition.  Rendering those trees again inside a
     * comparator made sorting O(n log n) full-tree serializations.  Their map
     * keys are the stable family identity (and a canonical gap identity), so
     * ordering the compact keys provides the same deterministic output without
     * repeatedly walking the symbolic trees.</p>
     */
    private static List<JsonObject> orderedValues(
            Map<String, JsonObject> rows) {
        List<String> keys = new ArrayList<>(rows.keySet());
        Collections.sort(keys);
        List<JsonObject> result = new ArrayList<>();
        for (String key : keys) result.add(rows.get(key));
        return Collections.unmodifiableList(result);
    }
}
