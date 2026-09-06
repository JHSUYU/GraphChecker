package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.binary;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.candidate;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.constant;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.event;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.ledgerEnvelope;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.occurrenceOf;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.sum;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.symbol;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.unknownCandidate;

/**
 * The VM envelopes a selected map publishes, in the shape the custom JDK
 * serializes them.
 *
 * <p>A whole-map state travels in the same {@code SHARED_FIELD_VERSIONS}
 * envelope a field does, at the same schema version, with {@code MAP_STATE}
 * as its location kind and the reserved whole-state slot. What differs is the
 * shape of one expression: a version carries an immutable
 * {@code ContainerRelation} state instead of a scalar value, and a guarded
 * query's arm is that state read at the queried key. These builders therefore
 * reuse the scalar fixtures wherever the shape is genuinely the same, so a
 * test that passes here is a test against one admission rule and not against
 * a second one written for maps.</p>
 */
final class RecordedMapStateFixtures {

    static final String MAP_EDGE = "EDGE.MAP";

    /** The selected map's own session identity. */
    static final long MAP_OWNER = 9L;
    /** The location key its whole state is addressed by. */
    static final String MAP_LOCATION =
            SharedStateEvidence.LOCATION_KIND_MAP_STATE + "/" + MAP_OWNER
                    + "#" + SharedStateEvidence.MAP_STATE_SLOT;
    /** The declared field the selected map is held in. */
    static final String MAP_FIELD = "example.Keys#allKeys";

    static final long INITIAL_VERSION = 30L;
    static final long WRITER_A_VERSION = 31L;
    static final long WRITER_B_VERSION = 32L;
    static final long QUERY_EVENT = 41L;

    static final String TARGET_OCCURRENCE = "REGION.0@Test#call30";
    static final String PRODUCER_OCCURRENCE = "REGION.1@Test#call20";
    static final String SOURCE_KEY = "TEST_DRIVER/test#epoch0";

    private RecordedMapStateFixtures() {
    }

    // ----- container expressions ------------------------------------------

    /** The map identity a state chain is rooted in. */
    static JsonObject mapReference(String name) {
        JsonObject reference = new JsonObject();
        reference.addProperty("_type", "SymbolExpression");
        reference.addProperty("_java_type", "Ljava/util/Map;");
        reference.addProperty("_exp", name);
        return reference;
    }

    private static JsonObject relation(String operation, JsonElement receiver,
                                       String javaType,
                                       JsonElement... arguments) {
        JsonObject node = new JsonObject();
        node.addProperty("_type", ContainerSmtCodec.EXPRESSION_TYPE);
        node.addProperty("_java_type", javaType);
        node.addProperty("shape", "ASSOCIATIVE");
        node.addProperty("operation", operation);
        if (receiver != null) node.add("receiver", receiver);
        JsonArray list = new JsonArray();
        for (JsonElement argument : arguments) list.add(argument);
        node.add("arguments", list);
        return node;
    }

    /** {@code STATE(m)}: the unconstrained state the map started in. */
    static JsonObject state(String name) {
        return relation("STATE", mapReference(name), "Ljava/util/Map;");
    }

    /** {@code PUT(receiver, key, value)}: one immutable whole-map state. */
    static JsonObject put(JsonElement receiver, JsonElement key,
                          JsonElement value) {
        return relation("PUT", receiver, "Ljava/util/Map;", key, value);
    }

    /** {@code REMOVE(receiver, key)}: the state after one removal. */
    static JsonObject remove(JsonElement receiver, JsonElement key) {
        return relation("REMOVE", receiver, "Ljava/util/Map;", key);
    }

    /** {@code READ(state, key)}: the query one arm applies to one state. */
    static JsonObject query(JsonElement receiver, JsonElement key) {
        return relation("READ", receiver, "I", key);
    }

    // ----- version store ---------------------------------------------------

    /** One published whole-map state, as the version store serializes it. */
    static JsonObject stateVersion(long fieldVersionId, String versionKind,
                                   String regionId, String taskId,
                                   JsonElement value, JsonElement pathGuard) {
        JsonObject version = new JsonObject();
        version.addProperty("fieldVersionId", fieldVersionId);
        version.addProperty("versionKind", versionKind);
        version.addProperty("writerContextId", 100L + fieldVersionId);
        version.addProperty("writerJavaThreadId", 200L + fieldVersionId);
        version.addProperty("writerStep", fieldVersionId);
        version.addProperty("regionId", regionId);
        version.addProperty("taskId", taskId);
        version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                RecordedSharedStateFixtures.TEST_SOURCE);
        version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                occurrenceOf(regionId));
        version.addProperty("volatileWrite", false);
        // A whole map has no comparable concrete fingerprint, so two writers
        // that installed equal states stay two candidates.
        version.addProperty("fingerprintKind", "NONE");
        version.addProperty("fingerprint", 0L);
        version.add("expression", value);
        version.add("pathGuard", pathGuard);
        return version;
    }

    static JsonObject mapVersionsEnvelope(JsonArray versions, JsonArray reads,
                                          boolean writerSetComplete) {
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", MAP_OWNER);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        JsonObject envelope = new JsonObject();
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("kind",
                SharedStateEvidence.VERSIONS_ENVELOPE_KIND);
        envelope.addProperty("selected", true);
        envelope.add("location", location);
        envelope.addProperty("writerSetComplete", writerSetComplete);
        envelope.add("versions", versions);
        envelope.add("reads", reads);
        return envelope;
    }

    /** The state each competing writer installed. */
    static JsonObject writerAState() {
        return put(state("M_MAP_allKeys"), constant(4242),
                sum(symbol("A"), constant(1)));
    }

    /**
     * Writer B's state.
     *
     * <p>Equal values install exactly writer A's state, which is the case no
     * value comparison can separate. Otherwise B puts its own distinctive
     * member and then removes the queried key, so its state differs from A's
     * in a way the lowered query has to show - and so the supported
     * {@code remove} mutation is exercised beside {@code put}.</p>
     */
    static JsonObject writerBState(boolean equalValues) {
        return equalValues
                ? put(state("M_MAP_allKeys"), constant(4242),
                sum(symbol("A"), constant(1)))
                : remove(put(state("M_MAP_allKeys"), constant(4242),
                constant(777)), constant(4242));
    }

    /**
     * Two competing mutations of one selected map and one query of it.
     *
     * <p>{@code equalValues} installs the <em>same</em> state from both
     * writers, which is the case a value comparison cannot separate and a
     * read-from choice still must.</p>
     */
    static JsonObject twoWriterMapEnvelope(boolean equalValues,
                                           boolean writerSetComplete) {
        JsonArray versions = new JsonArray();
        versions.add(stateVersion(WRITER_A_VERSION, "STATE_PUT",
                "REGION.writerA", "TASK.a", writerAState(), null));
        versions.add(stateVersion(WRITER_B_VERSION,
                equalValues ? "STATE_PUT" : "STATE_REMOVE", "REGION.writerB",
                "TASK.b", writerBState(equalValues),
                RecordedSharedStateFixtures.guard("G")));
        JsonArray reads = new JsonArray();
        reads.add(mapQueryRecord());
        return mapVersionsEnvelope(versions, reads, writerSetComplete);
    }

    /** The read record a guarded map query leaves in the version store. */
    static JsonObject mapQueryRecord() {
        JsonObject read = RecordedSharedStateFixtures.read(QUERY_EVENT,
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L, 2);
        // A guarded map query records no value observation at all: the
        // concrete member it returned is a fact about one entry, not about
        // the whole state a writer installed, so it cannot rule a writer out.
        read.addProperty("observedFingerprintKind", "NONE");
        read.addProperty("observedFingerprint", 0L);
        read.addProperty("regionId", "REGION.0");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                TARGET_OCCURRENCE);
        return read;
    }

    /** One admitted map-state record, joined to the field holding the map. */
    static JsonObject mapVersionsRecord(JsonObject envelope) {
        JsonObject record = SharedStateEvidence.versionsRecord(
                SharedStateEvidence.locationKey(envelope), envelope,
                RecordedSharedStateFixtures.identity("REGION.reader", 1L));
        JsonObject carrier = new JsonObject();
        carrier.addProperty("kind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        carrier.addProperty("declaringClass",
                MAP_FIELD.substring(0, MAP_FIELD.indexOf('#')));
        carrier.addProperty("fieldName",
                MAP_FIELD.substring(MAP_FIELD.indexOf('#') + 1));
        carrier.addProperty("descriptor", "Ljava/util/Map;");
        carrier.addProperty("index", -1);
        carrier.addProperty("fieldKey", MAP_FIELD + ":Ljava/util/Map;");
        record.add("carrier", carrier);
        return record;
    }

    // ----- the guarded map query -------------------------------------------

    /**
     * The guarded read-from node the VM attaches to an undecided map query.
     *
     * <p>Each arm is that writer's own state read at the queried key, which
     * is the whole difference between a scalar arm and a container arm: two
     * writers who installed different states answer differently even where
     * the member they wrote is equal.</p>
     */
    static JsonObject twoWriterGuardedMapRead(boolean equalValues) {
        JsonArray candidates = new JsonArray();
        JsonObject first = candidate("rf1", WRITER_A_VERSION,
                query(writerAState(), constant(4242)), null, QUERY_EVENT,
                WRITER_B_VERSION);
        first.addProperty("regionId", "REGION.writerA");
        JsonObject second = candidate("rf2", WRITER_B_VERSION,
                query(writerBState(equalValues), constant(4242)),
                RecordedSharedStateFixtures.guard("G"), QUERY_EVENT,
                WRITER_A_VERSION);
        second.addProperty("regionId", "REGION.writerB");
        candidates.add(first);
        candidates.add(second);
        candidates.add(unknownCandidate(QUERY_EVENT,
                "M_I_unknownWriter_" + MAP_OWNER + "_"
                        + SharedStateEvidence.MAP_STATE_SLOT + "_r"
                        + QUERY_EVENT));
        return guardedMapRead(candidates, true);
    }

    static JsonObject guardedMapRead(JsonArray candidates,
                                     boolean writerSetComplete) {
        JsonObject location = new JsonObject();
        location.addProperty("ownerSymRid", MAP_OWNER);
        location.addProperty("slot", SharedStateEvidence.MAP_STATE_SLOT);
        location.addProperty("locationKind",
                SharedStateEvidence.LOCATION_KIND_MAP_STATE);
        JsonArray selectors = new JsonArray();
        for (JsonElement element : candidates) {
            selectors.add(element.getAsJsonObject().get("selector")
                    .getAsString());
        }
        JsonObject node = new JsonObject();
        node.addProperty("_type", SharedStateEvidence.GUARDED_READ_TYPE);
        node.addProperty("_java_type", "I");
        node.addProperty("resolution",
                SharedStateEvidence.RESOLUTION_GUARDED);
        node.addProperty("reason", "AMBIGUOUS_WRITERS");
        node.addProperty("expressionAuthority",
                SharedStateEvidence.GUARDED_READ_AUTHORITY);
        node.addProperty("readEventId", QUERY_EVENT);
        node.add("location", location);
        node.addProperty("writerSetComplete", writerSetComplete);
        node.add("exactlyOne", selectors);
        node.add("candidates", candidates);
        node.add("ite", selectionTerm(candidates, 0));
        return node;
    }

    private static JsonElement selectionTerm(JsonArray candidates,
                                             int index) {
        JsonObject candidate = candidates.get(index).getAsJsonObject();
        if (index + 1 == candidates.size()) {
            return candidate.get("expression");
        }
        JsonObject ite = new JsonObject();
        ite.addProperty("_type", "IteExpression");
        ite.addProperty("selector",
                candidate.get("selector").getAsString());
        ite.add("then", candidate.get("expression"));
        ite.add("else", selectionTerm(candidates, index + 1));
        return ite;
    }

    /** Two map mutations and the query, in one acyclic order domain. */
    static JsonObject mapLedger() {
        JsonArray events = new JsonArray();
        events.add(event(WRITER_A_VERSION, "FIELD_WRITE", 101L,
                "REGION.writerA", MAP_OWNER));
        events.add(event(WRITER_B_VERSION, "FIELD_WRITE", 102L,
                "REGION.writerB", MAP_OWNER));
        events.add(event(QUERY_EVENT, "FIELD_READ", 103L, "REGION.0",
                MAP_OWNER));
        JsonArray order = new JsonArray();
        return ledgerEnvelope(events, order);
    }


    /** One {@code recordedSharedState} member carrying map-state evidence. */
    static JsonObject recordedMapMember(JsonObject envelope) {
        return SharedStateEvidence.recorded(
                Collections.singletonList(mapVersionsRecord(envelope)),
                SharedStateEvidence.ledgerRecord(mapLedger(),
                        RecordedSharedStateFixtures.identity("REGION.reader",
                                1L)));
    }

    // ----- composed golden --------------------------------------------------

    /**
     * The two-writer map query, composed through the real composer.
     *
     * <p>Nothing here is a stand-in: the formula the assertions read is the
     * one {@link ConcolicSmtComposer} emitted from these envelopes.</p>
     */
    static ConcolicSmtComposer.Result composedMapGolden(
            Path directory, boolean equalValues, boolean writerSetComplete)
            throws Exception {
        JsonObject envelope = twoWriterMapEnvelope(equalValues,
                writerSetComplete);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject guarded = twoWriterGuardedMapRead(equalValues);
        if (!writerSetComplete) {
            guarded.addProperty("writerSetComplete", false);
        }
        SharedStateEvidence.normalizeGuards(guarded);
        return composed(directory, envelope,
                binary(guarded, "==", constant(1)));
    }


    /**
     * The same composition over any envelope and target predicate, so a test
     * can vary one recorded fact and read the effect on the real formula.
     */
    static ConcolicSmtComposer.Result composed(Path directory,
                                               JsonObject envelope,
                                               JsonObject targetPredicate)
            throws Exception {
        JsonObject recordedEnvelope = envelope.deepCopy();
        for (JsonElement element : recordedEnvelope.getAsJsonArray(
                "versions")) {
            JsonObject version = element.getAsJsonObject();
            version.addProperty("regionId", "REGION.1");
            version.addProperty("taskId", "TASK.MAP");
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    SOURCE_KEY);
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    PRODUCER_OCCURRENCE);
        }
        JsonObject firstHop = binding();
        firstHop.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_CANDIDATE);
        firstHop.remove(RecordedReadFrom.EDGE_UNKNOWN_ARM);
        firstHop.remove("locationKey");
        RelationSummary producer = withRecordedMapState(
                producerSummary(firstHop), recordedEnvelope);
        targetPredicate.getAsJsonObject().getAsJsonObject("_left")
                .addProperty("recordedEventScope",
                        RecordedSessionModel.caseOwner("REGION.1",
                                PRODUCER_OCCURRENCE, "CASE.MAP", 0));
        Files.createDirectories(directory);
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaries = directory.resolve("summaries.jsonl");
        Path plan = directory.resolve("runtime_plan.jsonl");
        Path output = directory.resolve("candidate.smt2");
        Path manifest = directory.resolve("composed_smt_manifest.json");
        JsonObject query = fatalQuery(targetPredicate, firstHop);
        write(fatal, query + "\n");
        write(summaries, producer.toJson() + "\n");
        write(plan, RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", false, true))));
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(new String[]{
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaries.toString(),
                        "--runtime-plan", plan.toString(),
                        "--output", output.toString(),
                        "--manifest", manifest.toString(),
                        "--fatal-region", "REGION.0",
                        "--occurrence-id", TARGET_OCCURRENCE}));
    }

    private static RelationSummary withRecordedMapState(
            RelationSummary summary, JsonObject envelope) {
        JsonObject row = summary.toJson();
        row.getAsJsonObject("regionRelation").getAsJsonArray("cases")
                .get(0).getAsJsonObject().add(
                        SharedStateEvidence.RECORDED_FIELD,
                        recordedMapMember(envelope));
        return RelationSummary.decode(row);
    }

    private static JsonObject binding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", MAP_EDGE);
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("toRegion", "REGION.0");
        binding.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        binding.addProperty("toOccurrenceId", TARGET_OCCURRENCE);
        binding.addProperty("fromOutputPort", "REGION.1.out.0");
        binding.addProperty("toInputPort", "REGION.0.in.0");
        binding.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        binding.addProperty("writerLaneId", "lane.writer");
        binding.addProperty("readerLaneId", "lane.reader");
        binding.addProperty("programOrderRequired", false);
        binding.addProperty("writerEventSeq", 20);
        binding.addProperty("readerEventSeq", 30);
        binding.addProperty("receiverObjectId", 7);
        binding.addProperty(RecordedReadFrom.EDGE_PROVENANCE,
                RecordedReadFrom.PROVENANCE_GUARDED);
        binding.addProperty(RecordedReadFrom.EDGE_UNKNOWN_ARM,
                SharedStateEvidence.UNKNOWN_WRITER_SELECTOR);
        binding.addProperty("locationKey", MAP_LOCATION);
        return binding;
    }

    private static RelationSummary producerSummary(JsonObject firstHop) {
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1",
                java.util.Collections.singletonList("REGION.1.out.0"),
                "REGION.1.out.0", "<Test: int output>", "REGION_OUTPUT",
                "int", outputSlice());
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", RelationSummary.SCHEMA_VERSION);
        row.addProperty("kind", RelationSummary.KIND);
        row.addProperty("summaryId", "SUMMARY.MAP");
        row.addProperty("sourceKey", SOURCE_KEY);
        row.addProperty("regionId", "REGION.1");
        row.addProperty("occurrenceId", PRODUCER_OCCURRENCE);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(row);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray bindings = new JsonArray();
        bindings.add(firstHop.deepCopy());
        row.add("edgeBindings", bindings);
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE.MAP");
        path.addProperty("occurrenceId", PRODUCER_OCCURRENCE);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        path.addProperty("sourceTaskId", "TASK.MAP");
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", constant(10));
        path.add("outputExpressions", outputs);
        JsonArray cases = new JsonArray();
        cases.add(path);
        JsonObject relation = new JsonObject();
        relation.addProperty("schemaVersion", 1);
        relation.addProperty("kind", "GUARDED_PATH_MERGE");
        relation.add("cases", cases);
        row.add("regionRelation", relation);
        row.addProperty("relationallyComplete", true);
        return RelationSummary.decode(row);
    }


    private static JsonObject outputSlice() {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.1.out.0");
        slice.addProperty("outputCell", "<Test: int output>");
        JsonArray inputs = new JsonArray();
        inputs.add("REGION.1.in.0");
        slice.add("inputPorts", inputs);
        for (String member : new String[]{"sites", "staticSites", "methods",
                "captureBindings", "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        JsonArray causalEdges = new JsonArray();
        causalEdges.add(MAP_EDGE);
        slice.add("causalEdgeIds", causalEdges);
        return slice;
    }

    private static JsonObject fatalQuery(JsonObject targetPredicate,
                                         JsonObject firstHop) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion",
                TargetReachPathQueryBuilder.SCHEMA_VERSION);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("queryKey", "QUERY.RECORDED.MAP.STATE");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", TARGET_OCCURRENCE);
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("targetOccurrence", 1);
        fatal.addProperty("requiredTakenOutcome", false);
        fatal.addProperty("constraintAuthority", "RECORDED_TARGET_PREFIX_V1");
        JsonArray constraints = new JsonArray();
        constraints.add(targetPredicate);
        JsonObject path = new JsonObject();
        path.add("constraints", constraints);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        path.addProperty("desiredTakenOutcome", false);
        path.addProperty(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
                TargetReachPathQueryBuilder.SOURCE_TARGET_REACH_EVENT);
        path.addProperty("fatalBranchConditionAuthority",
                TargetReachPathQueryBuilder.SOURCE_FATAL_BRANCH_AUTHORITY);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", "<Test: void consume()>#u1");
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        path.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        JsonArray paths = new JsonArray();
        paths.add(path);
        fatal.add("paths", paths);
        fatal.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                new JsonArray());
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization", "IDENTITY");
        BranchWitness witness = BranchWitness.vmPc(
                "<Test: void consume()>#u1", "<Test: void consume()>", 1, 1,
                true, BranchPredicateAlgebra.complement(targetPredicate),
                0, metadata);
        path.add(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS,
                witness.toJson());
        fatal.add("seedReplayContract", BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(), witness).toJson());
        LoopBoundPolicy.cfgBackedges(8).writeTo(fatal);
        JsonArray selected = new JsonArray();
        selected.add(firstHop.deepCopy());
        fatal.add("selectedTargetBindings", selected);
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", TARGET_OCCURRENCE);
        fatal.add("symbolicContext", context);
        return fatal;
    }

    private static JsonObject region(String id, boolean hasInput,
                                     boolean hasOutput) {
        JsonObject region = new JsonObject();
        region.addProperty("schemaVersion", 3);
        region.addProperty("kind", "SYMBOLIC_REGION");
        region.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (hasInput) inputs.add(port(id + ".in.0", "input"));
        region.add("symbolicInputs", inputs);
        JsonArray outputs = new JsonArray();
        if (hasOutput) outputs.add(port(id + ".out.0", "output"));
        region.add("outputs", outputs);
        return region;
    }


    private static JsonObject port(String id, String role) {
        JsonObject port = new JsonObject();
        port.addProperty("portId", id);
        port.addProperty("cell", "<Test: int " + role + ">");
        port.addProperty("javaType", "int");
        return port;
    }


    private static void write(Path path, String content) throws Exception {
        Files.write(path, content.getBytes(StandardCharsets.UTF_8));
    }
}
