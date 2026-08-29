package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import edu.uva.liftlab.graphchecker.contract.RelationSummary;
import edu.uva.liftlab.graphchecker.contract.RuntimePlanArtifact;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.guardedMapRead;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.mapVersionsEnvelope;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.mapVersionsRecord;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.put;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.query;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.state;
import static edu.uva.liftlab.graphchecker.concolic.RecordedMapStateFixtures.stateVersion;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.binary;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.candidate;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.constant;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.edge;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.event;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.identity;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.ledgerEnvelope;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.symbol;
import static edu.uva.liftlab.graphchecker.concolic.RecordedSharedStateFixtures.unknownCandidate;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The causal-reach ranking of the fatal disjuncts.
 *
 * <p>A target that can reach its failure by more than one recorded path
 * leaves the composer a disjunction, and a disjunction asks the weakest
 * question there is: "can this fail at all".  When the paths differ in
 * <em>what the failing read was keyed on</em> - one on a value another node
 * handed this one, the other on something purely local - the causal question
 * is the first, and the composer says so by pinning that path.</p>
 *
 * <p>Four claims are pinned here.  The rule fires when exactly one disjunct
 * is keyed on a transported value; it refuses in each of the three ways it
 * can refuse - one disjunct, no disjunct reaching across a node, every
 * disjunct reaching alike - and in every refusal the emitted formula is the
 * formula it would have been.  That last property is what keeps a
 * single-read regression target inert.</p>
 */
public class CausalWitnessPinTest {

    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    private static final long LOCAL_READ = 41L;
    private static final long HANDED_READ = 42L;
    private static final long WRITER_A = 31L;
    private static final long WRITER_B = 32L;
    /** The value the fixture's other node hands this one. */
    private static final String HANDED_KEY = "HANDED_KEY";
    private static final long EXPORT_EVENT = 51L;
    private static final long ATTACH_EVENT = 52L;
    private static final String TARGET_OCCURRENCE =
            RecordedMapStateFixtures.TARGET_OCCURRENCE;

    // ----- the rule fires ---------------------------------------------------

    @Test
    public void pinsTheDisjunctKeyedOnTheTransportedValue() throws Exception {
        ConcolicSmtComposer.Result result = composed(true, constant(4242),
                symbol(HANDED_KEY));
        JsonObject pin = object(result.manifest,
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_FIELD);
        assertTrue(pin.toString(), bool(pin, "pinned", false));
        assertTrue(pin.toString(), bool(pin, "strengthening", false));
        assertEquals(pin.toString(), "", string(pin, "refusal"));
        assertEquals(pin.toString(),
                ConcolicSmtComposer.PIN_KIND_TARGET_PATH_CASE,
                string(pin, "pinKind"));
        assertEquals(pin.toString(), 2, integer(pin, "disjunctCount", 0));

        // The transported key ranks above the literal one, and the evidence
        // that says so is the VM's own handoff - the port it arrived on and
        // both endpoints of the edge that carried it.
        List<JsonObject> disjuncts = rows(pin, "disjuncts");
        assertEquals(pin.toString(), 0, integer(disjuncts.get(0), "rank", -1));
        assertEquals(pin.toString(), 1, integer(disjuncts.get(1), "rank", -1));
        JsonObject reach = array(disjuncts.get(1), "crossNodeReach").get(0)
                .getAsJsonObject();
        assertEquals(reach.toString(), HANDED_KEY,
                string(reach, "keySymbol"));
        assertEquals(reach.toString(), "REGION.1.in.0",
                string(reach, "portId"));
        assertEquals(reach.toString(),
                ConcolicSmtComposer.COMMUNICATION_LEAF,
                string(reach, "authority"));

        // The loser is named, never quietly dropped, and the disjunction it
        // belongs to is still in the formula beside the pin.
        List<JsonObject> excluded = rows(pin, "excludedDisjuncts");
        assertEquals(pin.toString(), 1, excluded.size());
        assertEquals(pin.toString(), 0,
                integer(excluded.get(0), "pathOrdinal", -1));
        assertEquals(pin.toString(),
                ConcolicSmtComposer.PIN_NO_CROSS_NODE_REACH,
                string(excluded.get(0), "excludedBecause"));
        assertTrue(result.smtLib, result.smtLib.contains(":named "
                + ConcolicSmtComposer.CAUSAL_WITNESS_PIN_ASSERTION + ")"));
        assertTrue(result.smtLib, result.smtLib.contains(":named fatal_path)"));

        // What is pinned is the winning path's case, not its term: a term
        // whose read no case performs is satisfied by never reading.
        assertEquals(pin.toString(),
                string(disjuncts.get(1), "caseSelector"),
                string(pin, "solverTerm"));
    }

    // ----- and refuses in each of the three ways it can ---------------------

    @Test
    public void failsClosedWhenNoDisjunctReachesAcrossANode() throws Exception {
        ConcolicSmtComposer.Result ranked = composed(true, constant(4242),
                symbol(HANDED_KEY));
        ConcolicSmtComposer.Result unranked = composed(false, constant(4242),
                symbol(HANDED_KEY));
        JsonObject pin = object(unranked.manifest,
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_FIELD);

        // Same two reads, same two keys; only the recorded handoff is gone.
        // With nothing saying the key crossed a node, nothing is pinned.
        assertFalse(pin.toString(), bool(pin, "pinned", true));
        assertEquals(pin.toString(),
                ConcolicSmtComposer.PIN_NO_CROSS_NODE_REACH,
                string(pin, "refusal"));
        assertEquals(pin.toString(), 0, integer(pin, "topRank", -1));
        assertEquals(pin.toString(), 0,
                rows(pin, "excludedDisjuncts").size());
        assertFalse(unranked.smtLib, unranked.smtLib.contains(
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_ASSERTION));
        assertTrue(ranked.smtLib, ranked.smtLib.contains(
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_ASSERTION));
    }

    @Test
    public void oneDisjunctIsNeverRanked() throws Exception {
        // The regression matrix's shape: one target read, so one disjunct.
        // A ranking over one candidate can only restate the query, and the
        // rule refuses rather than restate it.
        ConcolicSmtComposer.Result result = composed(true,
                Collections.singletonList(symbol(HANDED_KEY)));
        JsonObject pin = object(result.manifest,
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_FIELD);

        assertFalse(pin.toString(), bool(pin, "pinned", true));
        assertEquals(pin.toString(),
                ConcolicSmtComposer.PIN_SINGLE_DISJUNCT,
                string(pin, "refusal"));
        assertEquals(pin.toString(), 1, integer(pin, "disjunctCount", 0));
        assertFalse(result.smtLib, result.smtLib.contains(
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_ASSERTION));
    }

    @Test
    public void disjunctsThatRankAlikeExcludeNothing() throws Exception {
        // Both reads keyed on the transported value: the rank separates
        // nothing, so there is no disjunct to exclude and no pin to add.
        ConcolicSmtComposer.Result result = composed(true,
                symbol(HANDED_KEY), symbol(HANDED_KEY));
        JsonObject pin = object(result.manifest,
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_FIELD);

        assertFalse(pin.toString(), bool(pin, "pinned", true));
        assertEquals(pin.toString(),
                ConcolicSmtComposer.PIN_NO_DISCRIMINATION,
                string(pin, "refusal"));
        assertEquals(pin.toString(), 1, integer(pin, "topRank", -1));
        for (JsonObject disjunct : rows(pin, "disjuncts")) {
            assertEquals(pin.toString(), 1, integer(disjunct, "rank", -1));
        }
        assertFalse(result.smtLib, result.smtLib.contains(
                ConcolicSmtComposer.CAUSAL_WITNESS_PIN_ASSERTION));
    }

    // ----- fixture ----------------------------------------------------------

    private ConcolicSmtComposer.Result composed(boolean handed,
                                                JsonObject... keys)
            throws Exception {
        return composed(handed, Arrays.asList(keys));
    }

    /**
     * One target that reaches its failure once per key, over one map.
     *
     * <p>Each key is one recorded read of the same map location and one
     * fatal path constraining that read, so the composed fatal-path
     * assertion is a disjunction with one disjunct per key.  When
     * {@code handed} is set, the last path also carries the VM handoff that
     * brought {@link #HANDED_KEY} to this node.</p>
     */
    private ConcolicSmtComposer.Result composed(boolean handed,
                                                List<JsonObject> keys)
            throws Exception {
        JsonArray versions = new JsonArray();
        versions.add(stateVersion(WRITER_A, "STATE_PUT", "REGION.writerA",
                "TASK.a", writerState(1), null));
        versions.add(stateVersion(WRITER_B, "STATE_PUT", "REGION.writerB",
                "TASK.b", writerState(2), null));
        JsonArray reads = new JsonArray();
        JsonArray events = new JsonArray();
        events.add(event(WRITER_A, "FIELD_WRITE", 101L, "REGION.writerA",
                RecordedMapStateFixtures.MAP_OWNER));
        events.add(event(WRITER_B, "FIELD_WRITE", 102L, "REGION.writerB",
                RecordedMapStateFixtures.MAP_OWNER));
        List<JsonObject> predicates = new ArrayList<>();
        for (int index = 0; index < keys.size(); index++) {
            long readEventId = readEventId(index);
            reads.add(readRecord(readEventId));
            events.add(event(readEventId, "FIELD_READ", 103L + index,
                    "REGION.0", RecordedMapStateFixtures.MAP_OWNER));
            predicates.add(binary(read(readEventId, keys.get(index)), "==",
                    constant(1)));
        }
        JsonArray order = new JsonArray();
        order.add(edge(WRITER_A, WRITER_B, "SYNCHRONIZATION"));

        JsonObject envelope = mapVersionsEnvelope(versions, reads, true);
        SharedStateEvidence.normalizeGuards(envelope);
        JsonObject recorded = SharedStateEvidence.recorded(
                Collections.singletonList(mapVersionsRecord(envelope)),
                SharedStateEvidence.ledgerRecord(
                        ledgerEnvelope(events, order),
                        identity("REGION.reader", 1L)));

        Path directory = temporary.newFolder().toPath();
        Path fatal = directory.resolve("fatal.jsonl");
        Path summaries = directory.resolve("summaries.jsonl");
        Path plan = directory.resolve("runtime_plan.jsonl");
        write(fatal, fatalQuery(predicates, recorded) + "\n");
        write(summaries, producerSummary(handed).toJson() + "\n");
        write(plan, RuntimePlanArtifact.encode(
                Collections.<JsonObject>emptyList(),
                Collections.<JsonObject>emptyList(),
                Arrays.asList(region("REGION.0", true, false),
                        region("REGION.1", true, true))));
        return ConcolicSmtComposer.compose(
                ConcolicSmtComposer.Arguments.parse(new String[]{
                        "--fatal-query", fatal.toString(),
                        "--summaries", summaries.toString(),
                        "--runtime-plan", plan.toString(),
                        "--output", directory.resolve("candidate.smt2")
                        .toString(),
                        "--manifest", directory.resolve("manifest.json")
                        .toString(),
                        "--fatal-region", "REGION.0",
                        "--occurrence-id", TARGET_OCCURRENCE}));
    }

    private static long readEventId(int index) {
        return index == 0 ? LOCAL_READ : HANDED_READ + index - 1;
    }

    private static JsonObject writerState(long member) {
        return put(state("M_MAP_allKeys"), constant(4242), constant(member));
    }

    /** One guarded read of the shared map at {@code key}. */
    private static JsonObject read(long readEventId, JsonObject key) {
        JsonArray candidates = new JsonArray();
        JsonObject first = candidate("rf1", WRITER_A,
                query(writerState(1), key.deepCopy()), null, readEventId,
                WRITER_B);
        first.addProperty("regionId", "REGION.writerA");
        JsonObject second = candidate("rf2", WRITER_B,
                query(writerState(2), key.deepCopy()), null, readEventId,
                WRITER_A);
        second.addProperty("regionId", "REGION.writerB");
        candidates.add(first);
        candidates.add(second);
        candidates.add(unknownCandidate(readEventId, "M_I_unknown_"
                + readEventId));
        JsonObject node = guardedMapRead(candidates, true);
        node.addProperty("readEventId", readEventId);
        SharedStateEvidence.normalizeGuards(node);
        return node;
    }

    private static JsonObject readRecord(long readEventId) {
        JsonObject read = RecordedSharedStateFixtures.read(readEventId,
                SharedStateEvidence.RESOLUTION_GUARDED, "AMBIGUOUS_WRITERS",
                0L, 3);
        read.addProperty("observedFingerprintKind", "NONE");
        read.addProperty("observedFingerprint", 0L);
        read.addProperty("regionId", "REGION.0");
        read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                TARGET_OCCURRENCE);
        return read;
    }

    private static JsonObject fatalQuery(List<JsonObject> predicates,
                                         JsonObject recorded) {
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion",
                TargetReachPathQueryBuilder.SCHEMA_VERSION);
        fatal.addProperty("kind", "TARGET_REACH_PATH_SET_QUERY");
        fatal.addProperty("queryKey", "QUERY.CAUSAL.WITNESS.PIN");
        fatal.addProperty("regionId", "REGION.0");
        fatal.addProperty("occurrenceId", TARGET_OCCURRENCE);
        fatal.addProperty("targetSiteId", "<Test: void consume()>#u1");
        fatal.addProperty("targetOccurrence", 1);
        fatal.addProperty("requiredTakenOutcome", false);
        fatal.addProperty("constraintAuthority", "RECORDED_TARGET_PREFIX_V1");
        JsonArray paths = new JsonArray();
        for (int index = 0; index < predicates.size(); index++) {
            JsonObject path = new JsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(predicates.get(index));
            path.add("constraints", constraints);
            path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD,
                    new JsonArray());
            path.addProperty("desiredTakenOutcome", false);
            path.addProperty(
                    TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE,
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
            JsonObject metadata = new JsonObject();
            metadata.addProperty("predicateNormalization", "IDENTITY");
            BranchWitness witness = BranchWitness.vmPc(
                    "<Test: void consume()>#u1", "<Test: void consume()>", 1,
                    1, true, BranchPredicateAlgebra.complement(
                            predicates.get(index)), 0, metadata);
            path.add(TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS,
                    witness.toJson());
            path.add(SharedStateEvidence.RECORDED_FIELD, recorded.deepCopy());
            paths.add(path);
            if (index == 0) {
                fatal.add("seedReplayContract", BranchReplayContract.flip(
                        Collections.<BranchWitness>emptyList(), witness)
                        .toJson());
            }
        }
        fatal.add("paths", paths);
        fatal.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        LoopBoundPolicy.cfgBackedges(8).writeTo(fatal);
        JsonArray selected = new JsonArray();
        selected.add(protocolBinding());
        fatal.add("selectedTargetBindings", selected);
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", TARGET_OCCURRENCE);
        fatal.add("symbolicContext", context);
        return fatal;
    }

    /**
     * The companion the value came from.
     *
     * <p>With {@code handed} its case carries the VM handoff that brought
     * {@link #HANDED_KEY} across, and the ledger holding that edge.  Without
     * it the same case carries neither, so the two compositions differ in
     * exactly one recorded fact: whether the key ever crossed a node.</p>
     */
    private static RelationSummary producerSummary(boolean handed) {
        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.1", "REGION.1",
                Collections.singletonList("REGION.1.out.0"),
                "REGION.1.out.0", "<Test: int output>", "REGION_OUTPUT",
                "int", outputSlice());
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", RelationSummary.SCHEMA_VERSION);
        row.addProperty("kind", RelationSummary.KIND);
        row.addProperty("summaryId", "SUMMARY.PIN");
        row.addProperty("sourceKey", RecordedMapStateFixtures.SOURCE_KEY);
        row.addProperty("regionId", "REGION.1");
        row.addProperty("occurrenceId",
                RecordedMapStateFixtures.PRODUCER_OCCURRENCE);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(row);
        OutputClosureCodec.writeTo(row, closure);
        JsonArray bindings = new JsonArray();
        bindings.add(protocolBinding());
        row.add("edgeBindings", bindings);
        JsonObject path = new JsonObject();
        path.addProperty("caseId", "CASE.PIN");
        path.addProperty("occurrenceId",
                RecordedMapStateFixtures.PRODUCER_OCCURRENCE);
        path.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        path.addProperty("sourceTaskId", "TASK.PIN");
        JsonObject guard = new JsonObject();
        guard.addProperty("kind", "PATH_CONDITION");
        guard.add("conditions", new JsonArray());
        path.add("guard", guard);
        JsonObject outputs = new JsonObject();
        outputs.add("REGION.1.out.0", constant(10));
        path.add("outputExpressions", outputs);
        if (handed) {
            VmHandoffEvidence.writeTo(path, Collections.singletonList(
                    VmHandoffEvidence.event("REGION.1.in.0", EXPORT_EVENT,
                            ATTACH_EVENT, symbol(HANDED_KEY), "TASK.REMOTE",
                            "REGION.REMOTE@Test#call10")));
            JsonArray events = new JsonArray();
            events.add(event(EXPORT_EVENT, "HANDOFF_EXPORT", 110L,
                    "REGION.REMOTE"));
            events.add(event(ATTACH_EVENT, "HANDOFF_ATTACH", 111L,
                    "REGION.1"));
            JsonArray order = new JsonArray();
            order.add(edge(EXPORT_EVENT, ATTACH_EVENT, "VALUE_HANDOFF"));
            path.add(SharedStateEvidence.RECORDED_FIELD,
                    SharedStateEvidence.recorded(
                            Collections.<JsonObject>emptyList(),
                            SharedStateEvidence.ledgerRecord(
                                    ledgerEnvelope(events, order),
                                    identity("REGION.1", 1L))));
        }
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

    /** The one traced exchange that makes the companion a lowered producer. */
    private static JsonObject protocolBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 3);
        binding.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        binding.addProperty("edgeId", "EDGE.PIN");
        binding.addProperty("state", "CANDIDATE_TRACED_RPC_EXCHANGE");
        binding.addProperty("evidenceKind",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        binding.addProperty("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        binding.addProperty("transportKind", "HADOOP_IPC");
        binding.addProperty("fromRegion", "REGION.1");
        binding.addProperty("fromOccurrenceId",
                RecordedMapStateFixtures.PRODUCER_OCCURRENCE);
        binding.addProperty("fromOutputPort", "REGION.1.out.0");
        binding.addProperty("toRegion", "REGION.0");
        binding.addProperty("toOccurrenceId", TARGET_OCCURRENCE);
        binding.addProperty("toInputPort", "REGION.0.in.0");
        return binding;
    }

    private static JsonObject outputSlice() {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.1.out.0");
        slice.addProperty("outputCell", "<Test: int output>");
        JsonArray inputPorts = new JsonArray();
        inputPorts.add("REGION.1.in.0");
        slice.add("inputPorts", inputPorts);
        for (String member : new String[]{"sites", "staticSites", "methods",
                "captureBindings", "captureBindingIssues"}) {
            slice.add(member, new JsonArray());
        }
        JsonArray causalEdges = new JsonArray();
        causalEdges.add("EDGE.PIN");
        slice.add("causalEdgeIds", causalEdges);
        return slice;
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

    private static List<JsonObject> rows(JsonObject owner, String field) {
        List<JsonObject> result = new ArrayList<>();
        for (JsonElement element : array(owner, field)) {
            result.add(element.getAsJsonObject());
        }
        return result;
    }

    private static void write(Path path, String content) throws Exception {
        Files.write(path, content.getBytes(StandardCharsets.UTF_8));
    }
}
