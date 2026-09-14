package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.HandoffPhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Assume;
import org.junit.Test;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A handoff belongs to the occurrence whose port it is, and is answered by
 * the attach that minted it.
 *
 * <p>A CALL_RETURN attach runs in the CALLER's frame, so the row rides on
 * a different occurrence than the port is declared on: H names the consumer
 * the plan declares, and reproduction is asked of the corpus.</p>
 */
public class HandoffBelongsToItsConsumerTest {
    private static final String PORT = "XCH.1174244c.resp.block-key-id";
    private static final String CONSUMER =
            "hdfs-17899/sps#epoch0/region/REGION.16ba41cf#1";
    private static final String CARRIER =
            "hdfs-17899/sps#epoch0/region/REGION.b7266d53#1#a1";

    @Test
    public void aHandoffRowNamesTheOccurrenceWhosePortItIs() {
        JsonObject row = handoff(CONSUMER);

        assertEquals(CONSUMER, row.get(
                VmHandoffEvidence.CONSUMER_OCCURRENCE_ID).getAsString());
        assertTrue(VmHandoffEvidence.eventFault(row),
                VmHandoffEvidence.isEvent(row));

        // One that names none is no occurrence's handoff.
        row.addProperty(VmHandoffEvidence.CONSUMER_OCCURRENCE_ID, "");
        assertFalse("a row naming no consumer is refused by admission",
                VmHandoffEvidence.isEvent(row));
    }

    /**
     * A planned port is reproduced by the attach that minted it, wherever
     * the evidence rode.
     *
     * <p>The mint is the consumer's, so it happens whether or not the
     * message carried the producer's expression, and the row it publishes is
     * the reproduction.</p>
     */
    @Test
    public void aPlannedPortIsReproducedByTheAttachThatMintedIt() {
        JsonObject arrived = VmHandoffEvidence.event(PORT, 0L, 0L, null,
                "", "", CONSUMER,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                        "<a.BlockKey: int keyId>"),
                "M_I_field_HOFF.9c1d_a/BlockKey", "119982", "I", "", true);
        assertTrue(VmHandoffEvidence.eventFault(arrived),
                VmHandoffEvidence.isEvent(arrived));

        JsonObject raw = result(CARRIER);
        JsonArray events = new JsonArray();
        events.add(arrived);
        raw.add(VmHandoffEvidence.FIELD, events);
        assertFalse("a delivery with no element reproduced its planned port",
                reported(raw, "PLANNED_HANDOFF_NOT_REPRODUCED"));

        // The control: with no row at all the question is still asked, so
        // the assertion above is about the mint and not about the fold.
        raw.add(VmHandoffEvidence.FIELD, new JsonArray());
        assertTrue("a port nothing attached is still reported",
                reported(raw, "PLANNED_HANDOFF_NOT_REPRODUCED"));
    }

    /**
     * A handoff variable is answered by the attach that minted it, wherever
     * in this replay that attach happened.
     *
     * <p>The label {@code HOFF.<sha>} IS the identity of its attach, and
     * the attach happened in this same replay run, in whichever region
     * activation's summary made it: an assignment to a value that arrived
     * on a wire is a configured-source assignment whose phase id is the one
     * that obligation's handoff row names.</p>
     */
    @Test
    public void aHandoffVariableIsAnsweredByTheAttachThatMintedIt()
            throws Exception {
        JsonObject task = flipTask();
        JsonObject manifest = parse("{\"gaps\":[]}");
        ConcolicPathFlipPlanner.Wave.controlBySymbol(task, REPLAY,
                Arrays.asList(pathSummary(), siblingSummary()), manifest);

        JsonArray controls = task.getAsJsonArray(
                RegionPathWorklist.HANDOFF_CONTROLS);
        assertEquals("the attach that minted it answers it", 1,
                controls.size());
        JsonObject control = controls.get(0).getAsJsonObject();
        assertEquals(LABEL, control.get("rawSymbol").getAsString());
        assertEquals(PHASE, control.get(
                InSessionReadResolver.HANDOFF_PHASE_ID).getAsString());
        assertEquals("and names the activation it happened in",
                "node0/region/REGION.sibling#2#a1",
                control.get("consumerOccurrenceId").getAsString());
        assertEquals(0, manifest.getAsJsonArray("gaps").size());

        // A symbol no summary of this replay minted is named, not assumed.
        JsonObject alone = flipTask();
        manifest = parse("{\"gaps\":[]}");
        ConcolicPathFlipPlanner.Wave.controlBySymbol(alone, REPLAY,
                Arrays.asList(pathSummary()), manifest);
        assertFalse("nothing to carry",
                alone.has(RegionPathWorklist.HANDOFF_CONTROLS));
        JsonArray gaps = manifest.getAsJsonArray("gaps");
        assertEquals(1, gaps.size());
        assertEquals("HANDOFF_CONTROL_ROW_ABSENT",
                gaps.get(0).getAsJsonObject().get("kind").getAsString());
        assertTrue(gaps.get(0).getAsJsonObject().get("subject")
                .getAsString().contains("HOFF.abc123"));

        // And the solver materializes such an assignment, against the
        // phase id that row names.
        Assume.assumeTrue(z3Available());
        JsonObject query = wireQuery();
        JsonObject activation = parse("{\"inputActions\":[]}");
        assertEquals("with no handoff row the model is not materializable",
                "MATERIALIZATION_GAP", solve(query, activation).record
                        .get("status").getAsString());

        query.add(RegionPathWorklist.HANDOFF_CONTROLS,
                JsonParser.parseString("[{\"rawSymbol\":\"" + WIRE_SYMBOL
                + "\",\"handoffPhaseId\":\"" + WIRE_PHASE + "\","
                + "\"javaType\":\"I\",\"recordedValue\":\"7\"}]"));
        ConcolicConstraintSolver.Result result = solve(query, activation);
        assertEquals(result.record.toString(), "SAT_MODEL_READY",
                result.record.get("status").getAsString());
        assertEquals(1, result.modelAssignments.size());
        JsonObject assignment =
                result.modelAssignments.get(0).getAsJsonObject();
        assertEquals("SOURCE_PHASE:" + WIRE_PHASE,
                assignment.get("inputSymbol").getAsString());
        assertEquals(WIRE_PHASE,
                assignment.get("configuredSourcePhaseId").getAsString());
        assertEquals("the row states the symbol the query declared",
                WIRE_SYMBOL, assignment.get("engineSymbol").getAsString());
        assertFalse("so the target is covered, not reported unassigned",
                result.record.has("unassignedFlipVariables"));

        // And a model may not rest on a field the recording states no
        // value for: the accessor standing in for BlockKey.expiryDate is
        // free, so laneVM23's model expired a key the replay then kept.
        JsonObject free = wireQuery();
        free.add(RegionPathWorklist.HANDOFF_CONTROLS,
                query.get(RegionPathWorklist.HANDOFF_CONTROLS));
        free.add("replayContract", BranchReplayContract.atSource(
                BranchWitness.vmPcImmutable("TEST#u2",
                        "<test.Wire: void run()>", 1, 1, false,
                        BranchPredicateAlgebra.complement(parse(
                                "{'_type':'BinaryExpression','_op':'>',"
                                + "'_left':{'_type':'FieldAccessExpression',"
                                + "'_java_type':'J','ownerClass':'test/Key',"
                                + "'fieldOffset':8,'owner':{'_type':"
                                + "'SymbolExpression','_java_type':'test/Key'"
                                + ",'_exp':\"P_L'test/Key'_\"}},'_right':"
                                + "{'_type':'SymbolExpression','_java_type':"
                                + "'J','_exp':'" + WIRE_SYMBOL + "'}}")), 0,
                        parse("{'eventId':1,'contextId':1}"))).toJson());
        JsonObject refused = solve(free, activation).record;
        assertEquals(refused.toString(), "FLIP_MODEL_RESTS_ON_UNSTATED_FIELD",
                refused.get("reason").getAsString());
        assertEquals("test/Key@8:J", refused.getAsJsonArray(
                "unstatedFieldProjections").get(0).getAsString());
    }

    private static JsonObject handoff(String consumerOccurrenceId) {
        JsonObject expression = parse("{\"_type\":\"ConsumerBoundary"
                + "Expression\",\"boundaryKind\":\"RPC_ATTACH\","
                + "\"eventId\":63,\"_java_type\":\"I\",\"expression\":"
                + "{\"_type\":\"SymbolExpression\",\"_java_type\":\"I\","
                + "\"_exp\":\"M_I_field_SRC.root\"}}");
        return VmHandoffEvidence.event(PORT, 55L, 63L, expression,
                "TASK.SEED.1d0b713e",
                "hdfs-17899/nn0#epoch0/region/REGION.2392e4b7#1#a1",
                consumerOccurrenceId,
                HandoffPhaseContract.phaseId(PORT, CONSUMER, 1,
                        "<a.BlockKey: int keyId>"),
                "M_I_field_HOFF.9c1d_a/BlockKey", "119982", "I", "", false);
    }

    private static JsonObject result(String occurrenceId) {
        return parse("{\"event\":\"CONCOLIC_REGION_RESULT\",\"taskId\":"
                + "\"task\",\"occurrenceId\":\"" + occurrenceId + "\"}");
    }

    private static boolean reported(JsonObject raw, String code) {
        List<JsonObject> rows = new ArrayList<>();
        ConcolicSummaryImporter.topologyDivergences(
                new ConcolicSummaryImporter.ResultRow(raw, 0),
                consumerTask(), rows);
        for (JsonObject row : rows) {
            if (code.equals(row.get("code").getAsString())) return true;
        }
        return false;
    }

    private static ExecutionTask consumerTask() {
        return task(parse("{\"sourceKey\":\"hdfs-17899/sps#epoch0\","
                + "\"occurrenceId\":\"" + CONSUMER + "\",\"relationKey\":"
                + "\"relation\",\"regionId\":\"REGION.16ba41cf\",\"taskId\":"
                + "\"task\",\"goalId\":\"goal\",\"inputActions\":[],"
                + "\"communicationHandoffs\":[{\"portId\":\"" + PORT + "\","
                + "\"handoffLeafPath\":\"" + PORT + "\",\"side\":\"IN\","
                + "\"direction\":\"RESPONSE\",\"captureKind\":\"CALL_RETURN\","
                + "\"javaType\":\"int\",\"declaredCallee\":"
                + "\"<a.P: int keyId()>\",\"definitionMethod\":"
                + "\"<a.PBHelper: a.Key c()>\",\"definitionUnitIndex\":2}]}"));
    }

    private static ExecutionTask task(JsonObject row) {
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(row);
        return ExecutionTask.decode(row);
    }

    private static final String LABEL = "M_I_field_HOFF.abc123"
            + "_edu/uva/liftlab/graphchecker/runtime/"
            + "ConcolicRegionRuntime$HandoffLeafCarrier";
    private static final String PHASE =
            "HANDOFF_PHASE.11111111-2222-3333-4444-555555555555";
    private static final String REPLAY = "REPLAY.GROUP.ONE";

    private static JsonObject flipTask() {
        JsonObject task = parse("{\"queryKey\":\"0123456789abcdef\"}");
        task.add(ResolvedFlipQuery.FIELD, parse("{\"schemaVersion\":"
                + ResolvedFlipQuery.SCHEMA_VERSION + ",\"kind\":\""
                + ResolvedFlipQuery.KIND + "\",\"authority\":\""
                + ResolvedFlipQuery.AUTHORITY + "\",\"context\":[],"
                + "\"unresolved\":[],\"predicates\":[{\"_type\":"
                + "\"SymbolExpression\",\"_java_type\":\"I\",\"_exp\":\""
                + LABEL + "\"}]}"));
        return task;
    }

    private static JsonObject pathSummary() {
        return parse("{\"replayGroupId\":\"" + REPLAY + "\","
                + "\"occurrenceId\":\"node0/region/REGION.target#1#a1\"}");
    }

    private static JsonObject siblingSummary() {
        return parse("{\"replayGroupId\":\"" + REPLAY + "\","
                + "\"occurrenceId\":\"node0/region/REGION.sibling#2#a1\",\""
                + VmHandoffEvidence.FIELD + "\":[{\"kind\":"
                + "\"VM_HANDOFF_EVENT\",\"attachEventId\":77,\""
                + InSessionReadResolver.HANDOFF_SYMBOL + "\":\"" + LABEL
                + "\",\"" + InSessionReadResolver.HANDOFF_PHASE_ID + "\":\""
                + PHASE + "\",\"javaType\":\"I\",\"recordedValue\":"
                + "\"119982\"}]}");
    }

    private static final String WIRE_SYMBOL = "M_I_field_HOFF.abcdef0123456789"
            + "_edu/uva/liftlab/graphchecker/runtime/"
            + "ConcolicRegionRuntime$HandoffLeafCarrier";
    private static final String WIRE_PHASE =
            "HANDOFF_PHASE.1a2b3c4d-0000-0000-0000-000000000000";

    private static JsonObject wireQuery() {
        JsonObject target = parse("{\"_type\":\"BinaryExpression\",\"_op\":"
                + "\">\",\"_left\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"J\",\"_exp\":\"" + WIRE_SYMBOL + "\"},"
                + "\"_right\":{\"_type\":\"ConstExpr\",\"_java_type\":\"J\","
                + "\"_exp\":\"Y_J_10\"}}");
        BranchWitness source = BranchWitness.vmPcImmutable("TEST#u1",
                "<test.Wire: void run()>", 1, 1, false,
                BranchPredicateAlgebra.complement(target), 0,
                parse("{\"eventId\":1,\"contextId\":1}"));
        JsonObject query = parse("{\"schemaVersion\":3,\"kind\":"
                + "\"REGION_PATH_FLIP\",\"queryKey\":\""
                + CanonicalJson.sha256("wire-query") + "\",\"regionId\":"
                + "\"REGION.wire\",\"sourceActivationOccurrenceId\":"
                + "\"test/node#epoch0/region/REGION.wire#1#a1\","
                + "\"consumerAnchorCaseDependencies\":[],"
                + "\"solverPathContext\":{\"schemaVersion\":"
                + SolverPathContext.SCHEMA_VERSION + ",\"kind\":\""
                + SolverPathContext.KIND + "\",\"authority\":\""
                + SolverPathContext.AUTHORITY + "\",\"constraints\":[]}}");
        query.add("replayContract",
                BranchReplayContract.atSource(source).toJson());
        return query;
    }

    private static ConcolicConstraintSolver.Result solve(JsonObject query,
                                                         JsonObject activation)
            throws Exception {
        return ConcolicConstraintSolver.solve(query,
                Collections.singletonList(activation), activation,
                Paths.get("z3"), 10_000L,
                ClockRootPhysics.DEFAULT_SKEW_MILLIS);
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }

    private static JsonObject parse(String json) {
        return JsonParser.parseString(json).getAsJsonObject();
    }
}
