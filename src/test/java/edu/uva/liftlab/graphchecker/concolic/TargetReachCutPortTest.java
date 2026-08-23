package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * The target fragment behind a communication cut takes its input through the
 * cut's declared port.
 *
 * <p>README section 3's {@code T_S(Req_in, Resp_out)} is stated over the port
 * the cut declares, and that port is named after the exchange <em>site</em>:
 * it carries no region id, so the {@code <regionId>.in.} test that recognises
 * a region-minted port says nothing about it. Before this, a server fragment
 * whose only symbolic input was {@code XCH.<site>.req.p0} was refused as
 * "ambiguous target inputPorts" and no target reach query could be built for
 * any segmented case at all.</p>
 *
 * <p>The refusal it must not have weakened is the one below it: a port that
 * neither the region nor the cut mints is still not a port of this
 * occurrence.</p>
 */
public class TargetReachCutPortTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private static final String REGION = "REGION.b29f9e3d-09e2-363a-98c0-"
            + "e79910578a9e";
    private static final String OCCURRENCE = "slice/server#epoch0/region/"
            + REGION + "#1";
    private static final String GOAL = "GOAL.TARGET_REACH.12bf3876";
    private static final String METHOD = "<Server: int serve(int)>";
    private static final String TARGET_SITE = METHOD + "#u6";
    private static final String EXCHANGE_SITE =
            "XCH.dc98a244-08b8-370c-9cc0-7cc5320c0089";
    private static final String CUT_PORT =
            CommunicationCatalogContract.requestPortId(EXCHANGE_SITE, "p0");

    @Test
    public void theDeclaredCutPortIsAdmittedAsTheTargetFragmentsInput()
            throws Exception {
        assertTrue(CUT_PORT + " must be a port the contract mints",
                CommunicationCatalogContract.declaredPortId(CUT_PORT));

        JsonObject query = build(CUT_PORT);

        assertEquals("TARGET_REACH_PATH_SET_QUERY",
                query.get("kind").getAsString());
        assertEquals("RECORDED_TARGET_PREFIX_V1",
                query.get("constraintAuthority").getAsString());
        assertEquals(1, query.getAsJsonArray("paths").size());
        JsonObject selectedPath = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(true, selectedPath
                .getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .get("outcome").getAsBoolean());
        assertEquals(false,
                selectedPath.get("desiredTakenOutcome").getAsBoolean());
        assertEquals(">", selectedPath.getAsJsonArray("constraints")
                .get(0).getAsJsonObject().get("_op").getAsString());
        JsonArray admitted = query.getAsJsonObject("selectedTargetOccurrence")
                .getAsJsonArray("inputPorts");
        assertEquals(1, admitted.size());
        assertEquals(CUT_PORT, admitted.get(0).getAsString());
        assertEquals(0, query.getAsJsonArray(
                "selectedTargetBindings").size());
    }

    @Test
    public void aPortNeitherTheRegionNorTheCutMintsIsStillRefused()
            throws Exception {
        try {
            build("someOtherRegion.in.0f9b882a");
            fail("a port of another region must not be admitted");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(),
                    refused.getMessage().contains(
                            "nor a declared cut port"));
        }
    }

    @Test
    public void aRegionInputPortIsStillAdmitted() throws Exception {
        JsonObject query = build(REGION + ".in.375274cb");

        assertEquals(REGION + ".in.375274cb",
                query.getAsJsonObject("selectedTargetOccurrence")
                        .getAsJsonArray("inputPorts").get(0).getAsString());
    }

    @Test
    public void aPathWithoutTheRuntimeTargetEventCannotBecomeAQuery()
            throws Exception {
        JsonObject unattested = summary();
        unattested.remove(PathObservation.TargetReachEvent.FIELD);
        try {
            build(CUT_PORT, unattested);
            fail("an unattested path must not become a target query");
        } catch (IOException refused) {
            assertTrue(refused.getMessage(), refused.getMessage().contains(
                    "no exact source-attested target path"));
        }
    }

    @Test
    public void theRequiredRuntimeEventBecomesADirectTargetWitness()
            throws Exception {
        JsonObject opposite = summary();
        JsonObject mapping = opposite.getAsJsonArray("branchMappings")
                .get(0).getAsJsonObject();
        JsonObject witnessed = oppositePredicate();
        mapping.getAsJsonObject("witness")
                .addProperty("sourceTakenOutcome", false);
        mapping.getAsJsonObject("witness").add(
                "sourceSatisfiedPredicate", witnessed.deepCopy());
        opposite.getAsJsonArray("pathCondition").set(0,
                witnessed.deepCopy());
        opposite.getAsJsonObject(PathObservation.TargetReachEvent.FIELD)
                .addProperty("outcome", false);

        JsonObject query = build(CUT_PORT, opposite);

        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(false, path.getAsJsonObject(
                PathObservation.TargetReachEvent.FIELD)
                .get("outcome").getAsBoolean());
        assertEquals(TargetReachPathQueryBuilder.REQUIRED_TARGET_REACH_EVENT,
                path.get(TargetReachPathQueryBuilder.TARGET_ATTESTATION_ROLE)
                        .getAsString());
        assertEquals(">", path.getAsJsonArray("constraints").get(0)
                .getAsJsonObject().get("_op").getAsString());
    }

    private JsonObject build(String inputPort) throws IOException {
        return build(inputPort, summary());
    }

    private JsonObject build(String inputPort, JsonObject summary)
            throws IOException {
        File root = folder.newFolder(Integer.toHexString(
                31 * inputPort.hashCode() + summary.hashCode()));
        File manifest = new File(root, "path_closure.json");
        File seed = new File(root, "branch_queries.jsonl");
        File summaries = new File(root, "observed_path_summaries.jsonl");
        File output = new File(root, "reach_query.jsonl");
        write(manifest, manifest());
        write(seed, seedQuery(inputPort));
        write(summaries, summary);
        return TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", summaries.getAbsolutePath(),
                        "--path-manifest", manifest.getAbsolutePath(),
                        "--seed-query", seed.getAbsolutePath(),
                        "--exception-type", "test.TargetReached",
                        "--output", output.getAbsolutePath()}));
    }

    private static void write(File file, JsonObject row) throws IOException {
        Files.write(file.toPath(),
                (JSON.toJson(row) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static JsonObject manifest() {
        JsonObject row = new JsonObject();
        row.addProperty("state", "CLOSED");
        row.add("gaps", new JsonArray());
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("regionId", REGION);
        row.addProperty("goalId", GOAL);
        row.addProperty("occurrenceId", OCCURRENCE);
        return row;
    }

    private static JsonObject seedQuery(String inputPort) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        row.addProperty("readyForSolver", true);
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty("sourceKey", "slice/server#epoch0");
        row.addProperty("targetSiteId", TARGET_SITE);
        row.addProperty("fatalRequiredTakenOutcome", false);

        JsonObject contract = new JsonObject();
        contract.addProperty("kind", "BINARY_BRANCH_REPLAY_CONTRACT");
        contract.addProperty("schemaVersion", 2);
        contract.add("orderedPrefix", new JsonArray());
        contract.add("source", witness(TARGET_SITE, 6, true));
        row.add("replayContract", contract);

        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", OCCURRENCE);
        context.add("equalityClasses", new JsonArray());
        context.add("equalityRelations", new JsonArray());
        row.add("symbolicContext", context);

        JsonObject selected = new JsonObject();
        selected.addProperty("occurrenceId", OCCURRENCE);
        JsonArray ports = new JsonArray();
        ports.add(inputPort);
        selected.add("inputPorts", ports);
        selected.add("bindingIds", new JsonArray());
        row.add("selectedTargetOccurrence", selected);
        return row;
    }

    private static JsonObject summary() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("relationallyComplete", true);
        row.addProperty("taskId", "TASK.SEED.TARGET");
        row.addProperty("sourceKey", "slice/server#epoch0");
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("kind", "CFG_BACKEDGE");
        loopBound.addProperty("scope", "ALL_EXECUTION_SCOPE_LOOPS");
        loopBound.addProperty("maxBackedgeTraversals", 8);
        loopBound.addProperty("onLimit", "CUT_PATH");
        row.add("loopBound", loopBound);
        JsonArray pathCondition = new JsonArray();
        pathCondition.add(predicate());
        row.add("pathCondition", pathCondition);
        JsonObject mapping = new JsonObject();
        mapping.addProperty("policy", "EXPLORE");
        mapping.addProperty("summaryPcIndex", 0);
        mapping.add("witness", witness(TARGET_SITE, 6, true));
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        row.add("branchMappings", mappings);
        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", TARGET_SITE);
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        row.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        row.add("edgeBindings", new JsonArray());
        return row;
    }

    private static JsonObject witness(String siteId, int unitIndex,
                                      boolean outcome) {
        JsonObject site = new JsonObject();
        site.addProperty("method", METHOD);
        site.addProperty("occurrence", 1);
        site.addProperty("siteId", siteId);
        site.addProperty("unitIndex", unitIndex);
        JsonObject witness = new JsonObject();
        witness.addProperty("kind", "BINARY_BRANCH_WITNESS");
        witness.addProperty("schemaVersion", 1);
        witness.addProperty("predicateNormalization", "IDENTITY");
        witness.add("site", site);
        witness.add("sourceSatisfiedPredicate", predicate());
        witness.addProperty("sourceTakenOutcome", outcome);
        witness.addProperty("vmPcIndex", 0);
        return witness;
    }

    /** {@code Req_in <= 20}, stated over the declared cut port's symbol. */
    private static JsonObject predicate() {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", "M_I_field_" + CUT_PORT
                + "_java/lang/Integer");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_20");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_code_position", METHOD + ":149");
        predicate.add("_left", left);
        predicate.addProperty("_op", "<=");
        predicate.add("_right", right);
        return predicate;
    }

    private static JsonObject oppositePredicate() {
        JsonObject result = predicate();
        result.addProperty("_op", ">");
        return result;
    }
}
