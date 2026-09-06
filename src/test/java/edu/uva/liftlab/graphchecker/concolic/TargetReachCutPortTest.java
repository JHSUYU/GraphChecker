package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

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
        /** The exchange edge a replay recorded and the frozen plan lacked. */
    private static final String ABSORBED_EDGE =
            "RPC.1d5f0b6c-7a44-3e18-8c0b-2f2e5b7a91d0";
    private static final String PRODUCER_OCCURRENCE =
            "slice/client#epoch0/region/REGION.9c1a7f20-2d61-3b55-a4de-"
            + "6f30b1c8d47e#1";

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
        assertEquals(TARGET_SITE, selectedPath.getAsJsonObject(
                TargetReachPathQueryBuilder.TARGET_BRANCH_WITNESS)
                .getAsJsonObject("site").get("siteId").getAsString());
        JsonArray admitted = query.getAsJsonObject("selectedTargetOccurrence")
                .getAsJsonArray("inputPorts");
        assertEquals(1, admitted.size());
        assertEquals(CUT_PORT, admitted.get(0).getAsString());
        assertEquals(0, query.getAsJsonArray(
                "selectedTargetBindings").size());
        assertEquals(LoopBoundPolicy.cfgBackedges(8).identity(),
                LoopBoundPolicy.decode(query).identity());
    }

    @Test
    public void vmHandoffEvidenceRemainsOnItsTargetPath()
            throws Exception {
        JsonObject witnessed = summary();
        JsonObject attached = new JsonObject();
        attached.addProperty("_type", "SymbolExpression");
        attached.addProperty("_java_type", "I");
        attached.addProperty("_exp", "M_I_field_REMOTE.VALUE_Test");
        VmHandoffEvidence.writeTo(witnessed,
                java.util.Collections.singletonList(VmHandoffEvidence.event(
                        CUT_PORT, 41L, 42L, attached, "TASK.PRODUCER",
                        PRODUCER_OCCURRENCE)));
        witnessed.getAsJsonArray("edgeBindings").add(
                absorbed(exchangeBinding(), "TASK.PRODUCER"));

        JsonObject query = build(CUT_PORT, witnessed);

        assertTrue(query.toString(), !query.has(VmHandoffEvidence.FIELD));
        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(1, path.getAsJsonArray(VmHandoffEvidence.FIELD).size());
        assertEquals(41L, path.getAsJsonArray(VmHandoffEvidence.FIELD)
                .get(0).getAsJsonObject()
                .get(VmHandoffEvidence.EXPORT_EVENT_ID).getAsLong());
        // README RPC-1: the receive endpoint travels with the export, so the
        // path keeps the whole edge rather than half of it.
        assertEquals(42L, path.getAsJsonArray(VmHandoffEvidence.FIELD)
                .get(0).getAsJsonObject()
                .get(VmHandoffEvidence.ATTACH_EVENT_ID).getAsLong());
        assertEquals(ABSORBED_EDGE,
                path.getAsJsonArray(VmHandoffEvidence.FIELD)
                        .get(0).getAsJsonObject()
                        .get(VmHandoffEvidence.SELECTED_ENDPOINT_EDGE_ID)
                        .getAsString());
    }

    @Test
    public void sharedStateEvidenceRemainsOnItsTargetPath()
            throws Exception {
        JsonObject witnessed = summary();
        JsonObject recorded = new JsonObject();
        recorded.addProperty("pathLocalMarker", "TARGET.REPLAY.ONE");
        witnessed.add(SharedStateEvidence.RECORDED_FIELD, recorded);

        JsonObject query = build(CUT_PORT, witnessed);

        assertTrue(query.toString(), !query.has(
                SharedStateEvidence.RECORDED_FIELD));
        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals("TARGET.REPLAY.ONE", path.getAsJsonObject(
                        SharedStateEvidence.RECORDED_FIELD)
                .get("pathLocalMarker").getAsString());
    }

    @Test
    public void loopEvidenceRemainsOnItsTargetPath() throws Exception {
        JsonObject witnessed = summary();
        JsonObject count = new JsonObject();
        count.addProperty(LoopBoundPolicy.LOOP_SITE_ID,
                METHOD + "#u2");
        count.addProperty(LoopBoundPolicy.LOOP_BODY_COUNT, 2);
        JsonArray counts = new JsonArray();
        counts.add(count);
        witnessed.add(LoopBoundPolicy.PATH_LOOP_COUNTS, counts);
        JsonObject gap = new JsonObject();
        gap.addProperty("reason",
                LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS);
        gap.addProperty("subject", METHOD + "#u4");
        gap.addProperty("detail", "focused target loop evidence");
        JsonArray gaps = new JsonArray();
        gaps.add(gap);
        witnessed.add(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS, gaps);

        JsonObject query = build(CUT_PORT, witnessed);

        JsonObject path = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject();
        assertEquals(counts,
                path.getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNTS));
        assertEquals(gaps,
                path.getAsJsonArray(LoopBoundPolicy.PATH_LOOP_COUNT_GAPS));
    }

                /** One traced exchange row feeding the selected occurrence's cut port. */
    private static JsonObject exchangeBinding() {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", ABSORBED_EDGE);
        binding.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        binding.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        binding.addProperty("fromOutputPort", CUT_PORT);
        binding.addProperty("toOccurrenceId", OCCURRENCE);
        binding.addProperty("toInputPort", CUT_PORT);
        return binding;
    }

    /** The four fields that re-derive one row from the carry file. */
    private static JsonObject absorbed(JsonObject binding,
                                       String producerTaskId) {
        binding.addProperty(VmHandoffEvidence.ABSORBED_AUTHORITY_FIELD,
                VmHandoffEvidence.ABSORBED_AUTHORITY);
        binding.addProperty(VmHandoffEvidence.ABSORBED_FROM_TASK_ID,
                producerTaskId);
        binding.addProperty(VmHandoffEvidence.ABSORBED_EXPORT_EVENT_ID, 217L);
        binding.addProperty(VmHandoffEvidence.ABSORBED_ATTACH_EVENT_ID, 220L);
        return binding;
    }

            private JsonObject build(String inputPort) throws IOException {
        return build(inputPort, summary());
    }

    private JsonObject build(String inputPort, JsonObject summary)
            throws IOException {
        return build(inputPort, summary, manifest());
    }

    private JsonObject build(String inputPort, JsonObject summary,
                             JsonObject pathManifest) throws IOException {
        return build(inputPort, summary, pathManifest,
                seedQuery(inputPort));
    }

    private JsonObject build(String inputPort, JsonObject summary,
                             JsonObject pathManifest, JsonObject seedQuery)
            throws IOException {
        return build(inputPort, Collections.singletonList(summary),
                pathManifest, seedQuery);
    }

    private JsonObject build(String inputPort, List<JsonObject> summaries)
            throws IOException {
        return build(inputPort, summaries, manifest(), seedQuery(inputPort));
    }

    private JsonObject build(String inputPort, List<JsonObject> summaryRows,
                             JsonObject pathManifest, JsonObject seedQuery)
            throws IOException {
        File root = folder.newFolder(Integer.toHexString(
                31 * inputPort.hashCode() + summaryRows.hashCode()
                        + pathManifest.hashCode() + seedQuery.hashCode()));
        File manifest = new File(root, "path_closure.json");
        File seed = new File(root, "branch_queries.jsonl");
        File summaries = new File(root, "observed_path_summaries.jsonl");
        File output = new File(root, "reach_query.jsonl");
        write(manifest, pathManifest);
        write(seed, seedQuery);
        write(summaries, summaryRows);
        return TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", summaries.getAbsolutePath(),
                        "--path-manifest", manifest.getAbsolutePath(),
                        "--seed-query", seed.getAbsolutePath(),
                        "--output", output.getAbsolutePath()}));
    }

    private static void write(File file, JsonObject row) throws IOException {
        Files.write(file.toPath(),
                (JSON.toJson(row) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
    }

    private static void write(File file, List<JsonObject> rows)
            throws IOException {
        StringBuilder encoded = new StringBuilder();
        for (JsonObject row : rows) {
            encoded.append(JSON.toJson(row)).append(System.lineSeparator());
        }
        Files.write(file.toPath(), encoded.toString().getBytes(
                StandardCharsets.UTF_8));
    }

    private static JsonObject manifest() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "REGION_PATH_WORKLIST");
        row.addProperty("state", "CLOSED");
        row.addProperty("coverageState", "CLOSED");
        row.add("gaps", new JsonArray());
        row.add("coverageGaps", new JsonArray());
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("regionId", REGION);
        row.addProperty("goalId", GOAL);
        row.addProperty("occurrenceId", OCCURRENCE);
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);
        return row;
    }

    private static JsonObject seedQuery(String inputPort) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        row.addProperty("readyForSolver", true);
        row.addProperty("queryKey", "QUERY.TARGET.CUT.PORT");
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty("sourceKey", "slice/server#epoch0");
        row.addProperty("targetSiteId", TARGET_SITE);
        row.addProperty("fatalRequiredTakenOutcome", false);
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);

        JsonObject contract = new JsonObject();
        contract.addProperty("kind", "BINARY_BRANCH_REPLAY_CONTRACT");
        contract.addProperty("schemaVersion", 2);
        contract.add("orderedPrefix", new JsonArray());
        contract.add("source", witness(TARGET_SITE, 6, true));
        row.add("replayContract", contract);

        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", OCCURRENCE);
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
        row.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, OCCURRENCE);
        row.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        row.addProperty("occurrenceId", OCCURRENCE + "#a1");
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
        row.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
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

}
