package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.PathObservation;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * README {@code PC-1}: "A case guard contains the relevant decisions and
 * nothing from transport/startup noise."
 *
 * <p>Both halves of that sentence are pinned here for the fatal target case,
 * which is where the guard is consumed verbatim.  The relevant decisions are
 * the branch decisions this execution recorded on its way to the target -
 * dropping one would weaken the reachability query into admitting a model
 * that never reaches the target.  The noise is the other channel: the
 * container and method relations the VM recorded while transport, SASL and
 * startup library frames ran under the same occurrence.  Those reach the
 * guard only through a dependency edge from a decision, never by position.
 *
 * <p>The second test pins the reader side of the same item: the ambient VM
 * path condition has no reader left at all, so an older or patched VM that
 * still serialises one cannot silently re-admit that noise.</p>
 */
public class TargetCaseGuardSliceTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private static final String REGION = "REGION.GUARD.SLICE";
    private static final String OCCURRENCE =
            "slice/target#epoch0/region/" + REGION + "#1";
    private static final String GOAL = "GOAL.TARGET_REACH.GUARD_SLICE";
    private static final String METHOD = "<example.Target: void run()>";
    private static final String GUARD_SITE = METHOD + "#u4";
    private static final String TARGET_SITE = METHOD + "#u9";
    private static final String GATE = "M_I_field_example/Target_gate";
    private static final String KEY = "M_I_field_example/Target_keyId";
    private static final String SASL = "M_I_field_sasl/Negotiation_state";
    private static final String TRANSPORT_RELATION = "AUX.SASL.NEGOTIATION";
    private static final String DEMANDED_RELATION = "AUX.KEY.MAP.READ";

    /**
     * The occurrence recorded four rows: a nested guard it had to take, one
     * container relation from a SASL frame that ran underneath it, one
     * container relation that defines the target's own operand, and the
     * target decision.  Three of the four are the case; the SASL row is not.
     */
    @Test
    public void theFatalGuardKeepsDecisionsAndDropsTransportRelations()
            throws Exception {
        JsonObject summary = targetSummary();
        assertEquals("the recorded prefix under test must be the wide one",
                4, summary.getAsJsonArray("pathCondition").size());

        JsonArray constraints = build(summary).getAsJsonArray("paths")
                .get(0).getAsJsonObject().getAsJsonArray("constraints");

        // The nested guard, the relation the target operand is defined by,
        // and the flipped target predicate - in recorded order.
        assertEquals(constraints.toString(), 3, constraints.size());
        assertEquals(">", constraints.get(0).getAsJsonObject()
                .get("_op").getAsString());
        assertEquals(DEMANDED_RELATION, constraints.get(1).getAsJsonObject()
                .get("relationId").getAsString());
        assertEquals(">", constraints.get(2).getAsJsonObject()
                .get("_op").getAsString());
        assertFalse(constraints.toString(),
                constraints.toString().contains(TRANSPORT_RELATION));
        assertFalse(constraints.toString(),
                constraints.toString().contains(SASL));
    }

    /**
     * The same slice, taken by the class that owns it, so a consumer that is
     * not the fatal query cannot read the wide prefix back either.
     */
    @Test
    public void theProjectedTargetGuardIsTheSameSlice() {
        PathObservation observation = PathObservation.decode(
                targetSummary(), null);

        JsonArray projected = observation.relationPathCondition();
        assertEquals(projected.toString(), 3, projected.size());
        assertFalse(projected.toString(),
                projected.toString().contains(TRANSPORT_RELATION));
        // The kept rows keep their recorded positions, because the query
        // cuts its prefix on them and row 2 is no longer at offset 2.
        assertEquals(Arrays.asList(0, 2, 3),
                observation.relationPathConditionPositions());
    }

    /**
     * README {@code PC-1} deletes the full ambient-PC fallback, and the P0
     * tombstone forbids restoring it.  A summary from an engine that never
     * declared the omission therefore imports as an incomplete relation, and
     * the terms that existed only in its ambient array reach no guard.
     */
    @Test
    public void anAmbientPathConditionIsNamedAndNeverRead() throws Exception {
        JsonObject raw = ambientEngineResult();
        assertEquals("the fixture must offer an ambient array to read", 2,
                raw.getAsJsonObject("engineSummary")
                        .getAsJsonArray("pathCondition").size());

        Path directory = folder.newFolder("ambient-path-condition").toPath();
        Path results = directory.resolve("results.jsonl");
        Path tasks = directory.resolve("tasks.jsonl");
        Path regions = directory.resolve("regions.jsonl");
        Path output = directory.resolve("summaries.jsonl");
        Path diagnostics = directory.resolve("diagnostics.jsonl");
        Path delta = directory.resolve(TopologyDelta.FILE_NAME);
        JsonObject region = new JsonObject();
        region.addProperty("regionId", REGION);
        ArtifactIO.replaceJsonl(tasks,
                Collections.singletonList(importerTask()));
        ArtifactIO.replaceJsonl(regions, Collections.singletonList(region));
        ArtifactIO.replaceJsonl(results, Collections.singletonList(raw));

        ConcolicSummaryImporter.ImportResult result =
                ConcolicSummaryImporter.importSummaries(results, tasks,
                        ConcolicSummaryImporter.regionIds(
                                ArtifactIO.readJsonl(regions)),
                        output, diagnostics, delta,
                        "test-ambient-path-condition");

        assertEquals(1, result.validSummaryCount);
        JsonObject summary = ArtifactIO.readJsonl(output).get(0);
        assertFalse(summary.get("relationallyComplete").getAsBoolean());
        assertTrue(ArtifactIO.readJsonl(diagnostics).get(0).get("detail")
                .getAsString().contains("AMBIENT_PATH_CONDITION_NOT_ADMITTED"));
        // Only the selected branch witness rebuilt a term.  The ambient-only
        // row never had a reader, so it is absent rather than filtered.
        assertEquals(1, summary.getAsJsonArray("pathCondition").size());
        assertEquals(">", summary.getAsJsonArray("pathCondition").get(0)
                .getAsJsonObject().get("_op").getAsString());
        assertFalse(summary.toString(),
                summary.toString().contains(TRANSPORT_RELATION));
        assertFalse(summary.toString(),
                summary.has("pathConditionAuthority"));
    }

    // --------------------------------------------------------------- fixtures

    private JsonObject build(JsonObject summary) throws IOException {
        File root = folder.newFolder("query-"
                + Integer.toHexString(summary.hashCode()));
        File manifest = new File(root, "path_closure.json");
        File seed = new File(root, "branch_queries.jsonl");
        File summaries = new File(root, "observed_path_summaries.jsonl");
        File output = new File(root, "reach_query.jsonl");
        write(manifest, manifest());
        write(seed, seedQuery());
        write(summaries, summary);
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

    private static JsonObject seedQuery() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        row.addProperty("readyForSolver", true);
        row.addProperty("queryKey", "QUERY.TARGET.GUARD.SLICE");
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty("sourceKey", "slice/target#epoch0");
        row.addProperty("targetSiteId", TARGET_SITE);
        row.addProperty("fatalRequiredTakenOutcome", false);
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);

        JsonObject contract = new JsonObject();
        contract.addProperty("kind", "BINARY_BRANCH_REPLAY_CONTRACT");
        contract.addProperty("schemaVersion", 2);
        contract.add("orderedPrefix", new JsonArray());
        contract.add("source", witness(TARGET_SITE, 9, true,
                predicate(KEY, "<=", 10), 3));
        row.add("replayContract", contract);

        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", OCCURRENCE);
        row.add("symbolicContext", context);

        JsonObject selected = new JsonObject();
        selected.addProperty("occurrenceId", OCCURRENCE);
        JsonArray ports = new JsonArray();
        ports.add(REGION + ".in.0a1b2c3d");
        selected.add("inputPorts", ports);
        selected.add("bindingIds", new JsonArray());
        row.add("selectedTargetOccurrence", selected);
        return row;
    }

    /**
     * One imported target case in the shape the current VM produces: the
     * selected branch witnesses plus the bounded auxiliary constraints, all
     * at their recorded positions in one compact array.
     */
    private static JsonObject targetSummary() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 1);
        row.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        row.addProperty("regionId", REGION);
        row.addProperty("occurrenceId", OCCURRENCE + "#a1");
        row.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        row.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, OCCURRENCE);
        row.addProperty("goalId", GOAL);
        row.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        row.addProperty("relationallyComplete", true);
        row.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        row.addProperty("taskId", "TASK.SEED.GUARD.SLICE");
        row.addProperty("sourceKey", "slice/target#epoch0");
        row.addProperty("pathConditionAuthority",
                "VM_SELECTED_BRANCH_AND_AUXILIARY_CONSTRAINTS_V1");
        LoopBoundPolicy.cfgBackedges(8).writeTo(row);

        JsonArray pathCondition = new JsonArray();
        pathCondition.add(predicate(GATE, ">", 0));
        pathCondition.add(containerRelation(TRANSPORT_RELATION, SASL));
        pathCondition.add(containerRelation(DEMANDED_RELATION, KEY));
        pathCondition.add(predicate(KEY, "<=", 10));
        row.add("pathCondition", pathCondition);

        JsonArray mappings = new JsonArray();
        mappings.add(mapping("PATH_ASSUMPTION", 0, witness(GUARD_SITE, 4,
                true, predicate(GATE, ">", 0), 0)));
        mappings.add(mapping("EXPLORE", 3, witness(TARGET_SITE, 9, true,
                predicate(KEY, "<=", 10), 3)));
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

    /** The frozen task the ambient-shaped raw result is imported against. */
    private static JsonObject importerTask() {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.SEED.AMBIENT");
        task.addProperty("goalId", GOAL);
        task.addProperty("regionId", REGION);
        task.addProperty("sourceKey", "slice/target#epoch0");
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "slice/target/" + REGION);
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());

        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", TARGET_SITE);
        branch.addProperty("method", METHOD);
        branch.addProperty("unitIndex", 9);
        branch.addProperty("policy", "EXPLORE");
        JsonObject occurrence = new JsonObject();
        occurrence.addProperty("occurrence", 1);
        occurrence.addProperty("outcome", true);
        JsonArray occurrences = new JsonArray();
        occurrences.add(occurrence);
        branch.add("occurrences", occurrences);
        JsonArray branches = new JsonArray();
        branches.add(branch);
        task.add("branches", branches);

        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId", TARGET_SITE);
        targetBranch.addProperty("occurrence", 1);
        task.add("targetBranch", targetBranch);
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        return task;
    }

    /** A raw result from an engine that still serialises its ambient PC. */
    private static JsonObject ambientEngineResult() {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("schemaVersion", 1);
        raw.addProperty("taskId", "TASK.SEED.AMBIENT");
        raw.addProperty(PathObservation.ACTIVATION_ORDINAL, 1);
        raw.addProperty(PathObservation.PLANNED_OCCURRENCE_ID, OCCURRENCE);
        raw.addProperty("occurrenceId", OCCURRENCE + "#a1");
        raw.addProperty("relationallyComplete", true);
        raw.addProperty(PathObservation.TARGET_REACHED, true);
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");

        JsonObject engine = new JsonObject();
        engine.addProperty("complete", true);
        engine.addProperty("aborted", false);
        engine.addProperty("active", true);
        JsonArray ambient = new JsonArray();
        ambient.add(predicate(KEY, ">", 10));
        ambient.add(containerRelation(TRANSPORT_RELATION, SASL));
        engine.add("pathCondition", ambient);
        raw.add("engineSummary", engine);

        raw.add("unresolvedInputs", new JsonArray());
        raw.add("symbolizedInputs", new JsonArray());
        raw.add(SymbolicSourceEvidence.FREE_SYMBOLS_FIELD, new JsonArray());
        raw.add("outputCaptures", new JsonArray());

        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", TARGET_SITE);
        mapping.addProperty("method", METHOD);
        mapping.addProperty("unitIndex", 9);
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("rawPathConditionBaseline", 0);
        mapping.addProperty("rawPathConditionSize", 2);
        mapping.add("witness", BranchWitness.vmPc(TARGET_SITE, METHOD, 9, 1,
                true, predicate(KEY, ">", 10), 0, new JsonObject())
                .toJson());
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        raw.add("branchMappings", mappings);

        JsonObject targetReach = new JsonObject();
        targetReach.addProperty("kind",
                PathObservation.TargetReachEvent.KIND);
        targetReach.addProperty("siteId", TARGET_SITE);
        targetReach.addProperty("occurrence", 1);
        targetReach.addProperty("outcome", true);
        raw.add(PathObservation.TargetReachEvent.FIELD, targetReach);
        return raw;
    }

    private static JsonObject mapping(String policy, int summaryPcIndex,
                                      JsonObject witness) {
        JsonObject row = new JsonObject();
        row.addProperty("policy", policy);
        row.addProperty("summaryPcIndex", summaryPcIndex);
        row.add("witness", witness);
        return row;
    }

    private static JsonObject witness(String siteId, int unitIndex,
                                      boolean outcome, JsonObject predicate,
                                      int vmPcIndex) {
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
        witness.add("sourceSatisfiedPredicate", predicate);
        witness.addProperty("sourceTakenOutcome", outcome);
        witness.addProperty("vmPcIndex", vmPcIndex);
        return witness;
    }

    /**
     * One bounded auxiliary constraint, as the VM's separate channel carries
     * it: a container relation over exactly one symbol.
     */
    private static JsonObject containerRelation(String relationId,
                                                String symbol) {
        JsonObject operand = new JsonObject();
        operand.addProperty("_type", "SymbolExpression");
        operand.addProperty("_java_type", "I");
        operand.addProperty("_exp", symbol);
        JsonObject relation = new JsonObject();
        relation.addProperty("_type", "ContainerRelation");
        relation.addProperty("relationId", relationId);
        relation.addProperty("kind", "ASSOCIATIVE_READ");
        relation.add("member", operand);
        return relation;
    }

    private static JsonObject predicate(String symbol, String operator,
                                        int constant) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", symbol);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_code_position", METHOD + ":42");
        predicate.add("_left", left);
        predicate.addProperty("_op", operator);
        predicate.add("_right", right);
        return predicate;
    }
}
