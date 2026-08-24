package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/** The target advances through an observed frontier before solving fatality. */
public class NestedTargetFrontierProgressionTest {

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private static final Gson JSON = new GsonBuilder()
            .disableHtmlEscaping().create();

    private static final String REGION = "REGION.nested.target";
    private static final String OCCURRENCE =
            "cluster/target#epoch0/region/" + REGION + "#1";
    private static final String GOAL = "GOAL.nested.target";
    private static final String TASK = "TASK.SEED.nested.target";
    private static final String METHOD = "<example.Target: void run()>";
    private static final String OUTER = METHOD + "#u10";
    private static final String INNER = METHOD + "#u20";
    private static final String DEEPEST = METHOD + "#u25";
    private static final String THROW = METHOD + "#u30";
    private static final String GATE_PHASE = sourcePhaseId(
            "TARGET.GATE", 1);
    private static final String LIMIT_PHASE = sourcePhaseId(
            "TARGET.LIMIT", 2);
    private static final String GATE_RAW = "M_I_field_"
            + SymbolicSourceEvidence.engineLabelForPhase(GATE_PHASE,
            "TARGET.GATE") + "_example/Target";
    private static final String REMOTE_RAW =
            "M_I_field_REMOTE.RESPONSE_example/Reply";
    private static final String LIMIT_RAW = "M_I_field_"
            + SymbolicSourceEvidence.engineLabelForPhase(LIMIT_PHASE,
            "TARGET.LIMIT") + "_example/Target";

    /**
     * The outer decision is not the fatal predicate: it is the current
     * frontier leading to an annotated but unobserved inner guard. Its flip
     * must therefore be a fresh replay whose target event is the inner site.
     */
    @Test
    public void outerFrontierFlipIsReplayedWithInnerGuardAsNextTarget() {
        JsonObject summary = outerOnlySummary();
        JsonObject task = outerFrontierTask();

        RegionPathWorklist.Result worklist = RegionPathWorklist.plan(
                Collections.singletonList(summary),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());

        assertEquals(worklist.manifest.toString(), 1,
                worklist.tasks.size());
        JsonObject flip = worklist.tasks.get(0);
        BranchReplayContract replay = BranchReplayContract.fromJson(
                flip.getAsJsonObject("replayContract"));
        assertEquals(OUTER, replay.source().siteId());
        assertEquals(false, replay.requiredTakenOutcome());
        assertEquals(INNER, flip.getAsJsonObject("targetBranch")
                .get("siteId").getAsString());

        JsonObject executable = PathReplayTaskFactory.create(flip, task,
                one(modelAssignment(1)), replay, null);
        assertEquals(INNER, executable.getAsJsonObject("targetBranch")
                .get("siteId").getAsString());
    }

    /**
     * A source event at the outer frontier attests only that frontier. Even
     * with a solver-ready complement, it cannot become the exception query
     * while the same annotated throw still has an unobserved inner guard.
     */
    @Test
    public void outerOnlySeedCannotBecomeTheFinalFatalQuery()
            throws Exception {
        try {
            build(outerOnlySummary(), seedQuery(OUTER,
                    true, outerPredicate(), false,
                    new JsonArray(), frontierBranches(false)));
            fail("the outer target frontier must be replayed before a final "
                    + "fatal query is published");
        } catch (IOException expected) {
            // The exact wording is deliberately not the contract. The
            // refusal must occur because INNER remains unobserved, not
            // because the otherwise exact outer summary is malformed.
        }
    }

    /**
     * After the frontier replay reaches the inner guard, the new target path
     * retains the outer outcome as prefix and flips only the exact inner
     * decision that controls the annotated throw.
     */
    @Test
    public void replayedFrontierMakesInnerGuardTheFinalTarget()
            throws Exception {
        JsonObject query = build(postFrontierSummary(), seedQuery(OUTER,
                true, outerPredicate(), false, new JsonArray(),
                frontierBranches(false)));

        assertEquals(INNER, query.get("targetSiteId").getAsString());
        JsonArray constraints = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject().getAsJsonArray("constraints");
        assertEquals(2, constraints.size());
        assertEquals(">", constraints.get(0).getAsJsonObject()
                .get("_op").getAsString());
        assertEquals(">", constraints.get(1).getAsJsonObject()
                .get("_op").getAsString());
        BranchReplayContract replay = BranchReplayContract.fromJson(
                query.getAsJsonObject("seedReplayContract"));
        assertEquals(1, replay.orderedPrefix().size());
        assertEquals(OUTER, replay.orderedPrefix().get(0).siteId());
        assertEquals(INNER, replay.source().siteId());
        assertEquals(LoopBoundPolicy.cfgBackedges(8).identity(),
                LoopBoundPolicy.decode(query).identity());
    }

    @Test
    public void threeNestedGuardsAdvanceOneFrontierAtATimeWithTwoLocalSources()
            throws Exception {
        JsonObject task = threeFrontierTask();
        RegionPathWorklist.Result first = RegionPathWorklist.plan(
                Collections.singletonList(outerOnlySummary()),
                Collections.singletonList(task),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        assertEquals(first.manifest.toString(), 1, first.tasks.size());
        assertEquals(INNER, first.tasks.get(0).getAsJsonObject("targetBranch")
                .get("siteId").getAsString());

        JsonObject firstProposal = first.tasks.get(0);
        BranchReplayContract firstReplay = BranchReplayContract.fromJson(
                firstProposal.getAsJsonObject("replayContract"));
        JsonObject afterOuter = PathReplayTaskFactory.create(firstProposal,
                task, one(modelAssignment(1)), firstReplay, null);
        JsonObject middle = middleFrontierSummary();
        middle.addProperty("taskId", afterOuter.get("taskId").getAsString());

        RegionPathWorklist.Result second = RegionPathWorklist.plan(
                Collections.singletonList(middle),
                Collections.singletonList(afterOuter),
                Collections.<JsonObject>emptyList(),
                RegionPathWorklist.Bounds.defaults());
        JsonObject deepestFlip = null;
        for (JsonObject candidate : second.tasks) {
            JsonObject target = candidate.has("targetBranch")
                    && candidate.get("targetBranch").isJsonObject()
                    ? candidate.getAsJsonObject("targetBranch")
                    : new JsonObject();
            if (target.has("siteId") && DEEPEST.equals(
                    target.get("siteId").getAsString())) {
                if (deepestFlip != null) {
                    fail("deepest frontier was scheduled more than once");
                }
                deepestFlip = candidate;
            }
        }
        if (deepestFlip == null) {
            fail("middle replay did not schedule the deepest frontier: "
                    + second.manifest);
        }
        BranchReplayContract secondReplay = BranchReplayContract.fromJson(
                deepestFlip.getAsJsonObject("replayContract"));
        JsonObject deepestTask = PathReplayTaskFactory.create(deepestFlip,
                afterOuter, one(limitModelAssignment(6)), secondReplay, null);
        assertEquals(2, deepestTask
                .getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD).size());

        JsonObject query = build(deepestFrontierSummary(), seedQuery(OUTER,
                true, outerPredicate(), false, new JsonArray(),
                threeFrontierBranches()));
        assertEquals(DEEPEST, query.get("targetSiteId").getAsString());
        JsonArray constraints = query.getAsJsonArray("paths").get(0)
                .getAsJsonObject().getAsJsonArray("constraints");
        assertEquals(3, constraints.size());
        BranchReplayContract replay = BranchReplayContract.fromJson(
                query.getAsJsonObject("seedReplayContract"));
        assertEquals(2, replay.orderedPrefix().size());
        assertEquals(OUTER, replay.orderedPrefix().get(0).siteId());
        assertEquals(INNER, replay.orderedPrefix().get(1).siteId());
        assertEquals(DEEPEST, replay.source().siteId());
    }

    private JsonObject build(JsonObject summary, JsonObject seed)
            throws IOException {
        File root = folder.newFolder("case-" + summary.get("summaryId")
                .getAsString().replace('.', '-'));
        File manifest = new File(root, "path_closure.json");
        File seeds = new File(root, "branch_queries.jsonl");
        File summaries = new File(root, "observed_path_summaries.jsonl");
        File output = new File(root, "reach_query.jsonl");
        write(manifest, manifest());
        write(seeds, seed);
        write(summaries, summary);
        return TargetReachPathQueryBuilder.build(
                TargetReachPathQueryBuilder.Arguments.parse(new String[]{
                        "--summaries", summaries.getAbsolutePath(),
                        "--path-manifest", manifest.getAbsolutePath(),
                        "--seed-query", seeds.getAbsolutePath(),
                        "--output", output.getAbsolutePath()}));
    }

    private static JsonObject outerFrontierTask() {
        JsonObject task = identity(TASK);
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(task);
        LoopBoundPolicy.cfgBackedges(8).writeTo(task);
        JsonArray actions = new JsonArray();
        JsonObject action = new JsonObject();
        action.addProperty("symbol", REGION + ".in.gate");
        action.addProperty("portId", REGION + ".in.gate");
        action.addProperty("mode", "CONCRETE");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature",
                "<example.Target: int gate>");
        action.addProperty("javaType", "int");
        actions.add(action);
        task.add("inputActions", actions);

        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", "TARGET.GATE");
        source.addProperty("sourcePhaseId", GATE_PHASE);
        source.addProperty("fieldSignature",
                "<example.Target: int gate>");
        source.addProperty("requiredTargetInputPort",
                REGION + ".in.gate");
        task.add(SymbolicSourceEvidence.TASK_FIELD, one(source));
        task.add("branches", frontierBranches(false));
        task.add("edgeBindings", new JsonArray());
        JsonObject target = new JsonObject();
        target.addProperty("siteId", OUTER);
        target.addProperty("occurrence", 1);
        task.add("targetBranch", target);
        return task;
    }

    private static JsonObject threeFrontierTask() {
        JsonObject task = outerFrontierTask();
        JsonObject action = new JsonObject();
        action.addProperty("symbol", REGION + ".in.limit");
        action.addProperty("portId", REGION + ".in.limit");
        action.addProperty("mode", "CONCRETE");
        action.addProperty("location", "HEAP_OBJECT_FIELD");
        action.addProperty("bindingMode", "FIELD_ACCESS");
        action.addProperty("accessFieldSignature",
                "<example.Target: int limit>");
        action.addProperty("javaType", "int");
        task.getAsJsonArray("inputActions").add(action);
        JsonObject source = new JsonObject();
        source.addProperty("authority",
                SymbolicSourceEvidence.DECLARATION_AUTHORITY);
        source.addProperty("sourceId", "TARGET.LIMIT");
        source.addProperty("sourcePhaseId", LIMIT_PHASE);
        source.addProperty("fieldSignature",
                "<example.Target: int limit>");
        source.addProperty("requiredTargetInputPort",
                REGION + ".in.limit");
        task.getAsJsonArray(SymbolicSourceEvidence.TASK_FIELD).add(source);
        task.add("branches", threeFrontierBranches());
        return task;
    }

    private static JsonObject outerOnlySummary() {
        JsonObject summary = summaryIdentity("SUMMARY.OUTER.FRONTIER");
        summary.add("pathCondition", one(outerPredicate()));
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(OUTER, 10, true, outerPredicate(), 0,
                "EXPLORE"));
        summary.add("branchMappings", mappings);
        summary.add(PathObservation.TargetReachEvent.FIELD,
                targetReach(OUTER, true));
        return summary;
    }

    private static JsonObject postFrontierSummary() {
        JsonObject summary = summaryIdentity("SUMMARY.INNER.REACHED");
        JsonArray conditions = new JsonArray();
        conditions.add(enteredOuterPredicate());
        conditions.add(innerNormalPredicate());
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(OUTER, 10, false,
                enteredOuterPredicate(), 0, "PATH_ASSUMPTION"));
        mappings.add(mapping(INNER, 20, true,
                innerNormalPredicate(), 1, "EXPLORE"));
        summary.add("branchMappings", mappings);
        summary.add(PathObservation.TargetReachEvent.FIELD,
                targetReach(INNER, true));
        return summary;
    }

    private static JsonObject middleFrontierSummary() {
        JsonObject summary = threeSummaryIdentity("SUMMARY.MIDDLE.REACHED");
        JsonArray conditions = new JsonArray();
        conditions.add(enteredOuterPredicate());
        conditions.add(middleNormalPredicate());
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(OUTER, 10, false,
                enteredOuterPredicate(), 0, "PATH_ASSUMPTION"));
        mappings.add(mapping(INNER, 20, true,
                middleNormalPredicate(), 1, "EXPLORE"));
        summary.add("branchMappings", mappings);
        summary.add(PathObservation.TargetReachEvent.FIELD,
                targetReach(INNER, true));
        return summary;
    }

    private static JsonObject deepestFrontierSummary() {
        JsonObject summary = threeSummaryIdentity("SUMMARY.DEEPEST.REACHED");
        JsonArray conditions = new JsonArray();
        conditions.add(enteredOuterPredicate());
        conditions.add(enteredMiddlePredicate());
        conditions.add(innerNormalPredicate());
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping(OUTER, 10, false,
                enteredOuterPredicate(), 0, "PATH_ASSUMPTION"));
        mappings.add(mapping(INNER, 20, false,
                enteredMiddlePredicate(), 1, "PATH_ASSUMPTION"));
        mappings.add(mapping(DEEPEST, 25, true,
                innerNormalPredicate(), 2, "EXPLORE"));
        summary.add("branchMappings", mappings);
        summary.add(PathObservation.TargetReachEvent.FIELD,
                targetReach(DEEPEST, true));
        return summary;
    }

    private static JsonObject summaryIdentity(String summaryId) {
        JsonObject summary = identity(TASK);
        summary.addProperty("summaryId", summaryId);
        summary.addProperty("schemaVersion", 1);
        summary.addProperty("kind", "CONCOLIC_REGION_SUMMARY");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        ClosureGoalKind.TARGET_REACH_CLOSURE.writeToTask(summary);
        LoopBoundPolicy.cfgBackedges(8).writeTo(summary);
        JsonArray symbolic = new JsonArray();
        symbolic.add("SOURCE_PHASE:" + GATE_PHASE);
        summary.add("symbolicInputs", symbolic);
        summary.add("edgeBindings", new JsonArray());
        return summary;
    }

    private static JsonObject threeSummaryIdentity(String summaryId) {
        JsonObject summary = summaryIdentity(summaryId);
        summary.getAsJsonArray("symbolicInputs").add(
                "SOURCE_PHASE:" + LIMIT_PHASE);
        return summary;
    }

    private static JsonObject seedQuery(
            String targetSite, boolean sourceOutcome,
            JsonObject sourcePredicate, boolean requiredOutcome,
            JsonArray orderedPrefix, JsonArray branches) {
        JsonObject seed = new JsonObject();
        seed.addProperty("schemaVersion", 1);
        seed.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        seed.addProperty("readyForSolver", true);
        seed.addProperty("queryKey", "QUERY." + targetSite);
        seed.addProperty("regionId", REGION);
        seed.addProperty("occurrenceId", OCCURRENCE);
        seed.addProperty("goalId", GOAL);
        seed.addProperty("sourceKey", "cluster/target#epoch0");
        seed.addProperty("targetSiteId", targetSite);
        seed.addProperty("fatalRequiredTakenOutcome", requiredOutcome);
        LoopBoundPolicy.cfgBackedges(8).writeTo(seed);
        // This is the bounded failure-guard catalog already present on the
        // scheduled task. The scheduler/query boundary must retain it so the
        // builder can distinguish a terminal guard from a frontier guard.
        seed.add("targetGuardCatalog", branches.deepCopy());

        JsonObject contract = new JsonObject();
        contract.addProperty("kind", "BINARY_BRANCH_REPLAY_CONTRACT");
        contract.addProperty("schemaVersion", 2);
        contract.add("orderedPrefix", orderedPrefix.deepCopy());
        contract.add("source", witness(targetSite,
                targetSite.equals(OUTER) ? 10 : 20,
                sourceOutcome, sourcePredicate,
                orderedPrefix.size()));
        seed.add("replayContract", contract);

        JsonObject selected = new JsonObject();
        selected.addProperty("occurrenceId", OCCURRENCE);
        selected.add("inputPorts", new JsonArray());
        selected.add("bindingIds", new JsonArray());
        seed.add("selectedTargetOccurrence", selected);
        JsonObject context = new JsonObject();
        context.addProperty("occurrenceId", OCCURRENCE);
        seed.add("symbolicContext", context);
        return seed;
    }

    private static JsonArray frontierBranches(boolean innerObserved) {
        JsonArray branches = new JsonArray();
        branches.add(branch(OUTER, true, innerObserved ? false : true,
                "EXPLORE"));
        branches.add(branch(INNER, innerObserved, true,
                innerObserved ? "EXPLORE" : "PATH_ASSUMPTION"));
        return branches;
    }

    private static JsonArray threeFrontierBranches() {
        JsonArray branches = new JsonArray();
        branches.add(branch(OUTER, true, true, "EXPLORE"));
        branches.add(branch(INNER, false, true, "PATH_ASSUMPTION"));
        branches.add(branch(DEEPEST, false, true, "PATH_ASSUMPTION"));
        return branches;
    }

    private static JsonObject branch(String site, boolean observed,
                                     boolean observedOutcome,
                                     String policy) {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", site);
        branch.addProperty("failureTarget", true);
        branch.addProperty("observed", observed);
        if (observed) {
            branch.addProperty("observedOutcome", observedOutcome);
            branch.addProperty("selectedOccurrence", 1);
        } else {
            branch.addProperty("selectedOccurrence", 0);
        }
        branch.addProperty("requiredOutcome", false);
        branch.addProperty("policy", policy);
        JsonObject guarded = new JsonObject();
        guarded.addProperty("siteId", THROW);
        guarded.addProperty("requiredOutcome", false);
        branch.add("guardedSiteOutcomes", one(guarded));
        return branch;
    }

    private static JsonObject identity(String taskId) {
        JsonObject row = new JsonObject();
        row.addProperty("taskId", taskId);
        row.addProperty("goalId", GOAL);
        row.addProperty("regionId", REGION);
        row.addProperty("sourceKey", "cluster/target#epoch0");
        row.addProperty("occurrenceId", OCCURRENCE);
        row.addProperty("relationKey",
                "cluster/target/relation/" + REGION);
        return row;
    }

    private static JsonObject manifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "REGION_PATH_WORKLIST");
        manifest.addProperty("state", "CLOSED");
        manifest.addProperty("coverageState", "CLOSED");
        manifest.add("gaps", new JsonArray());
        manifest.add("coverageGaps", new JsonArray());
        manifest.addProperty(ClosureGoalKind.TASK_FIELD,
                ClosureGoalKind.TARGET_REACH_CLOSURE.name());
        manifest.addProperty("regionId", REGION);
        manifest.addProperty("occurrenceId", OCCURRENCE);
        manifest.addProperty("goalId", GOAL);
        LoopBoundPolicy.cfgBackedges(8).writeTo(manifest);
        return manifest;
    }

    private static JsonObject mapping(
            String site, int unit, boolean outcome,
            JsonObject predicate, int pcIndex, String policy) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("policy", policy);
        mapping.addProperty("summaryPcIndex", pcIndex);
        mapping.add("witness", witness(site, unit, outcome,
                predicate, pcIndex));
        return mapping;
    }

    private static JsonObject witness(
            String siteId, int unitIndex, boolean outcome,
            JsonObject predicate, int vmPcIndex) {
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
        witness.add("sourceSatisfiedPredicate", predicate.deepCopy());
        witness.addProperty("sourceTakenOutcome", outcome);
        witness.addProperty("vmPcIndex", vmPcIndex);
        return witness;
    }

    private static JsonObject targetReach(String site, boolean outcome) {
        JsonObject event = new JsonObject();
        event.addProperty("kind", PathObservation.TargetReachEvent.KIND);
        event.addProperty("siteId", site);
        event.addProperty("occurrence", 1);
        event.addProperty("outcome", outcome);
        return event;
    }

    /** Baseline Jimple branch: {@code if (gate <= 0) goto normalExit}. */
    private static JsonObject outerPredicate() {
        return predicate(GATE_RAW, "<=", 0);
    }

    /** Frontier replay enters the nested block: {@code gate > 0}. */
    private static JsonObject enteredOuterPredicate() {
        return predicate(GATE_RAW, ">", 0);
    }

    /** Normal inner decision: {@code remote <= 10}; complement is fatal. */
    private static JsonObject innerNormalPredicate() {
        return predicate(REMOTE_RAW, "<=", 10);
    }

    /** Middle guard takes its normal exit while the deepest guard is hidden. */
    private static JsonObject middleNormalPredicate() {
        return predicate(LIMIT_RAW, "<=", 5);
    }

    /** The next replay enters the middle block. */
    private static JsonObject enteredMiddlePredicate() {
        return predicate(LIMIT_RAW, ">", 5);
    }

    private static JsonObject predicate(String raw, String operator,
                                        int constant) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp", raw);
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_code_position", METHOD + ":100");
        predicate.add("_left", left);
        predicate.addProperty("_op", operator);
        predicate.add("_right", right);
        return predicate;
    }

    private static JsonObject modelAssignment(int value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL.TARGET.GATE");
        assignment.addProperty("engineSymbol", GATE_RAW);
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:" + GATE_PHASE);
        assignment.addProperty("configuredSourceId", "TARGET.GATE");
        assignment.addProperty("configuredSourcePhaseId", GATE_PHASE);
        assignment.addProperty("configuredSourceFieldSignature",
                "<example.Target: int gate>");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", String.valueOf(value));
        return assignment;
    }

    private static JsonObject limitModelAssignment(int value) {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL.TARGET.LIMIT");
        assignment.addProperty("engineSymbol", LIMIT_RAW);
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:" + LIMIT_PHASE);
        assignment.addProperty("configuredSourceId", "TARGET.LIMIT");
        assignment.addProperty("configuredSourcePhaseId", LIMIT_PHASE);
        assignment.addProperty("configuredSourceFieldSignature",
                "<example.Target: int limit>");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", String.valueOf(value));
        return assignment;
    }

    private static JsonArray one(JsonObject row) {
        JsonArray result = new JsonArray();
        result.add(row);
        return result;
    }

    private static String sourcePhaseId(String sourceId, int unitIndex) {
        return ConfiguredSourcePhaseContract.phaseId(OCCURRENCE,
                ConfiguredSourcePhaseContract.siteId(METHOD, unitIndex),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static void write(File file, JsonObject row)
            throws IOException {
        Files.write(file.toPath(),
                (JSON.toJson(row) + System.lineSeparator())
                        .getBytes(StandardCharsets.UTF_8));
    }
}
