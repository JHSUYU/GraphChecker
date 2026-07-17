package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicPathReplayVerifierTest {
    private static final String QUERY_KEY =
            "0123456789abcdef0123456789abcdef"
                    + "0123456789abcdef0123456789abcdef";
    private static final String PATH_ID = "a8ae6e6ee929abea";
    private static final String ACTIVATION_ID = "ACT.PATH." + PATH_ID;
    private static final String SCHEDULE_ID = "SCHEDULE.PATH." + PATH_ID;

    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void writesManifestForUniqueScheduledOutputPathFlip()
            throws Exception {
        Fixture fixture = fixture();

        int status = ConcolicPathReplayVerifier.run(fixture.arguments());

        assertEquals(0, status);
        JsonObject report = read(fixture.output);
        assertTrue(report.toString(), report.get("valid").getAsBoolean());
        assertEquals(1, report.get("matchingRawResultCount").getAsInt());
        assertEquals(1, report.get("matchingImportedSummaryCount")
                .getAsInt());
        assertTrue(report.getAsJsonObject("scheduledTargetValidation")
                .get("valid").getAsBoolean());
        assertTrue(report.getAsJsonObject("replayValidation")
                .get("valid").getAsBoolean());
    }

    @Test
    public void rejectsOutcomeMatchWithoutScheduledTargetEvidence()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject raw = fixture.raw.deepCopy();
        JsonObject target = raw.getAsJsonArray("branchMappings")
                .get(1).getAsJsonObject();
        target.addProperty("scheduledTarget", false);
        target.remove("scheduledDesiredOutcome");
        target.remove("scheduledOutcomeMatched");
        writeJsonl(fixture.results, raw);

        int status = ConcolicPathReplayVerifier.run(fixture.arguments());

        assertEquals(2, status);
        JsonObject report = read(fixture.output);
        assertFalse(report.get("valid").getAsBoolean());
        assertFalse(report.getAsJsonObject("scheduledTargetValidation")
                .get("valid").getAsBoolean());
        assertTrue("base validator alone observes the outcome",
                report.getAsJsonObject("replayValidation")
                        .get("valid").getAsBoolean());
        assertTrue(report.getAsJsonArray("failures").toString().contains(
                "SCHEDULED_FLIP_TARGET_NOT_EXACT"));
    }

    @Test
    public void rejectsDuplicateRowsForTheReplayActivation()
            throws Exception {
        Fixture fixture = fixture();
        writeJsonl(fixture.results, fixture.raw, fixture.raw.deepCopy());

        int status = ConcolicPathReplayVerifier.run(fixture.arguments());

        assertEquals(2, status);
        JsonObject report = read(fixture.output);
        assertFalse(report.get("valid").getAsBoolean());
        assertEquals(2, report.get("matchingRawResultCount").getAsInt());
        assertTrue(report.getAsJsonArray("failures").toString().contains(
                "RAW_RESULT_ACTIVATION_NOT_UNIQUE"));
        assertTrue(report.getAsJsonArray("failures").toString().contains(
                "RAW_RESULTS_FILE_ROW_COUNT_NOT_ONE"));
    }

    @Test
    public void rejectsExpectedPrefixObservedAfterTheFlipTarget()
            throws Exception {
        Fixture fixture = fixture();
        JsonArray reordered = new JsonArray();
        reordered.add(fixture.raw.getAsJsonArray("branchMappings")
                .get(1).getAsJsonObject().deepCopy());
        reordered.add(fixture.raw.getAsJsonArray("branchMappings")
                .get(0).getAsJsonObject().deepCopy());
        JsonObject raw = fixture.raw.deepCopy();
        raw.add("branchMappings", reordered);
        writeJsonl(fixture.results, raw);

        int status = ConcolicPathReplayVerifier.run(fixture.arguments());

        assertEquals(2, status);
        JsonObject report = read(fixture.output);
        assertFalse(report.get("valid").getAsBoolean());
        assertTrue(report.getAsJsonObject("scheduledTargetValidation")
                .get("valid").getAsBoolean());
        assertTrue("membership-only base validator accepts this order",
                report.getAsJsonObject("replayValidation")
                        .get("prefixValidated").getAsBoolean());
        assertFalse(report.getAsJsonObject("orderedPrefixValidation")
                .get("allPrefixMappingsBeforeTarget").getAsBoolean());
        assertTrue(report.getAsJsonArray("failures").toString().contains(
                "REPLAY_BRANCH_PREFIX_NOT_EXACT"));
    }

    private Fixture fixture() throws Exception {
        Path root = temporary.newFolder().toPath();
        Fixture fixture = new Fixture();
        fixture.taskFile = root.resolve("replay_validation_plan.json");
        fixture.activationPlan = root.resolve("activation_plan.jsonl");
        fixture.results = root.resolve("concolic_region_results.jsonl");
        fixture.summary = root.resolve("concolic_region_summaries.jsonl");
        fixture.output = root.resolve("path_replay_verification.json");
        fixture.task = task();
        fixture.activation = activation(fixture.task);
        fixture.raw = raw(fixture.task, fixture.activation);
        fixture.imported = imported(fixture.task, fixture.activation);
        write(fixture.taskFile, fixture.task.toString());
        writeJsonl(fixture.activationPlan, fixture.activation);
        writeJsonl(fixture.results, fixture.raw);
        writeJsonl(fixture.summary, fixture.imported);
        return fixture;
    }

    private static JsonObject task() {
        JsonObject task = new JsonObject();
        task.addProperty("schemaVersion", 1);
        task.addProperty("kind", "REGION_PATH_FLIP");
        task.addProperty("queryKey", QUERY_KEY);
        task.addProperty("regionId", "REGION.15");
        task.addProperty("sourceActivationId", "ACT.UPSTREAM.9");
        task.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        task.addProperty("flipSite", "SITE.1");
        task.addProperty("flipOccurrence", 4);
        task.addProperty("desiredOutcome", false);
        JsonObject prefix = branch("SITE.0", 3, true);
        prefix.addProperty("conditionIndex", 0);
        JsonArray prefixes = new JsonArray();
        prefixes.add(prefix);
        task.add("expectedBranchPrefix", prefixes);
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.15.out.122");
        requested.addProperty("cell", "<example.Manager: java.util.Map "
                + "allKeys>");
        requested.addProperty("kind", "HEAP_STATE");
        task.add("requestedOutput", requested);
        JsonArray assignments = new JsonArray();
        assignments.add(plannedAssignment());
        task.add("modelAssignments", assignments);
        return task;
    }

    private static JsonObject activation(JsonObject task) {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", ACTIVATION_ID);
        activation.addProperty("scheduleId", SCHEDULE_ID);
        activation.addProperty("regionId", "REGION.15");
        activation.addProperty("executionPhase", "REPLAY_OUTPUT_PATH_FLIP");
        activation.addProperty("activationSelectionRequired",
                ACTIVATION_ID);
        activation.addProperty("activationBundleRootActivationId",
                ACTIVATION_ID);
        activation.addProperty("activationBundleScheduleId",
                SCHEDULE_ID);
        activation.addProperty("activationBundleSize", 1);
        activation.addProperty("activationBundleIndex", 0);
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        activation.addProperty("pathQueryKey", QUERY_KEY);
        activation.add("modelAssignments", task.getAsJsonArray(
                "modelAssignments").deepCopy());
        activation.add("expectedBranchPrefix", task.getAsJsonArray(
                "expectedBranchPrefix").deepCopy());
        JsonObject target = new JsonObject();
        target.addProperty("siteId", "SITE.1");
        target.addProperty("occurrence", 4);
        target.addProperty("desiredOutcome", false);
        target.addProperty("validationOnly", true);
        target.addProperty("branchOverrideAllowed", false);
        activation.add("targetBranch", target);
        activation.addProperty("branchOverrideProhibited", true);
        return activation;
    }

    private static JsonObject raw(JsonObject task, JsonObject activation) {
        JsonObject raw = new JsonObject();
        raw.addProperty("event", "CONCOLIC_REGION_RESULT");
        raw.addProperty("executionMode", "SYMBOLIC_CONCOLIC");
        raw.addProperty("activationId", string(activation, "activationId"));
        raw.addProperty("regionId", "REGION.15");
        raw.addProperty("exitKind", "NORMAL");
        raw.addProperty("exceptionType", "");
        raw.addProperty("branchOverrideUsed", false);
        raw.addProperty("modelAssignmentCount", 1);
        raw.addProperty("modelAssignmentAppliedCount", 1);
        raw.addProperty("allModelAssignmentsApplied", true);
        JsonObject applied = task.getAsJsonArray("modelAssignments")
                .get(0).getAsJsonObject().deepCopy();
        applied.remove("solverSymbol");
        JsonArray appliedRows = new JsonArray();
        appliedRows.add(applied);
        raw.add("modelAssignmentsApplied", appliedRows);
        raw.add("replayMaterializationsApplied", new JsonArray());
        raw.add("dynamicFieldBindings", new JsonArray());
        JsonArray mappings = new JsonArray();
        mappings.add(branch("SITE.0", 3, true));
        JsonObject target = branch("SITE.1", 4, false);
        target.addProperty("scheduledTarget", true);
        target.addProperty("scheduledDesiredOutcome", false);
        target.addProperty("scheduledOutcomeMatched", true);
        mappings.add(target);
        raw.add("branchMappings", mappings);
        return raw;
    }

    private static JsonObject imported(JsonObject task,
                                       JsonObject activation) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.REPLAY.OUTPUT.FLIP");
        summary.addProperty("activationId", string(activation,
                "activationId"));
        summary.addProperty("regionId", "REGION.15");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.addProperty("normalExit", true);
        summary.addProperty("exceptionType", "");
        summary.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        summary.add("requestedOutput", task.getAsJsonObject(
                "requestedOutput").deepCopy());
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "Ljava/util/Map;");
        expression.addProperty("_exp", "REGION.15.in.32");
        JsonObject expressions = new JsonObject();
        expressions.add("REGION.15.out.122", expression);
        summary.add("outputExpressions", expressions);
        JsonObject admission = new JsonObject();
        admission.addProperty("complete", true);
        summary.add("outputExpressionAdmission", admission);
        summary.add("dynamicFieldBindings", new JsonArray());
        return summary;
    }

    private static JsonObject plannedAssignment() {
        JsonObject assignment = new JsonObject();
        assignment.addProperty("engineSymbol", "REGION.15.in.146");
        assignment.addProperty("solverSymbol", "solver_key_id");
        assignment.addProperty("inputSymbol", "REGION.15.in.146");
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "-415760230");
        assignment.addProperty("authority", "Z3_PATH_FLIP_MODEL");
        assignment.addProperty("materializeAtRealDefinition", true);
        return assignment;
    }

    private static JsonObject branch(String site, int occurrence,
                                     boolean outcome) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("occurrence", occurrence);
        mapping.addProperty("outcome", outcome);
        mapping.addProperty("observedOutcome", outcome);
        mapping.addProperty("effectiveOutcome", outcome);
        mapping.addProperty("overrideApplied", false);
        return mapping;
    }

    private static JsonObject read(Path path) throws Exception {
        return new JsonParser().parse(new String(Files.readAllBytes(path),
                StandardCharsets.UTF_8)).getAsJsonObject();
    }

    private static void writeJsonl(Path path, JsonObject... rows)
            throws Exception {
        StringBuilder value = new StringBuilder();
        for (JsonObject row : rows) {
            value.append(row).append(System.lineSeparator());
        }
        write(path, value.toString());
    }

    private static void write(Path path, String value) throws Exception {
        Files.write(path, value.getBytes(StandardCharsets.UTF_8));
    }

    private static String string(JsonObject object, String member) {
        return object.get(member).getAsString();
    }

    private static final class Fixture {
        private Path taskFile;
        private Path activationPlan;
        private Path results;
        private Path summary;
        private Path output;
        private JsonObject task;
        private JsonObject activation;
        private JsonObject raw;
        private JsonObject imported;

        private String[] arguments() {
            return new String[]{
                    "--task", taskFile.toString(),
                    "--activation-plan", activationPlan.toString(),
                    "--results", results.toString(),
                    "--summary", summary.toString(),
                    "--output", output.toString()
            };
        }
    }
}
