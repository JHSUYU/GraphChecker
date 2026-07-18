package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicPathFlipPlannerTest {
    @Test
    public void emitsOneSolvedPathPlanThatReusesReplayClasses()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Path directory = Files.createTempDirectory("single-path-flip-");
        Path activationFile = directory.resolve("seed-plan.jsonl");
        Path summaryFile = directory.resolve("seed-summary.jsonl");
        Path output = directory.resolve("flip");
        writeJsonl(activationFile, activation());
        writeJsonl(summaryFile, summary(false));

        ConcolicPathFlipPlanner.Arguments arguments =
                ConcolicPathFlipPlanner.Arguments.parse(new String[]{
                        "--activations", activationFile.toString(),
                        "--summaries", summaryFile.toString(),
                        "--output-dir", output.toString(),
                        "--z3", "z3",
                        "--activation-id", "ACT.UPSTREAM.TEST",
                        "--region-id", "REGION.TEST",
                        "--flip-site", "u14",
                        "--flip-occurrence", "1"});
        ConcolicPathFlipPlanner.Result result =
                ConcolicPathFlipPlanner.plan(arguments);
        ConcolicPathFlipPlanner.writeOutputs(output, result);

        assertTrue(result.manifest.toString(), result.manifest.get(
                "complete").getAsBoolean());
        assertEquals("PATH_FLIP_REPLAY_READY", result.manifest.get(
                "status").getAsString());
        assertFalse(result.manifest.get(
                "staticReinstrumentationRequired").getAsBoolean());
        assertTrue(result.manifest.get(
                "replayClassReuseRequired").getAsBoolean());

        JsonObject replay = JsonParser.parseString(Files.readAllLines(
                output.resolve("activation_plan.jsonl"),
                StandardCharsets.UTF_8).get(0)).getAsJsonObject();
        assertTrue(replay.get("activationId").getAsString().startsWith(
                "ACT.PATH."));
        assertEquals("REPLAY_OUTPUT_PATH_FLIP",
                replay.get("executionPhase").getAsString());
        assertEquals("RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY",
                replay.get("replayMode").getAsString());
        assertEquals(replay.get("activationId").getAsString(),
                replay.get("activationSelectionRequired").getAsString());
        assertEquals(1, replay.getAsJsonArray("modelAssignments").size());
        assertEquals("Z3_PATH_FLIP_MODEL", replay.getAsJsonArray(
                "modelAssignments").get(0).getAsJsonObject().get(
                "authority").getAsString());
        // observationOnlyReplay is reserved for a downstream target with no
        // input assignments.  A path flip injects only its solver model and
        // then validates the branch without overriding it.
        assertFalse(replay.has("observationOnlyReplay"));
        assertTrue(replay.getAsJsonObject("targetBranch").get(
                "validationOnly").getAsBoolean());
        assertFalse(replay.getAsJsonObject("targetBranch").get(
                "branchOverrideAllowed").getAsBoolean());
        assertFalse(replay.has("forcedBranches"));
        assertFalse(replay.has("replayMaterializations"));
        assertTrue(Files.size(output.resolve("path_flip_query.smt2")) > 0L);
        assertTrue(Files.size(output.resolve(
                "path_flip_solver_result.json")) > 0L);
    }

    @Test
    public void refusesToGuessWhenMoreThanOneExploreFlipMatches()
            throws Exception {
        Path directory = Files.createTempDirectory("ambiguous-path-flip-");
        Path activationFile = directory.resolve("seed-plan.jsonl");
        Path summaryFile = directory.resolve("seed-summary.jsonl");
        writeJsonl(activationFile, activation());
        writeJsonl(summaryFile, summary(true));

        Path output = directory.resolve("flip");
        ConcolicPathFlipPlanner.Result result =
                ConcolicPathFlipPlanner.plan(
                        ConcolicPathFlipPlanner.Arguments.parse(new String[]{
                                "--activations", activationFile.toString(),
                                "--summaries", summaryFile.toString(),
                                "--output-dir",
                                output.toString(),
                                "--activation-id", "ACT.UPSTREAM.TEST"}));
        ConcolicPathFlipPlanner.writeOutputs(output, result);

        assertFalse(result.manifest.get("complete").getAsBoolean());
        assertEquals("AMBIGUOUS_PATH_FLIP", result.manifest.get(
                "status").getAsString());
        assertEquals(2, result.manifest.get("selectedTaskCount").getAsInt());
        assertEquals(0L, Files.size(output.resolve(
                "activation_plan.jsonl")));
    }

    private static JsonObject activation() {
        JsonObject activation = new JsonObject();
        activation.addProperty("activationId", "ACT.UPSTREAM.TEST");
        activation.addProperty("regionId", "REGION.TEST");
        activation.addProperty("scheduleId", "SCHEDULE.SEED");
        activation.addProperty("replayMode",
                "RUNTIME_CONFIRMED_UPSTREAM_REGION_REPLAY");
        activation.addProperty("executionPhase", "CAPTURE_OUTPUT_PATH");
        activation.addProperty("activationSelectionRequired",
                "ACT.UPSTREAM.TEST");
        activation.addProperty("activationBundleRootActivationId",
                "ACT.UPSTREAM.TEST");
        activation.addProperty("activationBundleScheduleId",
                "SCHEDULE.SEED");
        activation.addProperty("activationBundleSize", 1);
        activation.addProperty("activationBundleIndex", 0);
        activation.addProperty("activationBundleMemberRole", "PRIMARY");
        activation.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonArray materializations = new JsonArray();
        JsonObject input = new JsonObject();
        input.addProperty("symbol", "REGION.TEST.in.0");
        input.addProperty("location", "ARGUMENT");
        input.addProperty("bindingMode", "ROOT_ENTRY");
        input.addProperty("index", 0);
        materializations.add(input);
        activation.add("materializations", materializations);
        return activation;
    }

    private static JsonObject summary(boolean secondExploreBranch) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.SEED");
        summary.addProperty("activationId", "ACT.UPSTREAM.TEST");
        summary.addProperty("regionId", "REGION.TEST");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", true);
        summary.add("captureGoal",
                RegionCaptureGoal.outputClosure().toJson());
        JsonObject output = new JsonObject();
        output.addProperty("portId", "REGION.TEST.out.0");
        output.addProperty("cell", "example.output");
        summary.add("requestedOutput", output);
        JsonObject outputSlice = new JsonObject();
        JsonArray sites = new JsonArray();
        sites.add("u14");
        if (secondExploreBranch) sites.add("u15");
        outputSlice.add("sites", sites);
        summary.add("requestedOutputSlice", outputSlice);

        JsonArray conditions = new JsonArray();
        conditions.add(binary(">", 0));
        if (secondExploreBranch) conditions.add(binary("<", 10));
        summary.add("pathCondition", conditions);
        JsonArray mappings = new JsonArray();
        mappings.add(mapping("u14", 0));
        if (secondExploreBranch) mappings.add(mapping("u15", 1));
        summary.add("branchMappings", mappings);
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapEffects", new JsonArray());
        return summary;
    }

    private static JsonObject mapping(String site, int conditionIndex) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", site);
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("conditionIndex", conditionIndex);
        mapping.addProperty("outcome", true);
        mapping.addProperty("policy", "EXPLORE");
        return mapping;
    }

    private static JsonObject binary(String operator, int constant) {
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "BinaryExpression");
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_java_type", "I");
        left.addProperty("_exp",
                "M_I_field_REGION.TEST.in.0_java/lang/Integer");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_java_type", "I");
        right.addProperty("_exp", "Y_I_" + constant);
        expression.add("_left", left);
        expression.addProperty("_op", operator);
        expression.add("_right", right);
        return expression;
    }

    private static void writeJsonl(Path path, JsonObject row)
            throws Exception {
        Files.write(path, (row.toString() + System.lineSeparator()).getBytes(
                StandardCharsets.UTF_8));
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }
}
