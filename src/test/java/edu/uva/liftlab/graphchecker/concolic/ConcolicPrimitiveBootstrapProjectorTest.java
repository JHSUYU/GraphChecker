package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ConcolicPrimitiveBootstrapProjectorTest {
    @Test
    public void z3SelectsProducerCasesAndBuildsAllTargetBundle()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        assertTrue(result.manifest.toString(), result.manifest.get(
                "complete").getAsBoolean());
        assertEquals("SAT_UPSTREAM_BOOLEAN_MODEL_READY",
                result.manifest.get("status").getAsString());
        assertFalse(result.manifest.get(
                "reportableFinalReachCondition").getAsBoolean());
        assertEquals(3, result.activations.size());
        assertEquals("REACHABILITY_SUPPORT", result.activations.get(0)
                .get("activationBundleMemberRole").getAsString());
        assertEquals("REACHABILITY_SUPPORT", result.activations.get(1)
                .get("activationBundleMemberRole").getAsString());
        for (int index = 0; index < 2; index++) {
            JsonObject producer = result.activations.get(index);
            assertEquals("ALL", producer.get(
                    "activationSelectionRequired").getAsString());
            assertTrue(producer.get("concreteReplayOnly").getAsBoolean());
            JsonArray assignments = producer.getAsJsonArray(
                    "modelAssignments");
            assertEquals(1, assignments.size());
            assertEquals("true", assignments.get(0).getAsJsonObject()
                    .get("value").getAsString());
            assertEquals("Z3_PATH_FLIP_MODEL", assignments.get(0)
                    .getAsJsonObject().get("authority").getAsString());
        }
        JsonObject target = result.activations.get(2);
        assertEquals("PRIMARY", target.get(
                "activationBundleMemberRole").getAsString());
        assertTrue(target.get("targetReplayRequired").getAsBoolean());
        assertTrue(target.get("observationOnlyReplay").getAsBoolean());
        assertFalse(target.get("concreteReplayOnly").getAsBoolean());
        assertEquals(0, target.getAsJsonArray("modelAssignments").size());
        assertEquals(0, target.getAsJsonArray("forcedBranches").size());
        assertEquals(0, target.getAsJsonArray(
                "replayMaterializations").size());
        assertEquals("ACT.T", target.getAsJsonObject(
                "directedTargetQuery").get("activationId").getAsString());
    }

    @Test
    public void finalReportCannotBeReusedAsBootstrapAuthority()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject report = fixture.reach.deepCopy();
        report.addProperty("extractionMode", "FINAL_REPORT");
        report.addProperty("replayBootstrapOnly", false);
        report.addProperty("reportableFinalReachCondition", true);
        Files.write(fixture.reachPath, report.toString().getBytes(
                StandardCharsets.UTF_8));

        try {
            ConcolicPrimitiveBootstrapProjector.project(fixture.arguments());
            fail("final reach report must not authorize bootstrap replay");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage().contains(
                    "BOOLEAN_REPORT_IS_NOT_AN_EXACT_BOOTSTRAP_MODEL"));
        }
    }

    private static Fixture fixture() throws Exception {
        Path directory = Files.createTempDirectory("primitive-bootstrap-");
        Path smt = directory.resolve("bootstrap.smt2");
        Path composition = directory.resolve("composition.json");
        Path reach = directory.resolve("reach.json");
        Path summaries = directory.resolve("summaries.jsonl");
        Path activations = directory.resolve("activations.jsonl");
        Path target = directory.resolve("target.jsonl");
        Path fatal = directory.resolve("fatal.jsonl");
        Path output = directory.resolve("activation-plan.jsonl");
        Path projection = directory.resolve("projection.json");

        String smtText = "(set-logic ALL)\n"
                + "(declare-const xa Int)\n"
                + "(declare-const xb Int)\n"
                + "(declare-const ca0 Bool)\n"
                + "(declare-const ca1 Bool)\n"
                + "(declare-const cb0 Bool)\n"
                + "(declare-const cb1 Bool)\n"
                + "(assert (= ca0 (= xa 0)))\n"
                + "(assert (= ca1 (= xa 1)))\n"
                + "(assert (= cb0 (= xb 0)))\n"
                + "(assert (= cb1 (= xb 1)))\n"
                + "(assert (= xa 1))\n"
                + "(assert (= xb 1))\n"
                + "(check-sat)\n";
        Files.write(smt, smtText.getBytes(StandardCharsets.UTF_8));

        JsonObject compositionJson = new JsonObject();
        compositionJson.addProperty("schemaVersion", 1);
        compositionJson.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        compositionJson.addProperty("compositionStage", "BOOTSTRAP");
        compositionJson.addProperty("structurallyComplete", true);
        compositionJson.addProperty("eligibleForBootstrapModel", true);
        compositionJson.addProperty("fatalReplayValidated", false);
        compositionJson.addProperty("complete", false);
        compositionJson.addProperty(
                "eligibleToReportAutomaticRelationship", false);
        compositionJson.addProperty("caseProjectionCatalogComplete", true);
        JsonArray cases = new JsonArray();
        cases.add(pathCase("REGION.A", "CASE.A.0", "ca0",
                "SUMMARY.A.0", "ACT.A.0", "REGION.A.in.0", "xa",
                "M_Z_field_REGION.A.in.0_java/lang/Boolean"));
        cases.add(pathCase("REGION.A", "CASE.A.1", "ca1",
                "SUMMARY.A.1", "ACT.A.1", "REGION.A.in.0", "xa",
                "M_Z_field_REGION.A.in.0_java/lang/Boolean"));
        cases.add(pathCase("REGION.B", "CASE.B.0", "cb0",
                "SUMMARY.B.0", "ACT.B.0", "REGION.B.in.0", "xb",
                "M_Z_field_REGION.B.in.0_java/lang/Boolean"));
        cases.add(pathCase("REGION.B", "CASE.B.1", "cb1",
                "SUMMARY.B.1", "ACT.B.1", "REGION.B.in.0", "xb",
                "M_Z_field_REGION.B.in.0_java/lang/Boolean"));
        compositionJson.add("caseProjectionCatalog", cases);
        compositionJson.addProperty("caseProjectionCatalogCount", 4);
        Files.write(composition, compositionJson.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject reachJson = new JsonObject();
        reachJson.addProperty("schemaVersion", 1);
        reachJson.addProperty("kind", "BOOLEAN_REACH_CONDITION_REPORT");
        reachJson.addProperty("extractionMode", "BOOTSTRAP_REPLAY_MODEL");
        reachJson.addProperty("replayBootstrapOnly", true);
        reachJson.addProperty("reportableFinalReachCondition", false);
        reachJson.addProperty("complete", true);
        reachJson.addProperty("status",
                "COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL");
        reachJson.addProperty("composedSmtSha256", sha256(smt));
        reachJson.add("composedSmtArtifact", artifact(smt));
        reachJson.add("compositionManifestArtifact", artifact(composition));
        JsonArray roots = new JsonArray();
        roots.add(root("REGION.A", "REGION.A.in.0", "xa"));
        roots.add(root("REGION.B", "REGION.B.in.0", "xb"));
        reachJson.add("rootBooleanInputs", roots);
        JsonObject valuation = new JsonObject();
        valuation.addProperty("ordinal", 3);
        valuation.addProperty("valuationKey", "11");
        valuation.addProperty("solverStatus", "sat");
        valuation.addProperty("reachesBug", true);
        JsonArray values = new JsonArray();
        values.add(valuation("REGION.A.in.0", "xa", true));
        values.add(valuation("REGION.B.in.0", "xb", true));
        valuation.add("assignments", values);
        JsonArray truth = new JsonArray();
        truth.add(valuation);
        reachJson.add("truthTable", truth);
        Files.write(reach, reachJson.toString().getBytes(
                StandardCharsets.UTF_8));

        StringBuilder summaryRows = new StringBuilder();
        StringBuilder activationRows = new StringBuilder();
        for (String[] row : new String[][]{
                {"REGION.A", "SUMMARY.A.0", "ACT.A.0"},
                {"REGION.A", "SUMMARY.A.1", "ACT.A.1"},
                {"REGION.B", "SUMMARY.B.0", "ACT.B.0"},
                {"REGION.B", "SUMMARY.B.1", "ACT.B.1"}}) {
            summaryRows.append(summary(row[0], row[1], row[2])).append('\n');
            activationRows.append(activation(row[0], row[2])).append('\n');
        }
        Files.write(summaries, summaryRows.toString().getBytes(
                StandardCharsets.UTF_8));
        Files.write(activations, activationRows.toString().getBytes(
                StandardCharsets.UTF_8));

        JsonObject targetActivation = new JsonObject();
        targetActivation.addProperty("activationId", "ACT.T");
        targetActivation.addProperty("regionId", "REGION.T");
        targetActivation.addProperty("regionInstanceId", "INSTANCE.T");
        targetActivation.addProperty("rootMethod", "<fixture.T: void run()>");
        targetActivation.addProperty("replayable", true);
        targetActivation.addProperty("symbolicReady", true);
        Files.write(target, (targetActivation + "\n").getBytes(
                StandardCharsets.UTF_8));
        JsonObject fatalQuery = fatal();
        Files.write(fatal, (fatalQuery + "\n").getBytes(
                StandardCharsets.UTF_8));
        return new Fixture(smt, composition, reach, summaries, activations,
                target, fatal, output, projection, reachJson);
    }

    private static JsonObject pathCase(String region, String caseId,
                                       String selector, String summary,
                                       String activation, String port,
                                       String solver, String engine) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "GUARDED_CASE_PROJECTION_CATALOG");
        result.addProperty("regionId", region);
        result.addProperty("caseId", caseId);
        result.addProperty("sourceSummaryId", summary);
        result.addProperty("sourceActivationId", activation);
        result.addProperty("selectorSolverSymbol", selector);
        result.addProperty("complete", true);
        JsonObject mapping = new JsonObject();
        mapping.addProperty("canonicalPort", port);
        mapping.addProperty("solverTerm", solver);
        mapping.addProperty("rawEngineSymbol", engine);
        mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        result.add("rawEngineSymbolMappings", mappings);
        return result;
    }

    private static JsonObject root(String region, String port, String solver) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", region);
        result.addProperty("portId", port);
        result.addProperty("javaTypeDescriptor", "Ljava/lang/Boolean;");
        result.addProperty("solverTerm", solver);
        result.addProperty("root", true);
        result.addProperty("upstreamSupplied", false);
        return result;
    }

    private static JsonObject valuation(String port, String solver,
                                        boolean value) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        result.addProperty("solverTerm", solver);
        result.addProperty("value", value);
        result.addProperty("solverLiteral", "(= " + solver + " "
                + (value ? "1" : "0") + ")");
        return result;
    }

    private static JsonObject summary(String region, String summary,
                                      String activation) {
        JsonObject result = new JsonObject();
        result.addProperty("summaryId", summary);
        result.addProperty("activationId", activation);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + region);
        result.addProperty("valid", true);
        result.addProperty("relationallyComplete", true);
        return result;
    }

    private static JsonObject activation(String region, String activation) {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", activation);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + region);
        result.addProperty("rootMethod", "<fixture." + region
                + ": void run()>");
        result.addProperty("replayable", true);
        result.addProperty("symbolicReady", true);
        JsonObject action = new JsonObject();
        action.addProperty("symbol", region + ".in.0");
        action.addProperty("bindingMode", "LOCAL_DEFINITION");
        action.addProperty("method", "<fixture." + region
                + ": boolean input()>");
        action.addProperty("local", "$z0");
        JsonArray actions = new JsonArray();
        actions.add(action);
        result.add("materializations", actions);
        return result;
    }

    private static JsonObject fatal() {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", "ACT.T");
        result.addProperty("regionId", "REGION.T");
        result.addProperty("regionInstanceId", "INSTANCE.T");
        result.addProperty("siteId", "<fixture.T: void run()>#u4");
        result.addProperty("occurrence", 1);
        result.addProperty("desiredOutcome", true);
        result.addProperty("readyForSolver", true);
        JsonObject condition = new JsonObject();
        condition.addProperty("_type", "SymbolExpression");
        condition.addProperty("_java_type", "Z");
        condition.addProperty("_exp", "fatal");
        result.add("originalTargetCondition", condition.deepCopy());
        result.add("negatedTargetCondition", condition.deepCopy());
        JsonArray constraints = new JsonArray();
        constraints.add(condition);
        result.add("constraints", constraints);
        JsonObject context = new JsonObject();
        context.addProperty("regionInstanceId", "INSTANCE.T");
        result.add("symbolicContext", context);
        return result;
    }

    private static JsonObject artifact(Path path) throws Exception {
        JsonObject result = new JsonObject();
        result.addProperty("path", path.toString());
        result.addProperty("sha256", sha256(path));
        result.addProperty("sizeBytes", Files.size(path));
        return result;
    }

    private static String sha256(Path path) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        StringBuilder result = new StringBuilder();
        for (byte value : digest.digest(Files.readAllBytes(path))) {
            result.append(String.format("%02x", value & 0xff));
        }
        return result.toString();
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }

    private static final class Fixture {
        private final Path smt;
        private final Path composition;
        private final Path reachPath;
        private final Path summaries;
        private final Path activations;
        private final Path target;
        private final Path fatal;
        private final Path output;
        private final Path projection;
        private final JsonObject reach;

        private Fixture(Path smt, Path composition, Path reach,
                        Path summaries, Path activations, Path target,
                        Path fatal, Path output, Path projection,
                        JsonObject reachJson) {
            this.smt = smt;
            this.composition = composition;
            this.reachPath = reach;
            this.summaries = summaries;
            this.activations = activations;
            this.target = target;
            this.fatal = fatal;
            this.output = output;
            this.projection = projection;
            this.reach = reachJson;
        }

        private ConcolicPrimitiveBootstrapProjector.Arguments arguments() {
            return ConcolicPrimitiveBootstrapProjector.Arguments.parse(
                    new String[]{
                            "--smt", smt.toString(),
                            "--composition-manifest", composition.toString(),
                            "--reach-report", reachPath.toString(),
                            "--summaries", summaries.toString(),
                            "--activations", activations.toString(),
                            "--target-activations", target.toString(),
                            "--fatal-query", fatal.toString(),
                            "--output", output.toString(),
                            "--manifest", projection.toString(),
                            "--z3", "z3",
                            "--timeout-ms", "10000"
                    });
        }
    }
}
