package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
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
        JsonObject solverIdentity = result.manifest.getAsJsonObject(
                "solverIdentity");
        assertTrue(solverIdentity.get("version").getAsString().contains(
                "Z3"));
        assertTrue(Paths.get(solverIdentity.get("resolvedPath").getAsString())
                .isAbsolute());
        if (solverIdentity.get("regularFile").getAsBoolean()) {
            assertEquals(64, solverIdentity.get("binarySha256")
                    .getAsString().length());
        }
        assertEquals(sha256(fixture.summaries), result.manifest
                .getAsJsonObject("summaryLedgerArtifact").get("sha256")
                .getAsString());
        assertEquals(sha256(fixture.activations), result.manifest
                .getAsJsonObject("producerActivationLedgerArtifact")
                .get("sha256").getAsString());
        assertEquals(sha256(fixture.target), result.manifest
                .getAsJsonObject("targetActivationPlanArtifact")
                .get("sha256").getAsString());
        assertEquals(sha256(fixture.fatal), result.manifest
                .getAsJsonObject("fatalQueryArtifact").get("sha256")
                .getAsString());
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
            assertTrue(producer.get("receiverRuntimeClass").getAsString()
                    .startsWith("fixture.REGION."));
            assertEquals(1, producer.get(
                    "invocationOrdinalWithinContext").getAsInt());
            assertFalse(producer.get("threadIdSelectionUsed")
                    .getAsBoolean());
            assertTrue(producer.get("concreteReplayOnly").getAsBoolean());
            JsonArray assignments = producer.getAsJsonArray(
                    "modelAssignments");
            assertEquals(1, assignments.size());
            assertEquals("true", assignments.get(0).getAsJsonObject()
                    .get("value").getAsString());
            assertEquals("Z3_PATH_FLIP_MODEL", assignments.get(0)
                    .getAsJsonObject().get("authority").getAsString());
            assertEquals(64, assignments.get(0).getAsJsonObject()
                    .get("targetActionIdentitySha256").getAsString()
                    .length());
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
        assertEquals("fixture.ConsumerThread", target.get(
                "receiverRuntimeClass").getAsString());
        assertEquals("rpc-consumer", target.get("threadName")
                .getAsString());
        assertEquals(1, target.get("invocationOrdinalWithinContext")
                .getAsInt());
        assertFalse(target.get("threadIdSelectionUsed").getAsBoolean());
        assertEquals("TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1",
                target.get("rootContextSelectionAuthority").getAsString());
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

    @Test
    public void tamperedDefinitionIdentityCannotJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        activation.getAsJsonArray("materializations").get(0)
                .getAsJsonObject().getAsJsonArray("definitionSites").get(0)
                .getAsJsonObject().addProperty("local", "$z9");
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "LOCAL_DEFINITION_ACTION_SITE_MISMATCH");
    }

    @Test
    public void resolvedCallReturnDefinitionCanJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        ConcolicPrimitiveBootstrapProjector.Result result =
                ConcolicPrimitiveBootstrapProjector.project(
                        fixture.arguments());

        assertTrue(result.manifest.toString(), result.manifest.get(
                "complete").getAsBoolean());
    }

    @Test
    public void callReturnWithoutSourceBindingModeCannotJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        action.remove("sourceBindingMode");
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "LOCAL_DEFINITION_ACTION_IDENTITY_INCOMPLETE");
    }

    @Test
    public void deferredCallReturnCannotJoinSelectedCase()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        action.addProperty("deferredResolution", true);
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "ROOT_INPUT_HAS_NO_REAL_MATERIALIZATION");
    }

    @Test
    public void mislabeledLocalCellCannotJoinAsCallReturnDefinition()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject activation = jsonlRow(fixture.activations,
                "activationId", "ACT.A.1");
        JsonObject action = activation.getAsJsonArray("materializations")
                .get(0).getAsJsonObject();
        makeCallReturn(action);
        action.addProperty("cell", "<fixture.REGION.A: boolean input()>"
                + "::$z0");
        replaceJsonlRow(fixture.activations, "activationId", "ACT.A.1",
                activation);

        expectFailure(fixture.arguments(),
                "LOCAL_DEFINITION_ACTION_IDENTITY_INCOMPLETE");
    }

    @Test
    public void mainWritesOneCompactJsonObjectPerActivationLine()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();

        ConcolicPrimitiveBootstrapProjector.main(
                fixture.commandLine(Paths.get("z3")));

        List<String> lines = Files.readAllLines(fixture.output,
                StandardCharsets.UTF_8);
        assertEquals(3, lines.size());
        for (String line : lines) {
            assertTrue(JsonParser.parseString(line).isJsonObject());
        }
    }

    @Test
    public void summaryAdmissionMustOwnSelectedMaterialization()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject summary = jsonlRow(fixture.summaries, "summaryId",
                "SUMMARY.A.1");
        summary.getAsJsonObject("inputMaterializationAdmission")
                .add("observedSymbolizedInputs", new JsonArray());
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT");

        fixture = fixture();
        summary = jsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1");
        JsonObject requirement = new JsonObject();
        requirement.addProperty("inputPort", "REGION.A.in.0");
        JsonArray requirements = new JsonArray();
        requirements.add(requirement);
        summary.getAsJsonObject("inputMaterializationAdmission")
                .add("unforcedEnvironmentValidationRequirements",
                        requirements);
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT");

        fixture = fixture();
        summary = jsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1");
        JsonArray fallbacks = new JsonArray();
        fallbacks.add("REGION.A.in.0");
        summary.getAsJsonObject("inputMaterializationAdmission")
                .add("admittedConcreteFallbackInputs", fallbacks);
        replaceJsonlRow(fixture.summaries, "summaryId", "SUMMARY.A.1",
                summary);

        expectFailure(fixture.arguments(),
                "SELECTED_SUMMARY_INPUT_ADMISSION_NOT_EXACT");
    }

    @Test
    public void selectedCaseMustBelongToIncludedCompositionInput()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject composition = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.composition),
                StandardCharsets.UTF_8)).getAsJsonObject();
        composition.getAsJsonArray("caseProjectionCatalog").get(1)
                .getAsJsonObject().addProperty("compositionInputSummaryId",
                "SUMMARY.A.NOT_INCLUDED");
        Files.write(fixture.composition, composition.toString().getBytes(
                StandardCharsets.UTF_8));
        JsonObject report = fixture.reach.deepCopy();
        report.add("compositionManifestArtifact",
                artifact(fixture.composition));
        Files.write(fixture.reachPath, report.toString().getBytes(
                StandardCharsets.UTF_8));

        expectFailure(fixture.arguments(),
                "SELECTED_SOURCE_SUMMARY_NOT_IN_COMPOSITION_INPUT");
    }

    @Test
    public void targetActivationMustMatchFatalBranchIdentity()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject target = jsonlRow(fixture.target, "activationId", "ACT.T");
        target.getAsJsonObject("targetBranch").addProperty("occurrence", 2);
        replaceJsonlRow(fixture.target, "activationId", "ACT.T", target);

        expectFailure(fixture.arguments(),
                "TARGET_ACTIVATION_EXACT_BINDING_MISMATCH");
    }

    @Test
    public void reachSolverLiteralCannotInjectSmt()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        JsonObject report = fixture.reach.deepCopy();
        report.getAsJsonArray("truthTable").get(0).getAsJsonObject()
                .getAsJsonArray("assignments").get(0).getAsJsonObject()
                .addProperty("solverLiteral",
                        "(= xa 1)) (assert false) (assert (= xa 1)");
        Files.write(fixture.reachPath, report.toString().getBytes(
                StandardCharsets.UTF_8));

        expectFailure(fixture.arguments(),
                "INVALID_BOOTSTRAP_VALUATION_ASSIGNMENT");
    }

    @Test
    public void nonzeroSolverExitAlwaysFailsProjection() throws Exception {
        Fixture fixture = fixture();
        Path solver = fixture.output.getParent().resolve("fake-z3");
        Files.write(solver, ("#!/bin/sh\n"
                + "if [ \"$1\" = \"-version\" ]; then\n"
                + "  echo 'Z3 version fixture'\n"
                + "  exit 0\n"
                + "fi\n"
                + "exit 7\n").getBytes(StandardCharsets.UTF_8));
        assertTrue(solver.toFile().setExecutable(true));

        expectFailure(fixture.arguments(solver),
                "Bootstrap model projection solver failed");
    }

    @Test
    public void solverVersionMustAttestZ3Identity() throws Exception {
        Fixture fixture = fixture();
        Path solver = fixture.output.getParent().resolve("not-z3");
        Files.write(solver, ("#!/bin/sh\n"
                + "echo 'generic solver version fixture'\n"
                + "exit 0\n").getBytes(StandardCharsets.UTF_8));
        assertTrue(solver.toFile().setExecutable(true));

        expectFailure(fixture.arguments(solver),
                "Solver identity is not Z3");
    }

    private static void expectFailure(
            ConcolicPrimitiveBootstrapProjector.Arguments arguments,
            String expected) throws Exception {
        try {
            ConcolicPrimitiveBootstrapProjector.project(arguments);
            fail("expected projection failure containing " + expected);
        } catch (java.io.IOException failure) {
            assertTrue(failure.getMessage(), failure.getMessage().contains(
                    expected));
        }
    }

    private static JsonObject jsonlRow(Path path, String field, String id)
            throws Exception {
        for (String line : Files.readAllLines(path,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = JsonParser.parseString(line).getAsJsonObject();
            if (id.equals(row.get(field).getAsString())) return row;
        }
        throw new AssertionError("missing " + field + "=" + id);
    }

    private static void replaceJsonlRow(Path path, String field, String id,
                                        JsonObject replacement)
            throws Exception {
        List<String> lines = Files.readAllLines(path,
                StandardCharsets.UTF_8);
        boolean replaced = false;
        for (int index = 0; index < lines.size(); index++) {
            if (lines.get(index).trim().isEmpty()) continue;
            JsonObject row = JsonParser.parseString(lines.get(index))
                    .getAsJsonObject();
            if (id.equals(row.get(field).getAsString())) {
                lines.set(index, replacement.toString());
                replaced = true;
            }
        }
        if (!replaced) throw new AssertionError("missing " + field + "=" + id);
        Files.write(path, lines, StandardCharsets.UTF_8);
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

        JsonObject fatalQuery = fatal();
        Files.write(fatal, (fatalQuery + "\n").getBytes(
                StandardCharsets.UTF_8));

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
        compositionJson.addProperty("fatalRegion", "REGION.T");
        compositionJson.addProperty("fatalActivation", "ACT.T");
        compositionJson.addProperty("fatalRegionInstanceId", "INSTANCE.T");
        compositionJson.addProperty("fatalSite",
                "<fixture.T: void run()>#u4");
        compositionJson.addProperty("fatalOccurrence", 1);
        compositionJson.addProperty("fatalDesiredOutcome", true);
        compositionJson.addProperty("fatalConditionCount", 1);
        compositionJson.addProperty("validatedSummaryId", "");
        compositionJson.addProperty("validatedFatalReplaySummary", "");
        compositionJson.add("composedSmtArtifact", artifact(smt));
        compositionJson.add("fatalQueriesArtifact", artifact(fatal));
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
        for (com.google.gson.JsonElement element : cases) {
            JsonObject pathCase = element.getAsJsonObject();
            pathCase.addProperty("compositionInputSummaryId",
                    "REGION.A".equals(pathCase.get("regionId").getAsString())
                            ? "SUMMARY.A.MERGED" : "SUMMARY.B.MERGED");
        }
        compositionJson.add("caseProjectionCatalog", cases);
        compositionJson.addProperty("caseProjectionCatalogCount", 4);
        JsonArray included = new JsonArray();
        included.add("SUMMARY.A.MERGED");
        included.add("SUMMARY.B.MERGED");
        compositionJson.add("includedSummaries", included);
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
        targetActivation.addProperty("receiverType",
                "fixture.ConsumerThread");
        targetActivation.addProperty("receiverRuntimeClass",
                "fixture.ConsumerThread");
        targetActivation.addProperty("threadName", "rpc-consumer");
        targetActivation.addProperty("threadIdSelectionUsed", false);
        targetActivation.addProperty("invocationOrdinalWithinContext", 1);
        targetActivation.addProperty("rootContextSelectionAuthority",
                "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1");
        targetActivation.addProperty("replayable", true);
        targetActivation.addProperty("symbolicReady", true);
        targetActivation.addProperty("schedulerReady", true);
        targetActivation.addProperty("branchOverrideProhibited", true);
        JsonObject captureGoal = new JsonObject();
        captureGoal.addProperty("kind", "TARGET_BRANCH");
        captureGoal.addProperty("scope", "ONE_DIRECTED_BRANCH");
        targetActivation.add("captureGoal", captureGoal);
        JsonObject targetBranch = new JsonObject();
        targetBranch.addProperty("siteId", "<fixture.T: void run()>#u4");
        targetBranch.addProperty("occurrence", 1);
        targetBranch.addProperty("desiredOutcome", true);
        targetActivation.add("targetBranch", targetBranch);
        Files.write(target, (targetActivation + "\n").getBytes(
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
        result.addProperty("pathKey", "PATH." + caseId);
        result.addProperty("sourceSummaryId", summary);
        result.addProperty("sourceActivationId", activation);
        result.addProperty("selectorSolverSymbol", selector);
        result.addProperty("complete", true);
        result.addProperty("rawEngineSymbolMappingAuthority",
                "EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE");
        JsonObject mapping = new JsonObject();
        mapping.addProperty("canonicalPort", port);
        mapping.addProperty("solverTerm", solver);
        mapping.addProperty("rawEngineSymbol", engine);
        mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        result.add("rawEngineSymbolMappings", mappings);
        result.addProperty("rawEngineSymbolMappingCount", mappings.size());
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
        JsonObject admission = new JsonObject();
        admission.addProperty("complete", true);
        JsonArray one = new JsonArray();
        one.add(region + ".in.0");
        admission.add("globalSliceInputs", one.deepCopy());
        admission.add("requiredSliceInputs", one.deepCopy());
        admission.add("observedSymbolizedInputs", one.deepCopy());
        admission.add("pathInactiveSliceInputs", new JsonArray());
        admission.add("admittedObservedInputs", new JsonArray());
        admission.addProperty("admittedObservedInputAuthority",
                "SCHEDULED_OBSERVATION_ONLY_INPUT_PLUS_UNIQUE_COMPLETE_"
                        + "FIRST_CONTAINER_RUNTIME_EVIDENCE_V1");
        admission.add("admittedConcreteFallbackInputs", new JsonArray());
        admission.add("admittedVmIntrinsicPlaceholderInputs",
                new JsonArray());
        admission.add("unforcedEnvironmentValidationRequirements",
                new JsonArray());
        admission.add("failures", new JsonArray());
        admission.addProperty("authority",
                "STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                        + "TRANSFORMER_RUNTIME_PATH_PROOFS_AND_EXPLICIT_"
                        + "CONCRETE_FALLBACKS");
        result.add("inputMaterializationAdmission", admission);
        return result;
    }

    private static JsonObject activation(String region, String activation) {
        JsonObject result = new JsonObject();
        result.addProperty("activationId", activation);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", "INSTANCE." + region);
        result.addProperty("rootMethod", "<fixture." + region
                + ": void run()>");
        result.addProperty("receiverType", "fixture." + region
                + ".Worker");
        result.addProperty("receiverRuntimeClass", "fixture." + region
                + ".Worker");
        result.addProperty("threadName", "rpc-producer-" + region);
        result.addProperty("threadIdSelectionUsed", false);
        result.addProperty("invocationOrdinalWithinContext", 1);
        result.addProperty("rootContextSelectionAuthority",
                "TRACE_EXACT_RECEIVER_RUNTIME_CLASS_AND_OPTIONAL_"
                        + "THREAD_NAME_CONTEXT_ORDINAL_V1");
        result.addProperty("replayable", true);
        result.addProperty("symbolicReady", true);
        JsonObject action = new JsonObject();
        action.addProperty("symbol", region + ".in.0");
        action.addProperty("bindingMode", "LOCAL_DEFINITION");
        action.addProperty("location", "REGION_LIVE_IN");
        String method = "<fixture." + region + ": boolean input()>";
        action.addProperty("method", method);
        action.addProperty("local", "$z0");
        action.addProperty("cell", method + "::$z0");
        action.addProperty("definitionAuthority",
                "STATIC_DATAFLOW_DEF_SITE");
        JsonObject definition = new JsonObject();
        definition.addProperty("method", method);
        definition.addProperty("local", "$z0");
        definition.addProperty("unitIndex", 2);
        definition.addProperty("siteId", method + "#u2");
        JsonArray definitions = new JsonArray();
        definitions.add(definition);
        action.add("definitionSites", definitions);
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

    private static void makeCallReturn(JsonObject action) {
        action.addProperty("cell",
                "<fixture.Source: boolean read()>.return");
        action.addProperty("sourceKind", "OPAQUE_CALL");
        action.addProperty("projection", "return");
        action.addProperty("location", "CALL_RETURN");
        action.addProperty("sourceBindingMode", "CALL_RETURN_DEFINITION");
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
            return arguments(Paths.get("z3"));
        }

        private ConcolicPrimitiveBootstrapProjector.Arguments arguments(
                Path solver) {
            return ConcolicPrimitiveBootstrapProjector.Arguments.parse(
                    commandLine(solver));
        }

        private String[] commandLine(Path solver) {
            return new String[]{
                    "--smt", smt.toString(),
                    "--composition-manifest", composition.toString(),
                    "--reach-report", reachPath.toString(),
                    "--summaries", summaries.toString(),
                    "--activations", activations.toString(),
                    "--target-activations", target.toString(),
                    "--fatal-query", fatal.toString(),
                    "--output", output.toString(),
                    "--manifest", projection.toString(),
                    "--z3", solver.toString(),
                    "--timeout-ms", "10000"
            };
        }
    }
}
