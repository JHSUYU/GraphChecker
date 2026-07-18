package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class ConcolicSmtComposerTest {
    @Test
    public void cliBindsExactInputsAndOutputsWithoutDigestCycle()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            Path relationshipsPath = folder.getRoot().toPath().resolve(
                    "relationships.json");
            ConcolicSmtComposer.main(new String[]{
                    "--fatal-query", fixture.fatal.toString(),
                    "--summaries", fixture.summaries.toString(),
                    "--regions", fixture.regions.toString(),
                    "--merge-plan", fixture.merge.toString(),
                    "--output", fixture.output.toString(),
                    "--manifest", fixture.manifest.toString(),
                    "--relationships", relationshipsPath.toString(),
                    "--fatal-region", "REGION.F",
                    "--activation-id", "ACT.F"
            });
            JsonObject manifest = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.manifest),
                    StandardCharsets.UTF_8)).getAsJsonObject();
            JsonObject relationships = JsonParser.parseString(new String(
                    Files.readAllBytes(relationshipsPath),
                    StandardCharsets.UTF_8)).getAsJsonObject();

            assertTrue(manifest.get("compositionBindingId").getAsString()
                    .matches("[0-9a-f]{64}"));
            assertEquals(manifest.get("compositionBindingId").getAsString(),
                    relationships.get("compositionBindingId").getAsString());
            assertTrue(manifest.has("fatalRegionInstanceId"));
            assertTrue(manifest.has("fatalOccurrence"));
            assertTrue(manifest.has("fatalDesiredOutcome"));
            assertTrue(manifest.has("validatedSummaryId"));
            assertEquals(1, manifest.getAsJsonArray(
                    "summaryInputArtifacts").size());
            BooleanReachConditionExtractor.validateArtifactBindings(
                    fixture.output, fixture.regions, relationshipsPath,
                    manifest, relationships);
        } finally {
            folder.delete();
        }
    }

    @Test
    public void tokenValueRefWitnessRequiresImporterCertification() {
        JsonObject record = new JsonObject();
        record.addProperty("valueExpressionAuthority",
                "ACTIVATION_LOCAL_OBJECT_TOKEN_REF_WITNESS_V1");
        record.addProperty("objectTokenScope", "ACT.P");
        record.addProperty("valueObjectToken", 103L);
        record.addProperty("valueExpressionWitnessSchemaVersion", 1);
        record.addProperty("valueExpressionWitnessKind",
                "ACTIVATION_LOCAL_REF_SYMBOL_WITNESS");
        record.addProperty("valueExpressionWitnessObjectToken", 103L);
        record.addProperty("valueExpressionWitnessObjectTokenScope", "ACT.P");
        record.addProperty("valueExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        record.addProperty("valueExpressionWitnessCertified", true);
        record.addProperty("valueExpressionWitnessCertificationAuthority",
                "IMPORTER_EXACT_ACTIVATION_TOKEN_AND_"
                        + "DYNAMIC_FIELD_OWNER_JOIN_V1");
        record.addProperty("valueExpressionWitnessCertifiedObjectToken", 103L);
        record.addProperty("valueExpressionWitnessCertifiedObjectTokenScope",
                "ACT.P");
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "L");
        expression.addProperty("_exp",
                "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T103");
        record.add("valueExpression", expression);

        assertTrue(ConcolicSmtComposer
                .authenticatedValueRefWitnessForTests(record,
                        "valueExpression", "valueExpressionAuthority",
                        "valueObjectToken"));
        record.remove("valueExpressionWitnessCertified");
        assertFalse(ConcolicSmtComposer
                .authenticatedValueRefWitnessForTests(record,
                        "valueExpression", "valueExpressionAuthority",
                        "valueObjectToken"));
        record.addProperty("valueExpressionAuthority", "");
        assertFalse("witness-shaped symbols cannot bypass the authority gate",
                ConcolicSmtComposer.authenticatedValueRefWitnessForTests(record,
                        "valueExpression", "valueExpressionAuthority",
                        "valueObjectToken"));
    }

    @Test
    public void missingInstanceScopedContextNeverFallsBackToGlobalPlan()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.remove("symbolicContext");
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(result.manifest.toString(), result.manifest.get(
                    "complete").getAsBoolean());
            assertFalse(result.manifest.get(
                    "instanceScopedSymbolicContext").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "MissingTargetInstanceSymbolicContext"));
            assertEquals(0, result.manifest.get(
                    "readFromConstraintCount").getAsInt());
            assertFalse(result.smtLib.contains(
                    "port__REGION_P_out_0 port__REGION_F_in_0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesFatalPathProducerEffectAndReadFrom() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertFalse(result.manifest.get("fatalReplayValidated")
                    .getAsBoolean());
            assertEquals("BOOTSTRAP", result.manifest.get(
                    "compositionStage").getAsString());
            assertTrue(result.manifest.get("eligibleForBootstrapModel")
                    .getAsBoolean());
            assertFalse(result.manifest.get(
                    "eligibleToReportAutomaticRelationship").getAsBoolean());
            assertTrue(result.relationships.get("eligibleForBootstrapModel")
                    .getAsBoolean());
            assertFalse(result.relationships.get(
                    "eligibleForAutomaticVerification").getAsBoolean());
            assertEquals("STRUCTURALLY_COMPLETE_BOOTSTRAP_COMPOSITION",
                    result.manifest.get("status").getAsString());
            assertEquals(1, result.manifest.get(
                    "readFromConstraintCount").getAsInt());
            assertEquals(1, result.manifest.get(
                    "orderConstraintCount").getAsInt());
            assertEquals(1, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertTrue(result.manifest.getAsJsonArray(
                    "resolvedProducerKeys").toString().contains(
                    "REGION.P@fixture#call1"));
            assertFalse(result.manifest.getAsJsonArray("relevantRegions")
                    .toString().contains("REGION.D"));
            assertTrue(result.smtLib.contains("(map_select "));
            assertTrue(result.smtLib.contains("(map_put "));
            assertTrue(result.smtLib.contains(
                    "port__REGION_P_out_0 port__REGION_F_in_0"));
            assertTrue(result.smtLib.contains("(check-sat)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void missingProducerIsExplicitAndNeverReportedComplete()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertEquals("COMPOSITION_WITH_EXPLICIT_GAPS",
                    result.manifest.get("status").getAsString());
            assertTrue(result.manifest.getAsJsonArray(
                    "missingSummaryRegions").toString().contains("REGION.P"));
            assertTrue(result.smtLib.contains("summary_missing__REGION_P"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mapLookupPlaceholderKeyIsExplicitlyUnsupported()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonObject lookup = fatal.getAsJsonArray("constraints").get(0)
                    .getAsJsonObject();
            lookup.getAsJsonArray("_param_list").set(1,
                    placeholderExpression("java/lang/String.split", 3));
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertFalse(result.manifest.get(
                    "eligibleToReportAutomaticRelationship").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "PlaceholderExpression:java/lang/String.split#3"));
            assertTrue(result.smtLib.contains("(check-sat)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void registersAuthenticatedVmPlaceholderInFatalScope()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String cell = vmCurrentTimeCell();
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8", cell));
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.getAsJsonArray("constraints").add(binaryCondition(
                    placeholderExpression("currentTimeMills", 3), ">",
                    constant("J", "Y_J_0")));
            addVmPlaceholderCertificate(fatal, "REGION.F.in.8", 3);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "PlaceholderExpression"));
            assertTrue(result.smtLib.contains(
                    "sym__port__REGION_F_in_8__int"));
            assertEquals(0, countDeclarationLines(result.smtLib,
                    "placeholder__", "currentTimeMills_3"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void registersAuthenticatedVmPlaceholderInPlainSummaryScope()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.6", vmCurrentTimeCell()));
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    placeholderExpression("currentTimeMills", 3), ">",
                    constant("J", "Y_J_0")));
            addVmPlaceholderCertificate(summary, "REGION.P.in.6", 3);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "PlaceholderExpression"));
            assertTrue(result.smtLib.contains(
                    "sym__port__REGION_P_in_6__int"));
            assertEquals(0, countDeclarationLines(result.smtLib,
                    "placeholder__", "currentTimeMills_3"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergerPreservesAndComposerRegistersCaseLocalVmPlaceholders()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.6", vmCurrentTimeCell()));
            JsonObject positive = producerSummary(singlePutEffect(), true);
            positive.add("captureGoal",
                    RegionCaptureGoal.outputClosure().toJson());
            positive.add("requestedOutput",
                    requestedOutput("REGION.P.out.0"));
            positive.getAsJsonArray("pathCondition").add(binaryCondition(
                    placeholderExpression("currentTimeMills", 3), ">",
                    constant("J", "Y_J_0")));
            addVmPlaceholderCertificate(positive, "REGION.P.in.6", 3);

            JsonObject nonPositive = positive.deepCopy();
            nonPositive.addProperty("summaryId", "SUMMARY.P.TIME.SECOND");
            nonPositive.addProperty("activationId", "ACT.P.TIME.SECOND");
            nonPositive.add("pathCondition", new JsonArray());
            nonPositive.getAsJsonArray("pathCondition").add(binaryCondition(
                    placeholderExpression("currentTimeMills", 7), "<=",
                    constant("J", "Y_J_0")));
            addVmPlaceholderCertificate(nonPositive,
                    "REGION.P.in.6", 7);
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(positive, nonPositive),
                    closedPathManifest());
            JsonArray cases = merged.summaries.get(0).getAsJsonObject(
                    "regionRelation").getAsJsonArray("cases");
            assertEquals(2, cases.size());
            for (JsonElement element : cases) {
                assertEquals(1, element.getAsJsonObject().getAsJsonArray(
                        "vmIntrinsicPlaceholderBindings").size());
                assertTrue(element.getAsJsonObject().getAsJsonObject(
                        "vmIntrinsicPlaceholderBindingAdmission")
                        .get("complete").getAsBoolean());
            }
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(2, result.manifest.get(
                    "guardedPathCaseCount").getAsInt());
            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "PlaceholderExpression"));
            assertEquals(1, countDeclarationLines(result.smtLib,
                    "sym__port__REGION_P_in_6__int"));
            assertEquals(0, countDeclarationLines(result.smtLib,
                    "placeholder__", "currentTimeMills"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsTamperedVmPlaceholderAdmissionCertificate()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.6", vmCurrentTimeCell()));
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    placeholderExpression("currentTimeMills", 3), ">",
                    constant("J", "Y_J_0")));
            addVmPlaceholderCertificate(summary, "REGION.P.in.6", 3);
            summary.getAsJsonObject(
                    "vmIntrinsicPlaceholderBindingAdmission")
                    .addProperty("bindingCount", 2);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "BINDING_ADMISSION_CERTIFICATE_INVALID"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "PlaceholderExpression:currentTimeMills#3"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void syntheticNnUsernameServerSplitParseFeedsUpstreamIntToMapGet()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonElement upstreamKey = symbol("I",
                    "M_I_field_REGION.P.in.2_example/Cache");
            JsonObject username = codecUsername(upstreamKey, " ",
                    "nn_username_suffix");

            // The producer summary exercises the standalone concat and
            // primitive-int toString encoding used before transport.
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.1", username.deepCopy());
            writeSummary(fixture, summary);

            // The structurally merged downstream provenance mirrors the
            // customized JDK schema: splitElement retains receiver, regex and
            // element index; parseInt retains that split expression.
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonObject serverKey = symbol("I",
                    "M_I_return_server_map_key");
            JsonObject parse = codecParse(upstreamKey.deepCopy(), " ",
                    null, 0, 10, serverKey.deepCopy());
            JsonArray oldConstraints = fatal.getAsJsonArray("constraints");
            JsonObject lookup = oldConstraints.get(0).getAsJsonObject();
            lookup.getAsJsonArray("_param_list").set(1,
                    serverKey.deepCopy());
            JsonArray constraints = new JsonArray();
            constraints.add(parse);
            for (JsonElement constraint : oldConstraints) {
                constraints.add(constraint);
            }
            fatal.add("constraints", constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertEquals(0, result.manifest.getAsJsonArray(
                    "unsupportedExpressions").size());
            String solverKey = declaredSymbolContaining(result.smtLib,
                    "server_map_key");
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");
            assertFalse(solverKey.isEmpty());
            assertTrue(fatalPath, fatalPath.contains("(= " + solverKey
                    + " sym__port__REGION_P_in_2__int)"));
            assertTrue(fatalPath, fatalPath.contains("(VMapInteger "
                    + solverKey
                    + ")"));
            assertTrue(result.smtLib.contains(
                    "(java_int_to_string sym__port__REGION_P_in_2__int)"));
            assertTrue(result.smtLib.contains("\" \""));
            assertTrue(result.smtLib.contains("java_int_range_"));
            assertFalse(result.smtLib.contains(
                    "uf__java_lang_Integer_parseInt"));
            assertFalse(result.smtLib.contains(
                    "uf__java_lang_String_splitElement"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void unprovedJavaCodecVariantsFailClosedWithoutCodecUfs()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonElement source = symbol("I",
                    "M_I_field_REGION.P.in.2_example/Cache");
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(codecParse(source.deepCopy(), " ", null, 0,
                    16, symbol("I", "M_I_bad_radix")));
            constraints.add(codecParse(source.deepCopy(), ".", null, 0,
                    10, symbol("I", "M_I_bad_regex")));
            constraints.add(codecParse(source.deepCopy(), " ", null, 1,
                    10, symbol("I", "M_I_bad_index")));
            constraints.add(codecParse(source.deepCopy(), " ", 1, 0,
                    10, symbol("I", "M_I_bad_limit")));
            constraints.add(codecParse(source.deepCopy(), "-", null, 0,
                    10, symbol("I", "M_I_bad_negative_boundary")));
            for (JsonElement constraint : fatal.getAsJsonArray(
                    "constraints")) {
                constraints.add(constraint);
            }
            fatal.add("constraints", constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String unsupported = result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString();

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertFalse(result.manifest.get(
                    "eligibleToReportAutomaticRelationship").getAsBoolean());
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:java/lang/Integer.parseInt:"
                            + "RADIX_NOT_LITERAL_10"));
            assertTrue(unsupported, unsupported.contains(
                    "ROUNDTRIP_NOT_PROVED_REGEX_NOT_SAFE_SINGLE_LITERAL"));
            assertTrue(unsupported, unsupported.contains(
                    "ROUNDTRIP_NOT_PROVED_INDEX_NOT_LITERAL_0"));
            assertTrue(unsupported, unsupported.contains(
                    "ROUNDTRIP_NOT_PROVED_LIMIT_DOES_NOT_PRESERVE_PREFIX"));
            assertTrue(unsupported, unsupported.contains(
                    "ROUNDTRIP_NOT_PROVED_"
                            + "DELIMITER_OCCURS_IN_JAVA_INT_TEXT"));
            assertFalse(result.smtLib.contains(
                    "uf__java_lang_Integer_parseInt"));
            assertFalse(result.smtLib.contains(
                    "uf__java_lang_String_splitElement"));
            assertTrue(result.smtLib.contains("unknown_codec_"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void requiresValidatedUnforcedReplayWhenFatalQueryIsReplayReady()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.addProperty("readyForReplay", true);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result missingReplay =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertFalse(missingReplay.manifest.get("complete").getAsBoolean());
            assertFalse(missingReplay.manifest.get("fatalReplayValidated")
                    .getAsBoolean());
            assertFalse(missingReplay.manifest.get(
                    "eligibleToReportAutomaticRelationship").getAsBoolean());

            JsonObject replay = new JsonObject();
            replay.addProperty("summaryId", "SUMMARY.F.REPLAY");
            replay.addProperty("activationId", "ACT.F");
            replay.addProperty("regionId", "REGION.F");
            replay.addProperty("regionInstanceId",
                    "REGION.F@fixture#call2");
            replay.addProperty("valid", true);
            replay.addProperty("targetReplayValidated", true);
            replay.addProperty("branchOverrideUsed", false);
            replay.add("captureGoal",
                    RegionCaptureGoal.targetBranch().toJson());
            JsonObject admission = new JsonObject();
            admission.addProperty("required", true);
            admission.addProperty("valid", true);
            admission.addProperty("branchOverrideAccepted", false);
            admission.addProperty("authority",
                    "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION");
            replay.add("executionAdmission", admission);
            Files.write(fixture.summaries, (replay + "\n").getBytes(
                    StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.APPEND);

            ConcolicSmtComposer.Result admitted =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertTrue(admitted.manifest.get("complete").getAsBoolean());
            assertTrue(admitted.manifest.get("fatalReplayValidated")
                    .getAsBoolean());
            assertEquals("VALIDATED_FINAL", admitted.manifest.get(
                    "compositionStage").getAsString());
            assertFalse(admitted.manifest.get("eligibleForBootstrapModel")
                    .getAsBoolean());
            assertEquals("SUMMARY.F.REPLAY", admitted.manifest.get(
                    "validatedFatalReplaySummary").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void freshValidatedFatalRequiresExactSummaryFormulaAndContext()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture positive = fixture(folder.newFolder("positive").toPath(),
                    false);
            FreshReplayPair admittedPair = installFreshReplay(positive);
            ConcolicSmtComposer.Result admitted =
                    ConcolicSmtComposer.compose(arguments(positive));
            ConcolicSmtComposer.FreshFatalArtifactValidation shared =
                    ConcolicSmtComposer.validateFreshFatalArtifact(
                            admittedPair.fatal,
                            java.util.Collections.singletonList(
                                    admittedPair.summary));
            assertTrue(shared.reason, shared.valid);
            assertEquals("SUMMARY.F.FRESH", shared.toJson().get(
                    "summaryId").getAsString());
            assertTrue(admitted.manifest.toString(), admitted.manifest.get(
                    "fatalReplayValidated").getAsBoolean());
            assertEquals("SUMMARY.F.FRESH", admitted.manifest.get(
                    "validatedFatalReplaySummary").getAsString());
            assertEquals(1, admitted.manifest.get(
                    "fatalReplayExactCandidateCount").getAsInt());

            Fixture missing = fixture(folder.newFolder("missing").toPath(),
                    false);
            installFreshReplay(missing);
            Files.write(missing.summaries, new byte[0]);
            assertFatalReplayGap(missing,
                    "EXACT_FATAL_REPLAY_SUMMARY_MISSING");

            Fixture stale = fixture(folder.newFolder("stale").toPath(),
                    false);
            FreshReplayPair stalePair = installFreshReplay(stale);
            stalePair.summary.addProperty("regionInstanceId", "F.OLD");
            writeSummary(stale, stalePair.summary);
            assertFatalReplayGap(stale,
                    "EXACT_FATAL_REPLAY_SUMMARY_MISSING");

            Fixture wrongId = fixture(folder.newFolder("wrong-id").toPath(),
                    false);
            FreshReplayPair wrongIdPair = installFreshReplay(wrongId);
            wrongIdPair.fatal.addProperty("validatedSummaryId",
                    "SUMMARY.F.OTHER");
            Files.write(wrongId.fatal,
                    (wrongIdPair.fatal + "\n").getBytes(StandardCharsets.UTF_8));
            assertFatalReplayGap(wrongId,
                    "EXACT_FATAL_REPLAY_SUMMARY_MISSING");

            Fixture tampered = fixture(folder.newFolder("tampered").toPath(),
                    false);
            FreshReplayPair tamperedPair = installFreshReplay(tampered);
            tamperedPair.fatal.getAsJsonArray("constraints").get(1)
                    .getAsJsonObject().addProperty("_op", "!=");
            tamperedPair.summary.getAsJsonObject("freshObservedTargetQuery")
                    .getAsJsonArray("constraints").get(1).getAsJsonObject()
                    .addProperty("_op", "!=");
            Files.write(tampered.fatal,
                    (tamperedPair.fatal + "\n").getBytes(StandardCharsets.UTF_8));
            writeSummary(tampered, tamperedPair.summary);
            assertFatalReplayGap(tampered,
                    "FRESH_FATAL_PREFIX_CONSTRAINT_MISMATCH");

            Fixture staleContext = fixture(folder.newFolder(
                    "stale-context").toPath(), false);
            FreshReplayPair contextPair = installFreshReplay(staleContext);
            contextPair.fatal.getAsJsonObject("symbolicContext")
                    .getAsJsonArray("versionedStateMerges").get(0)
                    .getAsJsonObject().getAsJsonArray("selectedBindings")
                    .get(0).getAsJsonObject().addProperty(
                            "toRegionInstance", "F.OLD");
            contextPair.summary.getAsJsonObject("freshObservedTargetQuery")
                    .getAsJsonObject("symbolicContext")
                    .getAsJsonArray("versionedStateMerges").get(0)
                    .getAsJsonObject().getAsJsonArray("selectedBindings")
                    .get(0).getAsJsonObject().addProperty(
                            "toRegionInstance", "F.OLD");
            Files.write(staleContext.fatal,
                    (contextPair.fatal + "\n").getBytes(StandardCharsets.UTF_8));
            writeSummary(staleContext, contextPair.summary);
            assertFatalReplayGap(staleContext,
                    "FRESH_FATAL_CONTEXT_ENDPOINT_MISMATCH");

            Fixture duplicate = fixture(folder.newFolder("duplicate")
                    .toPath(), false);
            FreshReplayPair duplicatePair = installFreshReplay(duplicate);
            Files.write(duplicate.summaries,
                    (duplicatePair.summary + "\n" + duplicatePair.summary
                            + "\n").getBytes(StandardCharsets.UTF_8));
            assertFatalReplayGap(duplicate,
                    "EXACT_FATAL_REPLAY_SUMMARY_NOT_UNIQUE");
        } finally {
            folder.delete();
        }
    }

    private static void assertFatalReplayGap(Fixture fixture, String reason)
            throws Exception {
        ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                arguments(fixture));
        assertFalse(result.manifest.get("fatalReplayValidated")
                .getAsBoolean());
        assertEquals(reason, result.manifest.get("fatalReplayGap")
                .getAsString());
        assertFalse(result.manifest.get(
                "eligibleToReportAutomaticRelationship").getAsBoolean());
    }

    private static FreshReplayPair installFreshReplay(Fixture fixture)
            throws Exception {
        JsonObject fatal = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.fatal), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        String instance = "REGION.F@fixture#call2";
        fatal.addProperty("regionInstanceId", instance);
        fatal.addProperty("occurrence", 1);
        fatal.addProperty("desiredOutcome", false);
        fatal.addProperty("conditionIndex", 1);
        fatal.addProperty("readyForReplay", false);
        fatal.addProperty("replayAlreadyValidated", true);
        fatal.addProperty("targetReplayValidated", true);
        fatal.addProperty("validatedSummaryId", "SUMMARY.F.FRESH");
        fatal.addProperty("replayValidationAuthority",
                "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                        + "TARGET_REPLAY");
        fatal.addProperty("formulaAuthority",
                "FRESH_INSTANCE_IMPORTED_UNFORCED_TARGET_PREFIX_PLUS_"
                        + "OBSERVED_TARGET");
        fatal.addProperty("targetPolicy",
                "KEEP_FRESH_OBSERVED_DESIRED_TARGET_CONDITION");
        JsonElement targetCondition = fatal.getAsJsonArray("constraints")
                .get(1).deepCopy();
        fatal.add("freshObservedTargetCondition",
                targetCondition.deepCopy());
        fatal.add("negatedTargetCondition", targetCondition.deepCopy());
        fatal.add("engineArrayInputBindings", new JsonArray());

        JsonObject admission = new JsonObject();
        admission.addProperty("required", true);
        admission.addProperty("valid", true);
        admission.addProperty("branchOverrideAccepted", false);
        admission.addProperty("authority",
                "SOLVER_MODEL_PLUS_UNFORCED_BRANCH_AND_EXCEPTION_OBSERVATION");
        JsonObject validated = new JsonObject();
        validated.addProperty("summaryId", "SUMMARY.F.FRESH");
        validated.addProperty("activationId", "ACT.F");
        validated.addProperty("regionId", "REGION.F");
        validated.addProperty("regionInstanceId", instance);
        validated.addProperty("targetReplayValidated", true);
        validated.addProperty("branchOverrideUsed", false);
        validated.add("executionAdmission", admission.deepCopy());
        fatal.add("validatedTargetSummary", validated);
        JsonObject rebase = new JsonObject();
        rebase.addProperty("activationId", "ACT.F");
        rebase.addProperty("regionInstanceId", instance);
        rebase.addProperty("downstreamInjectionUsed", false);
        rebase.addProperty("branchOverrideUsed", false);
        rebase.addProperty("authority",
                "FRESH_INSTANCE_UPSTREAM_SUPPORT_IMPORTED_UNFORCED_"
                        + "TARGET_REPLAY");
        fatal.add("targetRebaseProvenance", rebase);
        JsonObject rebuild = new JsonObject();
        rebuild.addProperty("freshSummaryId", "SUMMARY.F.FRESH");
        rebuild.addProperty("transitionExecutionId", "EXEC.FRESH");
        rebuild.addProperty("activationId", "ACT.F");
        rebuild.addProperty("regionInstanceId", instance);
        rebuild.addProperty("authority",
                "FRESH_SUMMARY_PATH_AND_CURRENT_RUNTIME_EDGE_LEDGER");
        fatal.add("freshQueryRebuildProvenance", rebuild);
        JsonObject context = fatal.getAsJsonObject("symbolicContext");
        context.addProperty("regionId", "REGION.F");
        context.addProperty("regionInstanceId", instance);
        context.addProperty("transitionExecutionId", "EXEC.FRESH");
        context.addProperty("selectionAuthority",
                "CURRENT_EDGE_LEDGER_EXACT_TARGET_ENDPOINT_INSTANCE");
        JsonObject binding = context.getAsJsonArray("versionedStateMerges")
                .get(0).getAsJsonObject().getAsJsonArray("selectedBindings")
                .get(0).getAsJsonObject();
        context.getAsJsonArray("versionedStateMerges").get(0)
                .getAsJsonObject().addProperty("toEndpoint",
                        "REGION.F::REGION.F.in.0");
        binding.addProperty("fromRegionInstance", "P.FRESH");
        binding.addProperty("toRegionInstance", instance);

        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.F.FRESH");
        summary.addProperty("activationId", "ACT.F");
        summary.addProperty("regionId", "REGION.F");
        summary.addProperty("regionInstanceId", instance);
        summary.addProperty("valid", true);
        summary.addProperty("targetReplayValidated", true);
        summary.addProperty("branchOverrideUsed", false);
        summary.add("captureGoal", RegionCaptureGoal.targetBranch().toJson());
        summary.add("executionAdmission", admission.deepCopy());
        summary.add("pathCondition", fatal.getAsJsonArray("constraints")
                .deepCopy());
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", "F#u2");
        mapping.addProperty("occurrence", 1);
        mapping.addProperty("conditionIndex", 1);
        mapping.addProperty("observedOutcome", false);
        mapping.addProperty("overrideApplied", false);
        mapping.add("condition", targetCondition.deepCopy());
        JsonArray mappings = new JsonArray();
        mappings.add(mapping);
        summary.add("branchMappings", mappings);
        summary.add("engineArrayInputBindings", new JsonArray());
        JsonObject provisional = new JsonObject();
        provisional.addProperty("siteId", "F#u2");
        provisional.addProperty("authority", "PROVISIONAL_TARGET_ORACLE");
        summary.add("directedTargetQuery", provisional);
        summary.add("freshObservedTargetQuery", fatal.deepCopy());

        Files.write(fixture.fatal,
                (fatal + "\n").getBytes(StandardCharsets.UTF_8));
        writeSummary(fixture, summary);
        return new FreshReplayPair(fatal, summary);
    }

    private static final class FreshReplayPair {
        private final JsonObject fatal;
        private final JsonObject summary;

        private FreshReplayPair(JsonObject fatal, JsonObject summary) {
            this.fatal = fatal;
            this.summary = summary;
        }
    }

    @Test
    public void composesVersionedJavaMapMutationChain() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            writeSummary(fixture, producerSummary(mutationChain(), true));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(0, result.manifest.getAsJsonArray(
                    "incompleteSummaryRegions").size());
            assertTrue(result.smtLib.contains("(map_put "));
            assertTrue(result.smtLib.contains("(map_remove "));
            assertTrue(result.smtLib.contains("(map_clear "));
            assertTrue(result.smtLib.contains("(map_put_all "));
            assertTrue(result.smtLib.contains(
                    "(map_remove port__local_heap__summary_SUMMARY_P__"));
            assertTrue(result.smtLib.contains(
                    "__REGION_P_out_heapMap0_state3 port__REGION_P_in_1)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesGuardedMultiPathRegionRelation() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject positive = producerSummary(singlePutEffect(), true);
            positive.add("captureGoal",
                    RegionCaptureGoal.outputClosure().toJson());
            JsonObject requested = new JsonObject();
            requested.addProperty("portId", "REGION.P.out.0");
            positive.add("requestedOutput", requested);
            positive.getAsJsonArray("pathCondition").add(
                    integerCondition(">", 0));
            JsonObject nonPositive = positive.deepCopy();
            nonPositive.addProperty("summaryId", "SUMMARY.P.SECOND");
            nonPositive.addProperty("activationId", "ACT.P.SECOND");
            nonPositive.add("pathCondition", new JsonArray());
            nonPositive.getAsJsonArray("pathCondition").add(
                    integerCondition("<=", 0));
            JsonObject closed = new JsonObject();
            closed.addProperty("complete", true);
            closed.addProperty("status",
                    "COMPLETE_BOUNDED_PATH_CLOSURE");
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(positive, nonPositive), closed);
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "guardedRegionRelationCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "guardedPathCaseCount").getAsInt());
            assertTrue(result.smtLib.contains(
                    "region_case_selector_coverage_REGION_P"));
            assertTrue(result.smtLib.contains(
                    "region_case_selector_exclusive_REGION_P_0_1"));
            assertTrue(result.smtLib.contains("(=>"));
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            String mergedSummaryId = merged.summaries.get(0).get(
                    "summaryId").getAsString();
            assertEquals(2, catalog.size());
            assertTrue(result.manifest.get(
                    "caseProjectionCatalogComplete").getAsBoolean());
            for (com.google.gson.JsonElement element : catalog) {
                JsonObject pathCase = element.getAsJsonObject();
                assertTrue(pathCase.get("complete").getAsBoolean());
                assertEquals("REGION.P",
                        pathCase.get("regionId").getAsString());
                assertFalse(pathCase.get("caseId").getAsString().isEmpty());
                assertFalse(pathCase.get("pathKey").getAsString().isEmpty());
                assertFalse(pathCase.get("symbolScope").getAsString().isEmpty());
                assertFalse(pathCase.get(
                        "sourceSummaryId").getAsString().isEmpty());
                assertEquals(mergedSummaryId, pathCase.get(
                        "compositionInputSummaryId").getAsString());
                String selector = pathCase.get(
                        "selectorSolverSymbol").getAsString();
                assertTrue(result.smtLib.contains(
                        "(declare-const " + selector + " Bool)"));
                assertTrue(result.smtLib.contains("(= " + selector + " "));
                JsonObject mapping = rawSymbolMapping(pathCase,
                        "M_I_field_REGION.P.in.2_example/Cache");
                assertEquals("sym__port__REGION_P_in_2__int",
                        mapping.get("solverTerm").getAsString());
                assertEquals("Int", mapping.get("solverSort").getAsString());
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void scopesRerunLocalsPlaceholdersAndArraysButSharesPorts()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String arrayCell = "<example.Keys: int[] values>";
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.4", arrayCell));
            JsonObject positive = producerSummary(singlePutEffect(), true);
            positive.add("captureGoal",
                    RegionCaptureGoal.outputClosure().toJson());
            JsonObject requested = new JsonObject();
            requested.addProperty("portId", "REGION.P.out.0");
            positive.add("requestedOutput", requested);
            positive.getAsJsonArray("pathCondition").add(
                    integerCondition(">", 0));
            positive.getAsJsonArray("pathCondition").add(
                    placeholderCondition(">", 1));
            positive.getAsJsonArray("pathCondition").add(
                    placeholderCondition(">", 1));
            positive.getAsJsonArray("pathCondition").add(
                    arrayLoad("AL_1", "EL_1"));
            positive.add("engineArrayInputBindings",
                    singleton(engineArrayInputBinding("ACT.P",
                            "REGION.P.in.4", arrayCell, "[I", "AL_1", 71,
                            constant("I", "Y_I_4"))));

            JsonObject nonPositive = positive.deepCopy();
            nonPositive.addProperty("summaryId", "SUMMARY.P.RERUN");
            nonPositive.addProperty("activationId", "ACT.P.RERUN");
            nonPositive.add("pathCondition", new JsonArray());
            nonPositive.getAsJsonArray("pathCondition").add(
                    integerCondition("<=", 0));
            nonPositive.getAsJsonArray("pathCondition").add(
                    placeholderCondition("<=", 1));
            nonPositive.getAsJsonArray("pathCondition").add(
                    arrayLoad("AL_1", "EL_1"));
            nonPositive.add("engineArrayInputBindings",
                    singleton(engineArrayInputBinding("ACT.P.RERUN",
                            "REGION.P.in.4", arrayCell, "[I", "AL_1", 91,
                            constant("I", "Y_I_4"))));

            JsonObject closed = closedPathManifest();
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(positive, nonPositive), closed);
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertEquals(2, countDeclarationLines(result.smtLib,
                    "producer_value"));
            assertEquals(2, countDeclarationLines(result.smtLib,
                    "placeholder__", "currentTimeMillis_1"));
            assertEquals(2, countDeclarationLines(result.smtLib,
                    "array__", "AL_1"));
            assertEquals(1, countDeclarationLines(result.smtLib,
                    "sym__port__REGION_P_in_2__int"));
            for (com.google.gson.JsonElement element
                    : result.manifest.getAsJsonArray(
                    "caseProjectionCatalog")) {
                JsonObject mapping = rawSymbolMapping(
                        element.getAsJsonObject(), "AL_1");
                assertEquals("REGION.P.in.4",
                        mapping.get("canonicalPort").getAsString());
                assertEquals("CANONICAL_ARRAY_INPUT_ELEMENTS",
                        mapping.get("termKind").getAsString());
            }
            for (String line : linesContaining(result.smtLib,
                    "engine_array_input_bridge_")) {
                assertFalse(line, line.contains("(=> "));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void bridgesEngineArrayLoadToCanonicalFiniteInputWithBounds()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String cell = "<example.Keys: int[] values>";
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.4", cell));
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonArray("pathCondition").add(
                    arrayLoad("VM_ARRAY_INPUT", "VM_ARRAY_VALUE"));
            summary.add("engineArrayInputBindings", singleton(
                    engineArrayInputBinding("ACT.P", "REGION.P.in.4",
                            cell, "[I", "VM_ARRAY_INPUT", 51,
                            constant("I", "Y_I_7"))));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "(finite_array_elements port__REGION_P_in_4)"));
            assertTrue(result.smtLib.contains(
                    "(= (finite_array_length port__REGION_P_in_4) 1)"));
            assertTrue(result.smtLib.contains(
                    "(< 0 (finite_array_length port__REGION_P_in_4))"));
            String bridge = lineContaining(result.smtLib,
                    "engine_array_input_bridge_");
            assertFalse(bridge, bridge.contains("(=> "));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void missingMalformedAndStoreEngineArrayBridgesFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Path missingRoot = folder.getRoot().toPath().resolve("missing");
            Files.createDirectories(missingRoot);
            Fixture missingFixture = fixture(missingRoot, true);
            JsonObject missing = producerSummary(singlePutEffect(), true);
            missing.getAsJsonArray("pathCondition").add(
                    arrayLoad("VM_ARRAY_MISSING", "VM_VALUE"));
            writeSummary(missingFixture, missing);
            ConcolicSmtComposer.Result missingResult =
                    ConcolicSmtComposer.compose(arguments(missingFixture));
            assertFalse(missingResult.manifest.get("complete")
                    .getAsBoolean());
            assertTrue(missingResult.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "EngineArrayInputBridgeMissing"));
            assertFalse(missingResult.smtLib.contains(
                    "array__summary_SUMMARY_P__VM_ARRAY_MISSING"));

            Path malformedRoot = folder.getRoot().toPath().resolve(
                    "malformed");
            Files.createDirectories(malformedRoot);
            Fixture malformedFixture = fixture(malformedRoot, true);
            String cell = "<example.Keys: int[] values>";
            addRegionPort(malformedFixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.4", cell));
            JsonObject malformed = producerSummary(singlePutEffect(), true);
            malformed.getAsJsonArray("pathCondition").add(
                    arrayLoad("VM_ARRAY_BAD", "VM_VALUE"));
            JsonObject badBridge = engineArrayInputBinding("ACT.P",
                    "REGION.P.in.4", cell, "[I", "VM_ARRAY_BAD", 61,
                    constant("I", "Y_I_3"));
            badBridge.addProperty("symbolizationPrefix",
                    "REGION.P.in.40");
            badBridge.addProperty("sameArrayObjectTokenVerified", false);
            malformed.add("engineArrayInputBindings",
                    singleton(badBridge));
            writeSummary(malformedFixture, malformed);
            ConcolicSmtComposer.Result malformedResult =
                    ConcolicSmtComposer.compose(arguments(malformedFixture));
            assertFalse(malformedResult.manifest.get("complete")
                    .getAsBoolean());
            assertTrue(malformedResult.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "ARRAY_SYMBOLIZATION_PREFIX_OR_MODE_INVALID"));

            Path storeRoot = folder.getRoot().toPath().resolve("store");
            Files.createDirectories(storeRoot);
            Fixture storeFixture = fixture(storeRoot, true);
            addRegionPort(storeFixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.4", cell));
            JsonObject store = producerSummary(singlePutEffect(), true);
            JsonObject event = arrayLoad("VM_ARRAY_STORE", "VM_VALUE");
            event.addProperty("_is_load", false);
            store.getAsJsonArray("pathCondition").add(event);
            store.add("engineArrayInputBindings", singleton(
                    engineArrayInputBinding("ACT.P", "REGION.P.in.4",
                            cell, "[I", "VM_ARRAY_STORE", 71,
                            constant("I", "Y_I_3"))));
            writeSummary(storeFixture, store);
            ConcolicSmtComposer.Result storeResult =
                    ConcolicSmtComposer.compose(arguments(storeFixture));
            assertFalse(storeResult.manifest.get("complete").getAsBoolean());
            assertTrue(storeResult.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "EngineArrayStoreUnsupported"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void fatalArrayBridgeUsesItsOwnScopeAndFixedRuntimeLength()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String cell = "<example.Request: int[] values>";
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8", cell));
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.getAsJsonArray("constraints").add(
                    arrayLoad("VM_FATAL_ARRAY", "VM_FATAL_VALUE"));
            fatal.add("engineArrayInputBindings", singleton(
                    engineArrayInputBinding("ACT.F", "REGION.F.in.8",
                            cell, "[I", "VM_FATAL_ARRAY", 81,
                            constant("I", "Y_I_5"))));
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains("array__fatal_ACT_F"));
            assertTrue(result.smtLib.contains(
                    "(= (finite_array_length port__REGION_F_in_8) 1)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void upstreamArrayLengthContradictsDifferentRuntimeInputLength()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String producerCell = "<example.Keys: int[] values>";
            String consumerCell = "<example.Request: int[] values>";
            installArrayProducerFlow(fixture, producerCell, consumerCell,
                    arrayValueExpression("[I", "I", true,
                            constant("I", "Y_I_7"),
                            constant("I", "Y_I_8")));
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.getAsJsonArray("constraints").add(
                    arrayLoad("VM_FATAL_LENGTH_ONE", "VM_FATAL_VALUE"));
            fatal.add("engineArrayInputBindings", singleton(
                    engineArrayInputBinding("ACT.F", "REGION.F.in.8",
                            consumerCell, "[I", "VM_FATAL_LENGTH_ONE", 82,
                            constant("I", "Y_I_5"))));
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "(= (finite_array_length port__REGION_F_in_8) 1)"));
            assertTrue(result.smtLib.contains(
                    "(= port__REGION_P_out_2 port__REGION_F_in_8)"));
            assertTrue(result.smtLib.contains("Y_I_2")
                    || result.smtLib.contains(" 2)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void fatalAndUpstreamJvmLocalsWithSameRawNameDoNotAlias()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    symbol("example/Value", "map_result"), "!=",
                    symbol("", "N")));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertEquals(2, countDeclarationLines(result.smtLib,
                    "map_result"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void derivedPortSubstringIsNotAcceptedAsCanonicalBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonArray("pathCondition").add(integerCondition(
                    "M_I_field_REGION.P.in.2.selectedField_example/Cache",
                    ">", 0));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertEquals(0, countDeclarationLines(result.smtLib,
                    "sym__port__REGION_P_in_2"));
            assertEquals(1, countDeclarationLines(result.smtLib,
                    "REGION_P_in_2_selectedField_example_Cache"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void nextCaseGuardCannotInheritPreviousCaseGuard() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject first = producerSummary(singlePutEffect(), true);
            first.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
            JsonObject requested = new JsonObject();
            requested.addProperty("portId", "REGION.P.out.0");
            first.add("requestedOutput", requested);
            first.getAsJsonArray("pathCondition").add(
                    integerCondition(">", 0));
            JsonObject second = first.deepCopy();
            second.addProperty("summaryId", "SUMMARY.P.SECOND.PORT");
            second.addProperty("activationId", "ACT.P.SECOND.PORT");
            second.add("pathCondition", new JsonArray());
            second.getAsJsonArray("pathCondition").add(integerCondition(
                    "M_I_field_REGION.F.in.3_example/Store", "<=", 0));
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(first, second),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));
            String binding = lineContaining(result.smtLib,
                    ":named bind_REGION_F_in_3");

            assertFalse(binding.isEmpty());
            assertFalse(binding.contains("(=>"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mapRemoveBindsRemovedExpiryToPreStateEntry() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject remove = mapEffect("MAP_REMOVE", "REGION.P.in.0",
                    "REGION.P.out.0", 0);
            remove.addProperty("requiresKeyPresent", true);
            remove.add("removedValueExpression", symbol("J", "expiry_value"));
            remove.addProperty("entryBindingAuthority",
                    "JAVA_MAP_ENTRY_FROM_BOUND_ENTRY_SET_NEXT");
            remove.addProperty("valueBindingAuthority",
                    "SAME_MAP_ENTRY_GET_VALUE_AT_NEXT");
            JsonArray effects = new JsonArray();
            effects.add(remove);
            JsonObject summary = producerSummary(effects, true);
            summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
            JsonObject requested = new JsonObject();
            requested.addProperty("portId", "REGION.P.out.0");
            summary.add("requestedOutput", requested);
            summary.getAsJsonArray("pathCondition").add(
                    integerCondition(">", 0));
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Collections.singletonList(summary),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));
            String present = lineContaining(result.smtLib,
                    ":named heap_remove_key_present_");
            String value = lineContaining(result.smtLib,
                    ":named heap_remove_value_binding_");

            assertTrue(present.contains("(=>"));
            assertTrue(present.contains(
                    "(map_has port__REGION_P_in_0 (VMapInteger 7))"));
            assertTrue(value.contains("(=>"));
            assertTrue(value.contains(
                    "(map_select port__REGION_P_in_0 (VMapInteger 7))"));
            assertTrue(value.contains("expiry_value"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergedRemoveAndNoRemoveCasesComposeHeapReadsAndIdentity()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonArray removeEffects = new JsonArray();
            removeEffects.add(mapEffect("MAP_REMOVE", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject remove = producerSummary(removeEffects, true);
            prepareOutputCase(remove, ">", "OBS.REMOVE", "entry_value_1");

            JsonArray identityEffects = new JsonArray();
            identityEffects.add(mapEffect("MAP_IDENTITY", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject noRemove = producerSummary(identityEffects, true);
            noRemove.addProperty("summaryId", "SUMMARY.P.NO_REMOVE");
            noRemove.addProperty("activationId", "ACT.P.NO_REMOVE");
            prepareOutputCase(noRemove, "<=", "OBS.NO_REMOVE",
                    "entry_value_1");

            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(remove, noRemove),
                    closedPathManifest());
            JsonArray mergedCases = merged.summaries.get(0).getAsJsonObject(
                    "regionRelation").getAsJsonArray("cases");
            assertEquals(1, mergedCases.get(0).getAsJsonObject()
                    .getAsJsonArray("heapObservations").size());
            assertEquals(1, mergedCases.get(1).getAsJsonObject()
                    .getAsJsonArray("heapObservations").size());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(2, result.manifest.get("heapObservationCount")
                    .getAsInt());
            assertEquals(2, result.manifest.get(
                    "heapObservationFieldBindingCount").getAsInt());
            assertEquals(2, countDeclarationLines(result.smtLib,
                    "entry_value_1"));
            assertEquals(1, countLines(result.smtLib,
                    "(declare-fun exact_field__"));
            for (String line : linesContaining(result.smtLib,
                    ":named heap_observation_")) {
                assertTrue(line, line.contains("(=>"));
            }
            assertEquals(8, linesContaining(result.smtLib,
                    ":named heap_observation_").size());
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            JsonObject removeProjection = projectionBySource(catalog,
                    "SUMMARY.P");
            JsonObject noRemoveProjection = projectionBySource(catalog,
                    "SUMMARY.P.NO_REMOVE");
            String removeSelector = removeProjection.get(
                    "selectorSolverSymbol").getAsString();
            String noRemoveSelector = noRemoveProjection.get(
                    "selectorSolverSymbol").getAsString();
            assertTrue(lineContaining(result.smtLib,
                    ":named heap_observation_key_present_OBS_REMOVE")
                    .contains("(=> " + removeSelector));
            assertTrue(lineContaining(result.smtLib,
                    ":named heap_observation_key_present_OBS_NO_REMOVE")
                    .contains("(=> " + noRemoveSelector));
            assertTrue(lineContaining(result.smtLib, "(map_remove ")
                    .contains("(=> " + removeSelector));
            assertTrue(lineContaining(result.smtLib,
                    ":named case_selector_definition_REGION_P_")
                    .contains("sym__port__REGION_P_in_2__int"));
            String identity = lineContaining(result.smtLib,
                    "(= port__REGION_P_out_0 port__REGION_P_in_0)");
            assertTrue(identity.contains("(=>"));
            assertTrue(identity.contains(noRemoveSelector));
            assertTrue(result.smtLib.contains(
                    "port__REGION_P_in_3"));
            assertTrue(result.smtLib.contains(
                    "heap_observation_key_present_OBS_REMOVE"));
            assertTrue(result.smtLib.contains("(VMapInteger 7)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergedDynamicCasesCatalogActualCaseScopedSolverTerms()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String dynamic =
                    "REGION.P.in.3.field.aaaaaaaaaaaa.occ.1";
            String rawField = "M_J_field_" + dynamic + "_expiry";

            JsonArray removeEffects = new JsonArray();
            removeEffects.add(mapEffect("MAP_REMOVE", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject remove = producerSummary(removeEffects, true);
            prepareDynamicOutputCase(remove, ">", "OBS.DYNAMIC.REMOVE",
                    "entry_value_dynamic", dynamic);

            JsonArray identityEffects = new JsonArray();
            identityEffects.add(mapEffect("MAP_IDENTITY", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject noRemove = producerSummary(identityEffects, true);
            noRemove.addProperty("summaryId", "SUMMARY.P.DYNAMIC.NO_REMOVE");
            noRemove.addProperty("activationId", "ACT.P.DYNAMIC.NO_REMOVE");
            prepareDynamicOutputCase(noRemove, "<=",
                    "OBS.DYNAMIC.NO_REMOVE", "entry_value_dynamic", dynamic);

            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(remove, noRemove),
                    closedPathManifest());
            assertEquals(2, merged.summaries.get(0).getAsJsonObject(
                    "regionRelation").get("caseCount").getAsInt());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString(),
                    result.manifest.get("structurallyComplete").getAsBoolean());
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            JsonObject removeProjection = projectionBySource(catalog,
                    "SUMMARY.P");
            JsonObject noRemoveProjection = projectionBySource(catalog,
                    "SUMMARY.P.DYNAMIC.NO_REMOVE");
            JsonObject removeMapping = rawSymbolMapping(removeProjection,
                    rawField);
            JsonObject noRemoveMapping = rawSymbolMapping(noRemoveProjection,
                    rawField);
            String removeTerm = removeMapping.get("solverTerm").getAsString();
            String noRemoveTerm = noRemoveMapping.get(
                    "solverTerm").getAsString();

            assertEquals("SCOPED_DYNAMIC_FIELD",
                    removeMapping.get("termKind").getAsString());
            assertEquals("Int", removeMapping.get("solverSort").getAsString());
            assertFalse(removeTerm.equals(noRemoveTerm));
            assertTrue(removeProjection.get(
                    "selectorGuardFormula").getAsString().contains(removeTerm));
            assertTrue(noRemoveProjection.get(
                    "selectorGuardFormula").getAsString().contains(noRemoveTerm));
            assertEquals(removeTerm, removeProjection.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject().get(
                    "solverTerm").getAsString());
            assertEquals(noRemoveTerm, noRemoveProjection.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject().get(
                    "solverTerm").getAsString());
            assertEquals("EMITTER_ACTUAL_DYNAMIC_FIELD_TERM",
                    removeProjection.getAsJsonArray("dynamicFieldBindings")
                            .get(0).getAsJsonObject().get(
                            "termBindingAuthority").getAsString());
            assertFalse(removeTerm.contains("port__REGION_P_in_3"));
            assertTrue(result.smtLib.contains("(= "
                    + removeProjection.get("selectorSolverSymbol").getAsString()
                    + " (> " + removeTerm + " 0))"));
            assertTrue(result.smtLib.contains("(= "
                    + noRemoveProjection.get(
                    "selectorSolverSymbol").getAsString()
                    + " (<= " + noRemoveTerm + " 0))"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergedContainerDynamicCaseUsesExactArraySelectorTerm()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String dynamic = "REGION.P.in.3.field.bbbbbbbbbbbb.occ.1";
            String raw = "M_I_field_" + dynamic + "_example/Key";
            JsonArray effects = new JsonArray();
            effects.add(mapEffect("MAP_IDENTITY", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject summary = producerSummary(effects, true);
            summary.add("captureGoal", RegionCaptureGoal.outputClosure()
                    .toJson());
            summary.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    symbol("I", raw), ">", constant("I", "Y_I_0")));
            JsonArray observations = new JsonArray();
            observations.add(heapObservation("OBS.CONTAINER", "value"));
            summary.add("heapObservations", observations);
            JsonArray bindings = new JsonArray();
            bindings.add(runtimeContainerFieldBinding(dynamic));
            summary.add("dynamicFieldBindings", bindings);

            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Collections.singletonList(summary),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));
            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            JsonObject projection = projectionBySource(result.manifest
                    .getAsJsonArray("caseProjectionCatalog"), "SUMMARY.P");
            JsonObject projected = projection.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            assertEquals("DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING",
                    projected.get("kind").getAsString());
            assertEquals(2, projected.getAsJsonObject("containerSelector")
                    .get("elementIndex").getAsInt());
            assertEquals("EMITTER_ACTUAL_DYNAMIC_FIELD_TERM",
                    projected.get("termBindingAuthority").getAsString());
            assertEquals(projected.get("solverTerm").getAsString(),
                    rawSymbolMapping(projection, raw).get(
                            "solverTerm").getAsString());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergedMapProjectionEmitsTypedFiniteValuesAndRejectsKeySet()
            throws Exception {
        for (String operation : new String[]{"MAP_VALUES_VIEW",
                "MAP_KEY_SET_VIEW"}) {
            TemporaryFolder folder = new TemporaryFolder();
            folder.create();
            try {
                Fixture fixture = fixture(folder.getRoot().toPath(), true);
                JsonObject summary = producerSummary(singlePutEffect(), true);
                summary.add("captureGoal",
                        RegionCaptureGoal.outputClosure().toJson());
                summary.add("requestedOutput",
                        requestedOutput("REGION.P.out.0"));
                summary.add("dynamicFieldBindings",
                        runtimeMapProjectionFieldBindings(operation));
                RegionSummaryMerger.Result merged =
                        RegionSummaryMerger.merge(
                                java.util.Collections.singletonList(summary),
                                closedPathManifest());
                writeSummary(fixture, merged.summaries.get(0));

                ConcolicSmtComposer.Result result =
                        ConcolicSmtComposer.compose(arguments(fixture));

                if ("MAP_KEY_SET_VIEW".equals(operation)) {
                    assertFalse(result.manifest.toString(),
                            result.manifest.get("complete").getAsBoolean());
                    assertTrue(result.manifest.toString(),
                            result.manifest.toString().contains(
                                    "MAP_PROJECTION"));
                    continue;
                }
                assertTrue(result.manifest.toString(),
                        result.manifest.get("structurallyComplete").getAsBoolean());
                assertTrue(result.smtLib.contains(
                        "(forall ((q Value)) (= (map_has "));
                assertTrue(result.smtLib.contains(
                        "finite_array_length port__REGION_P_out_2"));
                assertTrue(result.smtLib.contains(
                        "exact_field__"));
                assertTrue(result.smtLib.contains("(map_select "));
                assertTrue(result.smtLib.contains("(VMapInteger 11)"));
                JsonObject projected = projectionBySource(result.manifest
                        .getAsJsonArray("caseProjectionCatalog"),
                        "SUMMARY.P").getAsJsonArray(
                        "dynamicFieldBindings").get(0).getAsJsonObject();
                assertEquals("EXACT_RUNTIME_SYMBOLIZE_FIELD_WITHOUT_"
                                + "PC_EXPRESSION",
                        projected.get("termBindingAuthority").getAsString());
                assertEquals("MAP_OUTPUT_ARRAY_INDEX", projected
                        .getAsJsonObject("mapProjectionSelector")
                        .get("kind").getAsString());

                Path smt = folder.getRoot().toPath().resolve(
                        "map-projection.smt2");
                Path z3Output = folder.getRoot().toPath().resolve(
                        "z3.out");
                Files.write(smt, result.smtLib.getBytes(
                        StandardCharsets.UTF_8));
                Process process = new ProcessBuilder(
                        "/usr/local/bin/z3", smt.toString())
                        .redirectOutput(z3Output.toFile()).start();
                assertEquals(operation, 0, process.waitFor());
                assertTrue(operation, new String(Files.readAllBytes(z3Output),
                        StandardCharsets.UTF_8).startsWith("sat"));
            } finally {
                folder.delete();
            }
        }
    }

    @Test
    public void integerAndLongSamePayloadRemainDistinctMapKeysInRealZ3()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.add("captureGoal", RegionCaptureGoal.outputClosure()
                    .toJson());
            summary.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            JsonArray keys = new JsonArray();
            keys.add(constant("java/lang/Integer", "Y_I_1"));
            keys.add(constant("java/lang/Long", "Y_J_1"));
            summary.add("dynamicFieldBindings",
                    runtimeMapProjectionFieldBindingsWithKeys(keys));
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Collections.singletonList(summary),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains("(VMapInteger 1)"));
            assertTrue(result.smtLib.contains("(VMapLong 1)"));
            assertTrue(result.smtLib.contains(
                    "(distinct (VMapInteger 1) (VMapLong 1))"));
            Path smt = folder.getRoot().toPath().resolve(
                    "mixed-wrapper-map-keys.smt2");
            Path output = folder.getRoot().toPath().resolve("z3.out");
            Files.write(smt, result.smtLib.getBytes(StandardCharsets.UTF_8));
            Process process = new ProcessBuilder("/usr/local/bin/z3",
                    smt.toString()).redirectOutput(output.toFile()).start();
            assertEquals(0, process.waitFor());
            assertTrue(new String(Files.readAllBytes(output),
                    StandardCharsets.UTF_8).startsWith("sat"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void schema3MapProjectionRejectsFloatAndCustomReferenceKeys()
            throws Exception {
        for (JsonObject rejectedKey : new JsonObject[]{
                constant("java/lang/Double", "Y_D_1.0"),
                constant("example/CustomKey", "Y_L_custom")}) {
            TemporaryFolder folder = new TemporaryFolder();
            folder.create();
            try {
                Fixture fixture = fixture(folder.getRoot().toPath(), true);
                JsonObject summary = producerSummary(singlePutEffect(), true);
                summary.add("captureGoal", RegionCaptureGoal.outputClosure()
                        .toJson());
                summary.add("requestedOutput", requestedOutput(
                        "REGION.P.out.0"));
                JsonArray keys = new JsonArray();
                keys.add(rejectedKey.deepCopy());
                keys.add(constant("java/lang/Integer", "Y_I_2"));
                summary.add("dynamicFieldBindings",
                        runtimeMapProjectionFieldBindingsWithKeys(keys));
                RegionSummaryMerger.Result merged =
                        RegionSummaryMerger.merge(
                                java.util.Collections.singletonList(summary),
                                closedPathManifest());
                writeSummary(fixture, merged.summaries.get(0));

                ConcolicSmtComposer.Result result =
                        ConcolicSmtComposer.compose(arguments(fixture));
                assertFalse(rejectedKey + ":" + result.manifest,
                        result.manifest.get("complete").getAsBoolean());
                assertTrue(result.manifest.toString(),
                        result.manifest.toString().contains(
                                "MAP_PROJECTION"));
            } finally {
                folder.delete();
            }
        }
    }

    @Test
    public void allMapKeyEntrypointsFailClosedForUnsupportedJavaTypes()
            throws Exception {
        for (String source : new String[]{"MAP_GET_CUSTOM", "MAP_PUT_DOUBLE",
                "MAP_REMOVE_FLOAT", "HEAP_OBSERVATION_CUSTOM"}) {
            TemporaryFolder folder = new TemporaryFolder();
            folder.create();
            try {
                Fixture fixture = fixture(folder.getRoot().toPath(), true);
                JsonObject summary;
                if ("MAP_GET_CUSTOM".equals(source)) {
                    JsonObject fatal = JsonParser.parseString(new String(
                            Files.readAllBytes(fixture.fatal),
                            StandardCharsets.UTF_8).trim()).getAsJsonObject();
                    fatal.getAsJsonArray("constraints").get(0)
                            .getAsJsonObject().getAsJsonArray("_param_list")
                            .set(1, constant("example/CustomKey",
                                    "Y_L_custom"));
                    Files.write(fixture.fatal, (fatal + "\n").getBytes(
                            StandardCharsets.UTF_8));
                    summary = producerSummary(singlePutEffect(), true);
                } else if ("HEAP_OBSERVATION_CUSTOM".equals(source)) {
                    JsonArray effects = new JsonArray();
                    effects.add(mapEffect("MAP_IDENTITY", "REGION.P.in.0",
                            "REGION.P.out.0", 0));
                    summary = producerSummary(effects, true);
                    prepareOutputCase(summary, ">", "OBS.CUSTOM",
                            "entry_value_custom");
                    summary.getAsJsonArray("heapObservations").get(0)
                            .getAsJsonObject().add("keyExpression",
                            constant("example/CustomKey", "Y_L_custom"));
                } else {
                    String kind = "MAP_PUT_DOUBLE".equals(source)
                            ? "MAP_PUT" : "MAP_REMOVE";
                    JsonObject effect = mapEffect(kind, "REGION.P.in.0",
                            "REGION.P.out.0", 0);
                    effect.add("keyExpression",
                            "MAP_PUT_DOUBLE".equals(source)
                                    ? constant("java/lang/Double", "Y_D_1.0")
                                    : constant("java/lang/Float", "Y_F_1.0"));
                    JsonArray effects = new JsonArray();
                    effects.add(effect);
                    summary = producerSummary(effects, true);
                    summary.add("captureGoal",
                            RegionCaptureGoal.outputClosure().toJson());
                    summary.add("requestedOutput", requestedOutput(
                            "REGION.P.out.0"));
                }
                writeSummary(fixture, summary);

                ConcolicSmtComposer.Result result =
                        ConcolicSmtComposer.compose(arguments(fixture));
                assertFalse(source + ":" + result.manifest,
                        result.manifest.get("complete").getAsBoolean());
                assertTrue(source + ":" + result.manifest,
                        result.manifest.getAsJsonArray(
                                "unsupportedExpressions").toString()
                                .contains("MAP_KEY_TYPE_UNSUPPORTED"));
            } finally {
                folder.delete();
            }
        }
    }

    @Test
    public void typedJavaMapKeyConstructorsCoverAllSupportedKeyClasses()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject[] keys = new JsonObject[]{
                    constant("Z", "Y_Z_1"),
                    constant("B", "Y_B_-1"),
                    constant("C", "Y_C_65"),
                    constant("S", "Y_S_2"),
                    constant("I", "Y_I_3"),
                    constant("J", "Y_J_4"),
                    constant("Ljava/lang/String;", "Y_L_abc")};
            JsonArray effects = new JsonArray();
            for (int index = 0; index < keys.length; index++) {
                String input = index == 0 ? "REGION.P.in.0"
                        : "REGION.P.out.heapMap0.state" + index;
                String output = index == keys.length - 1
                        ? "REGION.P.out.0"
                        : "REGION.P.out.heapMap0.state" + (index + 1);
                JsonObject effect = mapEffect("MAP_PUT", input, output,
                        index);
                effect.add("keyExpression", keys[index]);
                effects.add(effect);
            }
            JsonObject summary = producerSummary(effects, true);
            summary.add("captureGoal", RegionCaptureGoal.outputClosure()
                    .toJson());
            summary.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));
            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            for (String constructor : new String[]{"VMapBoolean",
                    "VMapByte", "VMapChar", "VMapShort", "VMapInteger",
                    "VMapLong", "VMapString"}) {
                assertTrue(constructor + ":" + result.smtLib,
                        result.smtLib.contains("(" + constructor + " "));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void malformedTypedMapKeyLiteralsFailClosedInsteadOfBecomingUnsat()
            throws Exception {
        for (JsonObject malformed : new JsonObject[]{
                constant("B", "Y_B_128"),
                constant("I", "Y_J_1"),
                constant("Z", "Y_Z_2")}) {
            TemporaryFolder folder = new TemporaryFolder();
            folder.create();
            try {
                Fixture fixture = fixture(folder.getRoot().toPath(), true);
                JsonObject put = mapEffect("MAP_PUT", "REGION.P.in.0",
                        "REGION.P.out.0", 0);
                put.add("keyExpression", malformed.deepCopy());
                JsonArray effects = new JsonArray();
                effects.add(put);
                JsonObject summary = producerSummary(effects, true);
                summary.add("captureGoal", RegionCaptureGoal.outputClosure()
                        .toJson());
                summary.add("requestedOutput", requestedOutput(
                        "REGION.P.out.0"));
                writeSummary(fixture, summary);

                ConcolicSmtComposer.Result result =
                        ConcolicSmtComposer.compose(arguments(fixture));
                assertFalse(malformed + ":" + result.manifest,
                        result.manifest.get("complete").getAsBoolean());
                assertTrue(result.manifest.getAsJsonArray(
                        "unsupportedExpressions").toString(),
                        result.manifest.getAsJsonArray(
                                "unsupportedExpressions").toString()
                                .contains("MAP_KEY_LITERAL_INVALID"));
            } finally {
                folder.delete();
            }
        }
    }

    @Test
    public void containerSelectorAdmissionRejectsMissingAndDiscoveryForms() {
        JsonObject valid = runtimeContainerFieldBinding(
                "REGION.P.in.3.field.bbbbbbbbbbbb.occ.1");
        assertTrue(ConcolicSmtComposer.completeContainerSelectorForTests(
                valid));
        JsonObject missing = valid.deepCopy();
        missing.remove("containerSelector");
        assertFalse(ConcolicSmtComposer.completeContainerSelectorForTests(
                missing));
        JsonObject discovery = valid.deepCopy();
        discovery.getAsJsonObject("containerSelector").addProperty(
                "selectorAuthority", "DISCOVER_UNIQUE_IDENTITY_INDEX");
        assertFalse(ConcolicSmtComposer.completeContainerSelectorForTests(
                discovery));
    }

    @Test
    public void overlappingMergedCaseGuardsFailClosed() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonArray removeEffects = new JsonArray();
            removeEffects.add(mapEffect("MAP_REMOVE", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject remove = producerSummary(removeEffects, true);
            prepareOutputCase(remove, ">", "OBS.OVERLAP.REMOVE",
                    "entry_value_overlap");

            JsonArray identityEffects = new JsonArray();
            identityEffects.add(mapEffect("MAP_IDENTITY", "REGION.P.in.0",
                    "REGION.P.out.0", 0));
            JsonObject identity = producerSummary(identityEffects, true);
            identity.addProperty("summaryId", "SUMMARY.P.OVERLAP.IDENTITY");
            identity.addProperty("activationId", "ACT.P.OVERLAP.IDENTITY");
            prepareOutputCase(identity, ">", "OBS.OVERLAP.IDENTITY",
                    "entry_value_overlap");

            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(remove, identity),
                    closedPathManifest());
            assertEquals(2, merged.summaries.get(0).getAsJsonObject(
                    "regionRelation").get("caseCount").getAsInt());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertFalse(result.manifest.get(
                    "caseProjectionCatalogComplete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "OVERLAPPING_IDENTICAL_CASE_GUARD"));
            assertTrue(result.manifest.getAsJsonArray(
                    "caseProjectionCatalog").toString().contains(
                    "OVERLAPPING_IDENTICAL_CASE_GUARD"));
            assertTrue(result.smtLib.contains(
                    "region_case_selector_coverage_REGION_P"));
            assertTrue(result.smtLib.contains(
                    "region_case_selector_exclusive_REGION_P_0_1"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void malformedHeapReadObservationFailsClosed() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            JsonObject observation = heapObservation("OBS.BAD",
                    "entry_value_bad");
            observation.getAsJsonArray("entryFieldBindings").get(0)
                    .getAsJsonObject().remove("fieldSignature");
            JsonArray observations = new JsonArray();
            observations.add(observation);
            summary.add("heapObservations", observations);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.toString(), result.manifest.get(
                    "complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "IncompleteOrAmbiguousMapEntryRead"));
            assertFalse(result.smtLib.contains(
                    "heap_observation_key_present_OBS_BAD"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesTwoEntryFieldsAsIndependentDynamicInstances()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            JsonArray observations = new JsonArray();
            observations.add(dynamicHeapObservation("OBS.DYN.1",
                    "entry_value_1",
                    "REGION.P.in.3.field.aaaaaaaaaaaa.occ.1"));
            observations.add(dynamicHeapObservation("OBS.DYN.2",
                    "entry_value_2",
                    "REGION.P.in.3.field.aaaaaaaaaaaa.occ.2"));
            summary.add("heapObservations", observations);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString(),
                    result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(2, result.manifest.get("heapObservationCount")
                    .getAsInt());
            assertEquals(2, result.manifest.get(
                    "heapObservationFieldBindingCount").getAsInt());
            assertEquals(2, countDeclarationLines(result.smtLib,
                    "dynamic_field"));
            assertEquals(1, countLines(result.smtLib,
                    "(declare-fun exact_field__"));
            for (String line : linesContaining(result.smtLib,
                    ":named heap_observation_field_OBS_DYN")) {
                assertTrue(line, line.contains("dynamic_field"));
                assertFalse(line, line.contains(
                        "port__REGION_P_in_3"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void baseOnlyEntryFieldBindingIsAnExplicitRecursionGap()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            JsonObject observation = dynamicHeapObservation("OBS.BASE",
                    "entry_value_base",
                    "REGION.P.in.3.field.aaaaaaaaaaaa.occ.1");
            observation.getAsJsonArray("entryFieldBindings").get(0)
                    .getAsJsonObject().remove("fieldExpression");
            JsonArray observations = new JsonArray();
            observations.add(observation);
            summary.add("heapObservations", observations);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "BaseOnlyEntryFieldBindingRequiresDynamicExpression"));
            assertFalse(result.smtLib.contains(
                    "heap_observation_field_OBS_BASE"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void incompleteHeapModelIsAnExplicitCompositionGap()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            writeSummary(fixture, producerSummary(singlePutEffect(), false));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "incompleteSummaryRegions").toString()
                    .contains("REGION.P"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString()
                    .contains("IncompleteHeapEffectModel@REGION.P"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString()
                    .contains("IncompleteRelationalSummary@REGION.P"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void brokenHeapStateSsaCannotBeReportedComplete()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonArray effects = mutationChain();
            effects.get(1).getAsJsonObject().addProperty(
                    "inputPort", "REGION.P.in.0");
            writeSummary(fixture, producerSummary(effects, true));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "incompleteSummaryRegions").toString()
                    .contains("REGION.P"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString()
                    .contains("HeapPortChainGap@REGION.P"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesProvenFreshMapFromEmptyState() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonArray effects = new JsonArray();
            JsonObject put = mapEffect("MAP_PUT",
                    "REGION.P.state.heapMap0.empty", "REGION.P.out.0", 0);
            put.addProperty("inputBinding", "STATIC_FRESH_EMPTY_MAP");
            put.addProperty("outputBinding",
                    "STATIC_FRESH_ALLOCATION_TO_REQUESTED_OUTPUT");
            effects.add(put);
            JsonArray initializers = new JsonArray();
            initializers.add(emptyMapInitializer());
            writeSummary(fixture, producerSummary(effects, initializers,
                    true));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "(declare-const emptyMapState MapState)"));
            assertTrue(result.smtLib.contains(
                    "(map_members emptyMapState)"
                            + " ((as const (Array Value Bool)) false)"));
            assertTrue(result.smtLib.contains(
                    "__REGION_P_state_heapMap0_empty emptyMapState)"));
            assertTrue(result.smtLib.contains(
                    "(map_put port__local_heap__summary_SUMMARY_P__"));
            assertTrue(result.smtLib.contains("(VMapInteger 7)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void malformedFreshMapInitializerIsAnExplicitGap()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonArray effects = new JsonArray();
            JsonObject put = mapEffect("MAP_PUT",
                    "REGION.P.state.heapMap0.empty", "REGION.P.out.0", 0);
            put.addProperty("inputBinding", "STATIC_FRESH_EMPTY_MAP");
            effects.add(put);
            JsonArray initializers = new JsonArray();
            JsonObject malformed = emptyMapInitializer();
            malformed.addProperty("emptyStateAuthority", "UNPROVEN");
            initializers.add(malformed);
            writeSummary(fixture, producerSummary(effects, initializers,
                    true));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString()
                    .contains("MalformedMapEmptyInitializer@REGION.P"));
            assertFalse(result.smtLib.contains(
                    "(= port__REGION_P_state_heapMap0_empty emptyMapState)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mapTypeInferenceIgnoresMapTypesInContainingMethodParameters() {
        assertFalse(ConcolicSmtComposer.isMapCell(
                "<example.Server: void receive(int,java.util.Map)>::$i0"));
        assertFalse(ConcolicSmtComposer.isMapCell(
                "<example.Server: void receive(java.lang.String,java.util.Map)>"
                        + ".param0:java.lang.String"));
        assertTrue(ConcolicSmtComposer.isMapCell(
                "<example.Store: java.util.Map state>"));
        assertTrue(ConcolicSmtComposer.isMapCell(
                "<example.Store: java.util.Map getState()>.return"));
    }

    @Test
    public void arrayTypeInferenceCoversFieldParameterAndReturnOnly() {
        assertFalse(ConcolicSmtComposer.isArrayCell(
                "<example.Server: void receive(int,example.Key[])>::$i0"));
        assertTrue(ConcolicSmtComposer.isArrayCell(
                "<example.Keys: example.Key[] allKeys>"));
        assertTrue(ConcolicSmtComposer.isArrayCell(
                "<example.Server: void receive(example.Key[])>"
                        + ".param0:example.Key[]"));
        assertTrue(ConcolicSmtComposer.isArrayCell(
                "<example.Keys: example.Key[] getAllKeys()>.return"));
    }

    @Test
    public void finiteArrayOutputFlowsAcrossSelectedReadFromWithoutValueBoxing()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject snapshot = arrayValueExpression("[I", "I", true,
                    constant("I", "Y_I_7"),
                    symbol("I", "M_I_field_REGION.P.in.2_example/Cache"));
            installArrayProducerFlow(fixture,
                    "<example.Keys: int[] values>",
                    "<example.Request: int[] values>", snapshot);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "(declare-const port__REGION_P_out_2 FiniteArrayValue)"));
            assertTrue(result.smtLib.contains(
                    "(declare-const port__REGION_F_in_8 FiniteArrayValue)"));
            assertTrue(result.smtLib.contains("(mkFiniteArrayValue 2 "));
            assertTrue(result.smtLib.contains(
                    "(= port__REGION_P_out_2 port__REGION_F_in_8)"));
            assertFalse(result.smtLib.contains(
                    "(VRef port__REGION_P_out_2)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void incompleteFiniteArraySnapshotFailsClosedWithoutOutputBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject snapshot = arrayValueExpression("[I", "I", false,
                    constant("I", "Y_I_7"));
            installArrayProducerFlow(fixture,
                    "<example.Keys: int[] values>",
                    "<example.Request: int[] values>", snapshot);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "ELEMENTS_INCOMPLETE"));
            assertFalse(result.smtLib.contains(
                    ":named bind_REGION_P_out_2"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void arrayAndScalarOutputBindingsFailClosedInBothDirections()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject snapshot = arrayValueExpression("[I", "I", true,
                    constant("I", "Y_I_7"));
            installArrayProducerFlow(fixture,
                    "<example.Keys: int scalarValue>",
                    "<example.Request: int scalarValue>", snapshot);
            ConcolicSmtComposer.Result arrayToScalar =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertFalse(arrayToScalar.manifest.get("complete").getAsBoolean());
            assertTrue(arrayToScalar.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "ARRAY_TO_NON_ARRAY_PORT"));

            Path reverse = folder.getRoot().toPath().resolve("reverse");
            Files.createDirectories(reverse);
            fixture = fixture(reverse, true);
            installArrayProducerFlow(fixture,
                    "<example.Keys: int[] values>",
                    "<example.Request: int[] values>",
                    symbol("I", "not_an_array_snapshot"));
            ConcolicSmtComposer.Result scalarToArray =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertFalse(scalarToArray.manifest.get("complete").getAsBoolean());
            assertTrue(scalarToArray.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "ArrayValueExpressionRequired"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void incompatibleArrayTypesOnReadFromFailClosed() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            installArrayProducerFlow(fixture,
                    "<example.Keys: int[] values>",
                    "<example.Request: long[] values>",
                    arrayValueExpression("[I", "I", true,
                            constant("I", "Y_I_7")));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "ArrayPortJavaTypeMismatch"));
            assertFalse(result.smtLib.contains(
                    "(= port__REGION_P_out_2 port__REGION_F_in_8)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactContainerElementFieldAddsBoundsAndProjectionConstraint()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = containerFieldSummary(fixture,
                    "EXACT_ARRAY_INDEX", 1, 1, false);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "(< 1 (finite_array_length port__REGION_P_in_4))"));
            assertTrue(result.smtLib.contains(
                    "((_ is VRef) (finite_array_select "
                            + "port__REGION_P_in_4 1))"));
            assertTrue(result.smtLib.contains("exact_field__"));
            assertTrue(result.smtLib.contains(
                    "sym__port__REGION_P_in_3__int"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void discoveredContainerIndexUsesExactRuntimeSelectorAndFieldTerm()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = containerFieldSummary(fixture,
                    "DISCOVER_UNIQUE_IDENTITY_INDEX", -1, -1, true);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "(< 2 (finite_array_length port__REGION_P_in_4))"));
            assertTrue(result.smtLib.contains(
                    ":named container_dynamic_field_BIND_ARRAY_0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsLegacyAdapterSuppliedDomainSemantics() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            JsonObject arrayLoad = new JsonObject();
            arrayLoad.addProperty("_type", "_array_expr");
            arrayLoad.addProperty("_is_load", true);
            arrayLoad.addProperty("_arr_str", "fixture_values");
            arrayLoad.add("_index_exp", constant("I", "Y_I_0"));
            arrayLoad.add("_value_exp", symbol("I", "array_value"));
            summary.getAsJsonArray("pathCondition").add(arrayLoad);
            summary.addProperty("summaryMode", "RELATIONAL_PROTOCOL");
            summary.add("protocolModel", protocolModel());
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "LEGACY_DOMAIN_SEMANTIC_ADAPTER_REJECTED"));
            assertFalse(result.smtLib.contains(
                    "codec_encode__FIXTURE_INTEGER_CODEC"));
            assertFalse(result.smtLib.contains(
                    "temporal_FIXTURE_LIFECYCLE_cached_membership_guard"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "EngineArrayInputBridgeMissing"));
            assertFalse(result.smtLib.contains(
                    "__fixture_values 0)"));
            assertFalse(result.smtLib.contains("(forall ((s MapState)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mapEntryAndArrayElementShareCanonicalExactFieldAccessor()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = containerFieldSummary(fixture,
                    "EXACT_ARRAY_INDEX", 0, 1, false);
            String dynamic =
                    "REGION.P.in.3.field.sharedexpiry.occ.1";
            JsonObject observation = dynamicHeapObservation(
                    "OBS.SHARED.FIELD", "shared_element_ref", dynamic);
            observation.add("valueExpression", symbol("Lexample/Key;",
                    "shared_element_ref"));
            JsonObject observedField = observation.getAsJsonArray(
                    "entryFieldBindings").get(0).getAsJsonObject();
            observedField.addProperty("fieldSignature",
                    "<example.Key: long expiry>");
            summary.add("heapObservations", singleton(observation));
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.in.4", arrayValueExpression(
                            "[Lexample/Key;", "Lexample/Key;", true,
                            symbol("Lexample/Key;",
                                    "shared_element_ref")));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertEquals(1, countLines(result.smtLib,
                    "(declare-fun exact_field__"));
            assertFalse(result.smtLib.contains("(declare-fun heap_field__"));
            assertFalse(result.smtLib.contains(
                    "(declare-fun container_field__"));
            String accessor = declaredFunctionContaining(result.smtLib,
                    "exact_field__");
            assertFalse(accessor.isEmpty());
            assertTrue(lineContaining(result.smtLib,
                    ":named heap_observation_field_OBS_SHARED_FIELD_0")
                    .contains(accessor));
            assertTrue(lineContaining(result.smtLib,
                    ":named container_element_field_BIND_ARRAY_0")
                    .contains(accessor));
            assertTrue(result.smtLib.contains("shared_element_ref"));
            assertTrue(result.smtLib.contains(
                    "finite_array_select port__REGION_P_in_4 0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void canonicalExactFieldAccessorRejectsDeclaredSortConflict()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = containerFieldSummary(fixture,
                    "EXACT_ARRAY_INDEX", 0, 1, false);
            String dynamic = "REGION.P.in.3.field.badexpiry.occ.1";
            JsonObject observation = dynamicHeapObservation(
                    "OBS.BAD.SORT", "bad_element_ref", dynamic);
            JsonObject binding = observation.getAsJsonArray(
                    "entryFieldBindings").get(0).getAsJsonObject();
            binding.addProperty("fieldSignature",
                    "<example.Key: long expiry>");
            binding.addProperty("fieldJavaType", "int");
            binding.add("fieldExpression", symbol("I",
                    "M_I_field_" + dynamic + "_expiry"));
            summary.add("heapObservations", singleton(observation));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "IncompleteOrAmbiguousMapEntryRead"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesAlternativeWritersAsExactlyOneGuardedPhi()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject second = new JsonObject();
            second.addProperty("regionId", "REGION.Q");
            JsonObject input = new JsonObject();
            input.addProperty("portId", "REGION.Q.in.0");
            input.addProperty("cell",
                    "<example.Store: java.util.Map state>");
            JsonArray inputs = new JsonArray();
            inputs.add(input);
            second.add("symbolicInputs", inputs);
            JsonObject output = new JsonObject();
            output.addProperty("portId", "REGION.Q.out.0");
            output.addProperty("cell",
                    "<example.Store: java.util.Map state>");
            JsonArray outputs = new JsonArray();
            outputs.add(output);
            second.add("outputs", outputs);
            String secondRegion = second.toString() + "\n";
            Files.write(fixture.regions,
                    secondRegion.getBytes(StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.APPEND);

            JsonObject leftSummary = producerSummary(singlePutEffect(), true);
            JsonObject rightSummary = JsonParser.parseString(
                    leftSummary.toString().replace("REGION.P", "REGION.Q")
                            .replace("SUMMARY.P", "SUMMARY.Q")
                            .replace("ACT.P", "ACT.Q"))
                    .getAsJsonObject();
            Files.write(fixture.summaries,
                    (leftSummary.toString() + "\n" + rightSummary.toString()
                            + "\n").getBytes(StandardCharsets.UTF_8));

            JsonObject context = new JsonObject();
            context.addProperty("regionInstanceId",
                    "REGION.F@fixture#call2");
            context.add("equalityClasses", new JsonArray());
            context.add("equalityRelations", new JsonArray());
            context.add("versionedStateMerges", new JsonArray());
            JsonObject group = new JsonObject();
            group.addProperty("groupId", "NEUTRAL.WRITERS");
            group.addProperty("downstreamEndpoint", "REGION.F.in.0");
            group.addProperty("selectionSemantics",
                    "EXACTLY_ONE_GUARDED");
            JsonArray alternatives = new JsonArray();
            alternatives.add(guardedWriter("writer_guard__left",
                    "REGION.P.out.0", 10, 30));
            alternatives.add(guardedWriter("writer_guard__right",
                    "REGION.Q.out.0", 20, 30));
            group.add("alternatives", alternatives);
            JsonArray groups = new JsonArray();
            groups.add(group);
            context.add("alternativeWriterGroups", groups);

            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.add("symbolicContext", context.deepCopy());
            Files.write(fixture.fatal,
                    (fatal.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            Files.write(fixture.merge,
                    context.toString().getBytes(StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "alternativeWriterGroupCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "guardedAlternativeConstraintCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "readFromConstraintCount").getAsInt());
            assertTrue(result.smtLib.contains(
                    "(=> writer_guard__left (= port__REGION_P_out_0 "
                            + "port__REGION_F_in_0))"));
            assertTrue(result.smtLib.contains(
                    "(=> writer_guard__right (= port__REGION_Q_out_0 "
                            + "port__REGION_F_in_0))"));
            assertTrue(result.smtLib.contains(
                    "(= (+ (ite writer_guard__left 1 0)"
                            + " (ite writer_guard__right 1 0)) 1)"));
            assertFalse(result.smtLib.contains(
                    "(assert (! (= port__REGION_P_out_0 "
                            + "port__REGION_F_in_0)"));

            ConcolicSmtComposer.Arguments boundedArguments =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--merge-plan", fixture.merge.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P"
                    });
            ConcolicSmtComposer.Result bounded =
                    ConcolicSmtComposer.compose(boundedArguments);

            assertTrue(bounded.manifest.toString(), bounded.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertTrue(bounded.manifest.get("boundedComposition")
                    .getAsBoolean());
            assertEquals("EXPLICIT_BOUNDED_UPSTREAM_REGIONS",
                    bounded.manifest.get("compositionScope").getAsString());
            assertEquals(1, bounded.manifest.getAsJsonArray(
                    "boundedUpstreamRegions").size());
            assertEquals(1, bounded.manifest.get(
                    "excludedAlternativeWriterCount").getAsInt());
            assertEquals(1, bounded.manifest.get(
                    "includedBoundedRelationCount").getAsInt());
            assertEquals(0, bounded.manifest.get(
                    "alternativeWriterGroupCount").getAsInt());
            assertTrue(bounded.smtLib.contains(
                    "(= port__REGION_P_out_0 port__REGION_F_in_0)"));
            assertFalse(bounded.smtLib.contains("writer_guard__right"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void acceptsRepeatedSummaryArgumentsAndEdgeBindingEvidence()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            JsonObject binding = new JsonObject();
            binding.addProperty("toRegion", "REGION.F");
            binding.addProperty("fromRegionInstance",
                    "REGION.P@fixture#call1");
            binding.addProperty("toRegionInstance",
                    "REGION.F@fixture#call2");
            binding.addProperty("fromOutputPort", "REGION.P.out.0");
            binding.addProperty("toInputPort", "REGION.F.in.0");
            binding.addProperty("orderConfirmed", true);
            binding.addProperty("objectIdentityConfirmed", true);
            binding.addProperty("writerEventSeq", 30);
            binding.addProperty("readerEventSeq", 40);
            binding.addProperty("receiverObjectId", 17);
            binding.addProperty("selectionAuthority",
                    "RUNTIME_CONFIRMED_READ_FROM");
            JsonArray bindings = new JsonArray();
            bindings.add(binding);
            summary.add("edgeBindings", bindings);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Arguments arguments =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--merge-plan", fixture.merge.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments);

            assertTrue(result.manifest.get("structurallyComplete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "edgeBindingConstraintCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "readFromConstraintCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "orderConstraintCount").getAsInt());
            assertEquals(1, result.manifest.get(
                    "objectIdentityConstraintCount").getAsInt());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void recursivelyComposesExactMultiHopSummaryBinding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String upstreamRegion = "{\"regionId\":\"REGION.U\","
                    + "\"symbolicInputs\":[{\"portId\":\"REGION.U.in.0\","
                    + "\"cell\":\"<example.Upstream: java.util.Map state>\"}],"
                    + "\"outputs\":[{\"portId\":\"REGION.U.out.0\","
                    + "\"cell\":\"<example.Upstream: java.util.Map state>\"}]}\n";
            Files.write(fixture.regions, upstreamRegion.getBytes(
                    StandardCharsets.UTF_8),
                    java.nio.file.StandardOpenOption.APPEND);

            JsonObject intermediate = producerSummary(singlePutEffect(), true);
            intermediate.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            intermediate.add("requestedOutputSlice", requestedSlice(
                    "REGION.P.in.0"));

            JsonObject upstream = JsonParser.parseString(
                    producerSummary(singlePutEffect(), true).toString()
                            .replace("REGION.P", "REGION.U")
                            .replace("SUMMARY.P", "SUMMARY.U")
                            .replace("ACT.P", "ACT.U")
                            .replace("fixture#call1", "fixture#call0"))
                    .getAsJsonObject();
            upstream.add("requestedOutput", requestedOutput(
                    "REGION.U.out.0"));
            JsonArray bindings = new JsonArray();
            bindings.add(runtimeEdgeBinding("REGION.U",
                    "REGION.U@fixture#call0", "REGION.U.out.0",
                    "REGION.P", "REGION.P@fixture#call1",
                    "REGION.P.in.0", 5, 8, 91));
            upstream.add("edgeBindings", bindings);
            Files.write(fixture.summaries,
                    (intermediate + "\n" + upstream + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicSmtComposer.Arguments bounded =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--merge-plan", fixture.merge.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertEquals(2, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertEquals(1, result.manifest.get(
                    "resolvedRecursiveEdgeCount").getAsInt());
            JsonArray resolvedEdges = result.manifest.getAsJsonArray(
                    "resolvedEdgeBindings");
            assertEquals(1, resolvedEdges.size());
            JsonObject recursive = resolvedEdges.get(0).getAsJsonObject();
            assertEquals("REGION.U.out.0", recursive.get(
                    "sourceOutput").getAsString());
            assertEquals("REGION.P.in.0", recursive.get(
                    "targetInput").getAsString());
            assertTrue(recursive.get("recursive").getAsBoolean());
            assertEquals("RUNTIME_CONFIRMED_READ_FROM", recursive.get(
                    "selectionAuthority").getAsString());
            assertEquals(1, result.manifest.get(
                    "edgeBindingConstraintCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "readFromConstraintCount").getAsInt());
            assertEquals(0, result.manifest.getAsJsonArray(
                    "unreachableBoundedUpstreamRegions").size());
            assertTrue(result.smtLib.contains(
                    "port__REGION_U_out_0 port__REGION_P_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_P_out_0 port__REGION_F_in_0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void oneExactRegionInstanceSummarySuppliesSixDemandedOutputsOnce()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            addRegionPort(fixture, "REGION.P", "outputs",
                    port("REGION.P.out.2", "<example.P: int two>"));
            addRegionPort(fixture, "REGION.P", "outputs",
                    port("REGION.P.out.3", "<example.P: int three>"));
            addRegionPort(fixture, "REGION.P", "outputs",
                    port("REGION.P.out.4", "<example.P: int four>"));
            addRegionPort(fixture, "REGION.P", "outputs",
                    port("REGION.P.out.5", "<example.P: int five>"));
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8", "<example.F: java.lang.String eight>"));
            for (int index = 9; index <= 12; index++) {
                addRegionPort(fixture, "REGION.F", "symbolicInputs",
                        port("REGION.F.in." + index,
                                "<example.F: int value" + index + ">"));
            }

            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            JsonObject outputs = summary.getAsJsonObject(
                    "outputExpressions");
            outputs.add("REGION.P.out.1", symbol("java/lang/String",
                    "six_output_string"));
            for (int index = 2; index < 6; index++) {
                outputs.add("REGION.P.out." + index,
                        symbol("I", "six_output_int_" + index));
            }
            int[] fatalInputs = new int[]{0, 8, 9, 10, 11, 12};
            JsonArray bindings = new JsonArray();
            for (int index = 0; index < 6; index++) {
                bindings.add(runtimeEdgeBinding("REGION.P",
                        "REGION.P@fixture#call1", "REGION.P.out." + index,
                        "REGION.F", "REGION.F@fixture#call2",
                        "REGION.F.in." + fatalInputs[index],
                        10 + index, 30 + index, 100 + index));
            }
            summary.add("edgeBindings", bindings);
            writeSummary(fixture, summary);
            installFatalRelations(fixture, bindings);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertEquals(6, result.manifest.get(
                    "resolvedDemandedOutputCount").getAsInt());
            assertEquals(1, result.manifest.getAsJsonArray(
                    "includedSummaries").size());
            assertEquals(6, result.manifest.getAsJsonArray(
                    "resolvedProducerKeys").size());
            assertEquals(6, result.manifest.get(
                    "edgeBindingConstraintCount").getAsInt());
            for (int index = 0; index < 6; index++) {
                assertTrue(result.smtLib.contains(
                        "port__REGION_P_out_" + index));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void differentInstancesOfOneRegionAreNeverMerged()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject first = producerSummary(singlePutEffect(), true);
            first.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            JsonObject firstBinding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 10, 30, 101);
            JsonArray firstBindings = new JsonArray();
            firstBindings.add(firstBinding);
            first.add("edgeBindings", firstBindings);

            JsonObject second = producerSummary(new JsonArray(), true);
            second.addProperty("summaryId", "SUMMARY.P.OTHER.INSTANCE");
            second.addProperty("activationId", "ACT.P.OTHER.INSTANCE");
            second.addProperty("regionInstanceId",
                    "REGION.P@fixture#call9");
            second.add("requestedOutput", requestedOutput(
                    "REGION.P.out.1"));
            second.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.1", symbol("java/lang/String",
                            "other_instance_output"));
            JsonObject secondBinding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call9", "REGION.P.out.1",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.2", 11, 31, 102);
            JsonArray secondBindings = new JsonArray();
            secondBindings.add(secondBinding);
            second.add("edgeBindings", secondBindings);
            Files.write(fixture.summaries,
                    (first + "\n" + second + "\n").getBytes(
                            StandardCharsets.UTF_8));
            JsonArray fatalBindings = new JsonArray();
            fatalBindings.add(firstBinding);
            fatalBindings.add(secondBinding);
            installFatalRelations(fixture, fatalBindings);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertEquals(1, result.manifest.get(
                    "resolvedDemandedOutputCount").getAsInt());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "ConflictingProducerRegionInstance:REGION.P"));
            assertEquals(1, result.manifest.getAsJsonArray(
                    "includedSummaries").size());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void missingOneDemandedOutputPortFailsClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            JsonObject mapBinding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 10, 30, 101);
            JsonObject absentBinding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.1",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.2", 11, 31, 102);
            JsonArray bindings = new JsonArray();
            bindings.add(mapBinding);
            bindings.add(absentBinding);
            summary.add("edgeBindings", bindings);
            writeSummary(fixture, summary);
            installFatalRelations(fixture, bindings);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertEquals(1, result.manifest.get(
                    "resolvedDemandedOutputCount").getAsInt());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "MissingExactProducerSummary:REGION.P"
                            + "[instance=REGION.P@fixture#call1,"
                            + "output=REGION.P.out.1]"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void twoTrustedRecursiveChainsConvergeAtFatalInstance()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            appendRegion(fixture, region("REGION.U1", "java.util.Map",
                    "upstreamMap"));
            appendRegion(fixture, region("REGION.Q", "int",
                    "intermediateInt"));
            appendRegion(fixture, region("REGION.U2", "int",
                    "upstreamInt"));

            JsonObject p = producerSummary(singlePutEffect(), true);
            p.add("requestedOutput", requestedOutput("REGION.P.out.0"));
            p.add("requestedOutputSlice", requestedSlice("REGION.P.in.0"));
            JsonObject pToFatal = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 20, 40, 201);
            JsonArray pBindings = new JsonArray();
            pBindings.add(pToFatal);
            p.add("edgeBindings", pBindings);

            JsonObject q = scalarSummary("REGION.Q", "SUMMARY.Q",
                    "ACT.Q", "REGION.Q@fixture#call3",
                    "q_output");
            q.add("requestedOutputSlice", requestedSlice("REGION.Q.in.0"));
            JsonObject qToFatal = runtimeEdgeBinding("REGION.Q",
                    "REGION.Q@fixture#call3", "REGION.Q.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.1", 21, 41, 202);
            JsonArray qBindings = new JsonArray();
            qBindings.add(qToFatal);
            q.add("edgeBindings", qBindings);

            JsonObject u1 = JsonParser.parseString(
                    producerSummary(singlePutEffect(), true).toString()
                            .replace("REGION.P", "REGION.U1")
                            .replace("SUMMARY.P", "SUMMARY.U1")
                            .replace("ACT.P", "ACT.U1")
                            .replace("fixture#call1", "fixture#call0"))
                    .getAsJsonObject();
            u1.add("requestedOutput", requestedOutput("REGION.U1.out.0"));
            JsonObject u1ToP = runtimeEdgeBinding("REGION.U1",
                    "REGION.U1@fixture#call0", "REGION.U1.out.0",
                    "REGION.P", "REGION.P@fixture#call1",
                    "REGION.P.in.0", 5, 15, 301);
            JsonArray u1Bindings = new JsonArray();
            u1Bindings.add(u1ToP);
            u1.add("edgeBindings", u1Bindings);

            JsonObject u2 = scalarSummary("REGION.U2", "SUMMARY.U2",
                    "ACT.U2", "REGION.U2@fixture#call4",
                    "u2_output");
            JsonObject u2ToQ = runtimeEdgeBinding("REGION.U2",
                    "REGION.U2@fixture#call4", "REGION.U2.out.0",
                    "REGION.Q", "REGION.Q@fixture#call3",
                    "REGION.Q.in.0", 6, 16, 302);
            JsonArray u2Bindings = new JsonArray();
            u2Bindings.add(u2ToQ);
            u2.add("edgeBindings", u2Bindings);

            Files.write(fixture.summaries,
                    (p + "\n" + q + "\n" + u1 + "\n" + u2 + "\n")
                            .getBytes(StandardCharsets.UTF_8));
            JsonArray fatalBindings = new JsonArray();
            fatalBindings.add(pToFatal);
            fatalBindings.add(qToFatal);
            installFatalRelations(fixture, fatalBindings);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), result.manifest.get(
                    "structurallyComplete").getAsBoolean());
            assertEquals(4, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertEquals(2, result.manifest.get(
                    "resolvedRecursiveEdgeCount").getAsInt());
            assertEquals(4, result.manifest.get(
                    "resolvedEdgeBindingCount").getAsInt());
            JsonArray resolvedEdges = result.manifest.getAsJsonArray(
                    "resolvedEdgeBindings");
            assertEquals(4, resolvedEdges.size());
            assertTrue(resolvedEdges.toString().contains(
                    "\"sourceOutput\":\"REGION.P.out.0\""));
            assertTrue(resolvedEdges.toString().contains(
                    "\"targetInput\":\"REGION.F.in.0\""));
            assertTrue(resolvedEdges.toString().contains(
                    "\"sourceOutput\":\"REGION.U2.out.0\""));
            assertTrue(resolvedEdges.toString().contains(
                    "\"targetInput\":\"REGION.Q.in.0\""));
            // These chains feed different fatal inputs (the map-valued state
            // and the scalar lookup key).  They are simultaneous dependencies
            // of one query, not competing writers for one input port.
            assertEquals(0, result.manifest.get(
                    "alternativeWriterGroupCount").getAsInt());
            assertEquals(0, result.manifest.get(
                    "guardedAlternativeConstraintCount").getAsInt());
            assertTrue(result.smtLib.contains(
                    "port__REGION_U1_out_0 port__REGION_P_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_P_out_0 port__REGION_F_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_U2_out_0 port__REGION_Q_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_Q_out_0 port__REGION_F_in_1"));
            assertFalse(result.smtLib.contains("writer_guard__"));
            assertFalse(result.smtLib.contains("writer_choice_"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void recursiveMappingOnlyBindingIsNeverAdmitted()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            appendRegion(fixture, region("REGION.U", "java.util.Map",
                    "upstreamMap"));
            JsonObject p = producerSummary(singlePutEffect(), true);
            p.add("requestedOutput", requestedOutput("REGION.P.out.0"));
            p.add("requestedOutputSlice", requestedSlice("REGION.P.in.0"));
            JsonObject pToFatal = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 20, 40, 201);
            JsonArray pBindings = new JsonArray();
            pBindings.add(pToFatal);
            p.add("edgeBindings", pBindings);

            JsonObject upstream = JsonParser.parseString(
                    producerSummary(singlePutEffect(), true).toString()
                            .replace("REGION.P", "REGION.U")
                            .replace("SUMMARY.P", "SUMMARY.U")
                            .replace("ACT.P", "ACT.U")
                            .replace("fixture#call1", "fixture#call0"))
                    .getAsJsonObject();
            upstream.add("requestedOutput", requestedOutput(
                    "REGION.U.out.0"));
            JsonObject mappingOnly = runtimeEdgeBinding("REGION.U",
                    "REGION.U@fixture#call0", "REGION.U.out.0",
                    "REGION.P", "REGION.P@fixture#call1",
                    "REGION.P.in.0", 5, 15, 301);
            mappingOnly.addProperty("selectionAuthority",
                    "STATIC_PORT_MAPPING_ONLY");
            JsonArray upstreamBindings = new JsonArray();
            upstreamBindings.add(mappingOnly);
            upstream.add("edgeBindings", upstreamBindings);
            Files.write(fixture.summaries,
                    (p + "\n" + upstream + "\n").getBytes(
                            StandardCharsets.UTF_8));
            JsonArray fatalBindings = new JsonArray();
            fatalBindings.add(pToFatal);
            installFatalRelations(fixture, fatalBindings);

            ConcolicSmtComposer.Arguments bounded =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--merge-plan", fixture.merge.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertEquals(1, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertEquals(0, result.manifest.get(
                    "resolvedRecursiveEdgeCount").getAsInt());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "UnreachableBoundedRegion:REGION.U"));
            assertFalse(result.smtLib.contains(
                    "port__REGION_U_out_0 port__REGION_P_in_0"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsAmbiguousExactProducerSummary() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject first = producerSummary(singlePutEffect(), true);
            first.add("requestedOutput", requestedOutput("REGION.P.out.0"));
            JsonObject second = first.deepCopy();
            second.addProperty("summaryId", "SUMMARY.P.AMBIGUOUS");
            Files.write(fixture.summaries,
                    (first + "\n" + second + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertEquals(0, result.manifest.get(
                    "resolvedProducerCount").getAsInt());
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "AmbiguousExactProducerSummary:REGION.P"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsUnreachableRequestedBoundedRegion()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            ConcolicSmtComposer.Arguments bounded =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--merge-plan", fixture.merge.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertFalse(result.manifest.get("complete").getAsBoolean());
            assertTrue(result.manifest.getAsJsonArray(
                    "reachedBoundedUpstreamRegions").toString().contains(
                    "REGION.P"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unreachableBoundedUpstreamRegions").toString().contains(
                    "REGION.U"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "UnreachableBoundedRegion:REGION.U"));
        } finally {
            folder.delete();
        }
    }

    private static JsonObject protocolModel() {
        JsonObject model = new JsonObject();
        model.addProperty("complete", true);
        JsonArray relations = new JsonArray();

        JsonObject codec = protocolRelation("FIXTURE.CODEC",
                "LOSSLESS_CODEC");
        codec.addProperty("codecId", "FIXTURE_INTEGER_CODEC");
        codec.addProperty("lossless", true);
        codec.addProperty("transportEqualityConfirmed", true);
        codec.add("source", protocolPort("REGION.P.in.2", "INT"));
        codec.add("encoded", protocolPort("REGION.P.out.1", "VALUE"));
        codec.add("transport", protocolPort("REGION.F.in.2", "VALUE"));
        JsonObject decoded = new JsonObject();
        decoded.addProperty("kind", "EXPRESSION");
        decoded.addProperty("valueType", "INT");
        decoded.add("expression", symbol("java/lang/Integer",
                "boxed_lookup_key"));
        codec.add("decoded", decoded);
        relations.add(codec);

        JsonObject constant = protocolRelation("FIXTURE.CONSTANT",
                "CONSTANT_BINDING");
        constant.add("target", protocolPort("REGION.F.in.7", "INT"));
        JsonObject value = new JsonObject();
        value.addProperty("kind", "CONSTANT");
        value.addProperty("valueType", "INT");
        value.addProperty("value", 23);
        constant.add("value", value);
        relations.add(constant);

        JsonObject lifecycle = protocolRelation("FIXTURE.LIFECYCLE",
                "EXPIRING_CACHE_MEMBERSHIP");
        lifecycle.addProperty("exactExpiryRemoval", true);
        lifecycle.addProperty("currentValuePresent", true);
        lifecycle.addProperty("retainsCachedValue", true);
        lifecycle.addProperty("uniqueSuccessorValues", true);
        lifecycle.add("cachedValue", protocolPort("REGION.P.in.2", "INT"));
        lifecycle.add("currentValue", protocolPort("REGION.F.in.3", "INT"));
        lifecycle.add("state", protocolPort("REGION.P.out.0", "MAP"));
        lifecycle.add("observationTime",
                protocolPort("REGION.F.in.4", "INT"));
        lifecycle.add("updateInterval",
                protocolPort("REGION.F.in.5", "INT"));
        lifecycle.add("lifetime", protocolPort("REGION.F.in.6", "INT"));
        lifecycle.add("issueTime", protocolSymbol("issue", "INT"));
        lifecycle.add("retirementTime", protocolSymbol("retire", "INT"));
        lifecycle.add("credentialExpiry",
                protocolSymbol("credential_expiry", "INT"));
        lifecycle.add("memberExpiry",
                protocolSymbol("member_expiry", "INT"));
        relations.add(lifecycle);

        model.addProperty("relationCount", relations.size());
        model.add("relations", relations);
        return model;
    }

    private static JsonObject guardedWriter(String guard, String from,
                                            int writeSeq, int readSeq) {
        JsonObject relation = new JsonObject();
        relation.addProperty("edgeId", "EDGE." + guard);
        relation.addProperty("fromEndpoint", from);
        relation.addProperty("toEndpoint", "REGION.F.in.0");
        relation.addProperty("guardSymbol", guard);
        relation.addProperty("requiresOrder", true);
        relation.addProperty("requiresObjectIdentity", true);
        JsonObject binding = new JsonObject();
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("objectIdentityConfirmed", true);
        binding.addProperty("writeSeq", writeSeq);
        binding.addProperty("readSeq", readSeq);
        binding.addProperty("receiverObjectId", 41);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        relation.add("selectedBindings", bindings);
        return relation;
    }

    private static JsonObject protocolRelation(String id, String kind) {
        JsonObject relation = new JsonObject();
        relation.addProperty("relationId", id);
        relation.addProperty("kind", kind);
        relation.addProperty("evidenceConfirmed", true);
        return relation;
    }

    private static JsonObject protocolPort(String port, String valueType) {
        JsonObject endpoint = new JsonObject();
        endpoint.addProperty("kind", "PORT");
        endpoint.addProperty("portId", port);
        endpoint.addProperty("valueType", valueType);
        return endpoint;
    }

    private static JsonObject protocolSymbol(String symbol, String valueType) {
        JsonObject endpoint = new JsonObject();
        endpoint.addProperty("kind", "SYMBOL");
        endpoint.addProperty("symbol", symbol);
        endpoint.addProperty("valueType", valueType);
        return endpoint;
    }

    private static JsonArray singlePutEffect() {
        JsonArray effects = new JsonArray();
        effects.add(mapEffect("MAP_PUT", "REGION.P.in.0",
                "REGION.P.out.0", 0));
        return effects;
    }

    private static JsonArray mutationChain() {
        JsonArray effects = new JsonArray();
        effects.add(mapEffect("MAP_PUT", "REGION.P.in.0",
                "REGION.P.out.heapMap0.state1", 0));
        effects.add(mapEffect("MAP_REMOVE",
                "REGION.P.out.heapMap0.state1",
                "REGION.P.out.heapMap0.state2", 1));
        effects.add(mapEffect("MAP_CLEAR",
                "REGION.P.out.heapMap0.state2",
                "REGION.P.out.heapMap0.state3", 2));
        effects.add(mapEffect("MAP_PUT_ALL",
                "REGION.P.out.heapMap0.state3", "REGION.P.out.0", 3));
        return effects;
    }

    private static JsonObject mapEffect(String kind, String input,
                                        String output, int before) {
        JsonObject effect = new JsonObject();
        effect.addProperty("effectId", "HEAP_EFFECT.REGION.P." + before);
        effect.addProperty("kind", kind);
        effect.addProperty("stateFamily", "MAP_STATE.REGION.P.0");
        effect.addProperty("preState", "MAP_STATE.REGION.P.0." + before);
        effect.addProperty("postState",
                "MAP_STATE.REGION.P.0." + (before + 1));
        effect.addProperty("stateOrdinalBefore", before);
        effect.addProperty("stateOrdinalAfter", before + 1);
        effect.addProperty("inputPort", input);
        effect.addProperty("outputPort", output);
        if ("MAP_PUT".equals(kind) || "MAP_REMOVE".equals(kind)) {
            effect.add("keyExpression", constant("I", "Y_I_7"));
        }
        if ("MAP_PUT".equals(kind)) {
            effect.add("valueExpression", symbol("example/Value",
                    "producer_value"));
        }
        if ("MAP_PUT_ALL".equals(kind)) {
            effect.add("sourceExpression", symbol("L",
                    "M_L_field_REGION.P.in.1_example/Source"));
        }
        return effect;
    }

    private static JsonObject producerSummary(JsonArray effects,
                                              boolean complete) {
        return producerSummary(effects, new JsonArray(), complete);
    }

    private static JsonObject producerSummary(JsonArray effects,
                                              JsonArray initializers,
                                              boolean complete) {
        JsonObject summary = new JsonObject();
        summary.addProperty("summaryId", "SUMMARY.P");
        summary.addProperty("activationId", "ACT.P");
        summary.addProperty("regionId", "REGION.P");
        summary.addProperty("regionInstanceId",
                "REGION.P@fixture#call1");
        summary.addProperty("valid", true);
        summary.addProperty("relationallyComplete", complete);
        summary.add("pathCondition", new JsonArray());
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapStateInitializers", initializers);
        summary.add("heapEffects", effects);
        JsonObject model = new JsonObject();
        model.addProperty("policy", "RAW_SEMANTIC_PATH_ORDER_MAP_STATE_SSA");
        model.addProperty("candidateMutationCount",
                effects.size() + (complete ? 0 : 1));
        model.addProperty("effectCount", effects.size());
        model.addProperty("mapStateFamilyCount", effects.size() == 0 ? 0 : 1);
        model.addProperty("unsupportedMutationCount", complete ? 0 : 1);
        model.addProperty("malformedMutationCount", 0);
        model.addProperty("initializedInputCount", initializers.size());
        model.addProperty("initializerCount", initializers.size());
        model.addProperty("complete", complete);
        summary.add("heapEffectModel", model);
        return summary;
    }

    private static JsonObject requestedOutput(String port) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        return result;
    }

    private static JsonObject requestedSlice(String... inputs) {
        JsonObject result = new JsonObject();
        JsonArray ports = new JsonArray();
        for (String input : inputs) ports.add(input);
        result.add("inputPorts", ports);
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject runtimeEdgeBinding(
            String fromRegion, String fromInstance, String fromOutput,
            String toRegion, String toInstance, String toInput,
            int writeSeq, int readSeq, int receiver) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE." + fromRegion + ".TO."
                + toRegion);
        binding.addProperty("fromRegion", fromRegion);
        binding.addProperty("toRegion", toRegion);
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromOutput);
        binding.addProperty("toInputPort", toInput);
        binding.addProperty("writerEventSeq", writeSeq);
        binding.addProperty("readerEventSeq", readSeq);
        binding.addProperty("receiverObjectId", receiver);
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("objectIdentityConfirmed", true);
        binding.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        return binding;
    }

    private static JsonObject scalarSummary(String region, String summaryId,
                                            String activationId,
                                            String instanceId,
                                            String symbolName) {
        JsonObject result = producerSummary(new JsonArray(), true);
        result.addProperty("summaryId", summaryId);
        result.addProperty("activationId", activationId);
        result.addProperty("regionId", region);
        result.addProperty("regionInstanceId", instanceId);
        result.add("requestedOutput", requestedOutput(region + ".out.0"));
        result.getAsJsonObject("outputExpressions").add(
                region + ".out.0", symbol("I", symbolName));
        return result;
    }

    private static JsonObject port(String portId, String cell) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", portId);
        result.addProperty("cell", cell);
        return result;
    }

    private static JsonObject region(String regionId, String javaType,
                                     String cellName) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", regionId);
        JsonArray inputs = new JsonArray();
        inputs.add(port(regionId + ".in.0", "<example." + regionId
                + ": " + javaType + " " + cellName + ">"));
        JsonArray outputs = new JsonArray();
        outputs.add(port(regionId + ".out.0", "<example." + regionId
                + ": " + javaType + " " + cellName + ">"));
        result.add("symbolicInputs", inputs);
        result.add("outputs", outputs);
        return result;
    }

    private static void appendRegion(Fixture fixture, JsonObject region)
            throws Exception {
        Files.write(fixture.regions, (region + "\n").getBytes(
                        StandardCharsets.UTF_8),
                java.nio.file.StandardOpenOption.APPEND);
    }

    private static void addRegionPort(Fixture fixture, String regionId,
                                      String collection, JsonObject port)
            throws Exception {
        java.util.List<String> lines = Files.readAllLines(fixture.regions,
                StandardCharsets.UTF_8);
        java.util.List<String> updated = new java.util.ArrayList<>();
        boolean found = false;
        for (String line : lines) {
            if (line.trim().isEmpty()) continue;
            JsonObject region = JsonParser.parseString(line).getAsJsonObject();
            if (regionId.equals(region.get("regionId").getAsString())) {
                region.getAsJsonArray(collection).add(port.deepCopy());
                found = true;
            }
            updated.add(region.toString());
        }
        if (!found) throw new AssertionError("missing region " + regionId);
        Files.write(fixture.regions,
                (String.join("\n", updated) + "\n").getBytes(
                        StandardCharsets.UTF_8));
    }

    private static void installFatalRelations(Fixture fixture,
                                              JsonArray bindings)
            throws Exception {
        JsonObject fatal = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.fatal), StandardCharsets.UTF_8)
                .trim()).getAsJsonObject();
        JsonObject context = fatal.getAsJsonObject("symbolicContext");
        JsonArray relations = new JsonArray();
        JsonArray classes = new JsonArray();
        for (JsonElement element : bindings) {
            JsonObject binding = element.getAsJsonObject();
            String from = binding.get("fromOutputPort").getAsString();
            String to = binding.get("toInputPort").getAsString();
            JsonObject relation = new JsonObject();
            relation.addProperty("edgeId", binding.get("edgeId")
                    .getAsString());
            relation.addProperty("fromEndpoint", from);
            relation.addProperty("toEndpoint", to);
            JsonArray selected = new JsonArray();
            selected.add(binding.deepCopy());
            relation.add("selectedBindings", selected);
            relations.add(relation);
            JsonObject equality = new JsonObject();
            JsonArray members = new JsonArray();
            members.add(from);
            members.add(to);
            equality.add("members", members);
            classes.add(equality);
        }
        context.add("equalityClasses", classes);
        context.add("equalityRelations", new JsonArray());
        context.add("versionedStateMerges", relations);
        Files.write(fixture.fatal, (fatal + "\n").getBytes(
                StandardCharsets.UTF_8));
    }

    private static JsonObject emptyMapInitializer() {
        JsonObject initializer = new JsonObject();
        initializer.addProperty("initializerId",
                "HEAP_INITIALIZER.REGION.P.0");
        initializer.addProperty("kind", "MAP_EMPTY");
        initializer.addProperty("statePort",
                "REGION.P.state.heapMap0.empty");
        initializer.addProperty("stateFamily", "MAP_STATE.REGION.P.0");
        initializer.addProperty("stateId", "MAP_STATE.REGION.P.0.0");
        initializer.addProperty("requestedOutputPort", "REGION.P.out.0");
        initializer.addProperty("allocatedType", "java.util.HashMap");
        initializer.addProperty("staticInitializerId",
                "STATIC_INIT.REGION.P.0");
        initializer.addProperty("allocationEdgeId", "EDGE.ALLOC.0");
        initializer.addProperty("constructorArgumentCount", 0);
        JsonArray proof = new JsonArray();
        proof.add("EDGE.ALLOC.0");
        initializer.add("proofEdgeIds", proof);
        initializer.addProperty("proofComplete", true);
        initializer.addProperty("bindingAuthority",
                "STATIC_UNIQUE_DEFAULT_ALLOCATION_TO_REQUESTED_OUTPUT_"
                        + "PLUS_RUNTIME_UNIQUE_MAP_RECEIVER");
        initializer.addProperty("emptyStateAuthority",
                "JAVA_PLATFORM_DEFAULT_MAP_CONSTRUCTOR_SEMANTICS");
        return initializer;
    }

    private static JsonObject symbol(String javaType, String expression) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "SymbolExpression");
        result.addProperty("_java_type", javaType);
        result.addProperty("_exp", expression);
        return result;
    }

    private static JsonObject constant(String javaType, String expression) {
        JsonObject result = symbol(javaType, expression);
        result.addProperty("_type", "ConstExpr");
        return result;
    }

    private static JsonObject conString(String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ConStringSymbolExp");
        result.addProperty("_java_type", "java/lang/String");
        result.addProperty("_exp", "Y_L'String'_" + value);
        return result;
    }

    private static JsonObject opString(String operation,
                                       JsonElement... params) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "OpStrExpression");
        result.addProperty("_name", operation);
        result.addProperty("_is_not", false);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : params) arguments.add(parameter);
        result.add("_param_list", arguments);
        return result;
    }

    private static JsonObject method(String name, JsonElement resultValue,
                                     JsonElement... params) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "MethodExpression");
        result.addProperty("_name", name);
        JsonArray arguments = new JsonArray();
        for (JsonElement parameter : params) arguments.add(parameter);
        result.add("_param_list", arguments);
        result.add("_res_exp", resultValue);
        return result;
    }

    private static JsonObject codecUsername(JsonElement integer,
                                            String delimiter,
                                            String suffixName) {
        JsonObject prefix = opString("concat",
                opString("toString", integer), conString(delimiter));
        return opString("concat", prefix,
                symbol("java/lang/String", suffixName));
    }

    private static JsonObject codecParse(JsonElement integer,
                                         String delimiter, Integer limit,
                                         int index, Integer radix,
                                         JsonElement resultValue) {
        JsonObject receiver = codecUsername(integer, delimiter,
                "server_suffix");
        JsonObject split;
        if (limit == null) {
            split = method("java/lang/String splitElement",
                    conString("split_result"), receiver,
                    conString(delimiter), constant("I", "Y_I_" + index));
        } else {
            split = method("java/lang/String splitElement",
                    conString("split_result"), receiver,
                    conString(delimiter), constant("I", "Y_I_" + limit),
                    constant("I", "Y_I_" + index));
        }
        if (radix == null) {
            return method("java/lang/Integer parseInt", resultValue, split);
        }
        return method("java/lang/Integer parseInt", resultValue, split,
                constant("I", "Y_I_" + radix));
    }

    private static JsonObject integerCondition(String operator, int value) {
        return integerCondition(
                "M_I_field_REGION.P.in.2_example/Cache", operator, value);
    }

    private static JsonObject integerCondition(String raw, String operator,
                                               int value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", symbol("I", raw));
        result.addProperty("_op", operator);
        result.add("_right", constant("I", "Y_I_" + value));
        return result;
    }

    private static JsonObject placeholderCondition(String operator,
                                                   int count) {
        return binaryCondition(placeholderExpression("currentTimeMillis",
                        count), operator,
                constant("I", "Y_I_0"));
    }

    private static JsonObject placeholderExpression(String function,
                                                    int count) {
        JsonObject placeholder = new JsonObject();
        placeholder.addProperty("_type", "PlaceholderExpression");
        placeholder.addProperty("_place_holder_func", function);
        placeholder.addProperty("_count", count);
        return placeholder;
    }

    private static String vmCurrentTimeCell() {
        return "<java.lang.System: long currentTimeMillis()>.return";
    }

    private static void addVmPlaceholderCertificate(
            JsonObject container, String inputPort, int count) {
        String identity = "currentTimeMills#" + count;
        JsonObject requirement = new JsonObject();
        requirement.addProperty("kind",
                "UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT");
        requirement.addProperty("required", true);
        requirement.addProperty("inputPort", inputPort);
        requirement.addProperty("cell", vmCurrentTimeCell());
        requirement.addProperty("sourceKind", "ENVIRONMENT");
        requirement.addProperty("bindingMode",
                "VM_INTRINSIC_PLACEHOLDER");
        requirement.addProperty("placeholderFunction",
                "currentTimeMills");
        requirement.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        requirement.addProperty("modelControllable", false);
        requirement.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        requirement.addProperty("evidenceAuthority",
                "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION");
        JsonArray evidence = new JsonArray();
        evidence.add(identity);
        requirement.add("placeholderEvidenceIdentities", evidence);
        JsonArray requirements = new JsonArray();
        requirements.add(requirement);

        JsonObject inputAdmission = new JsonObject();
        inputAdmission.addProperty("complete", true);
        inputAdmission.add("globalSliceInputs", singletonString(inputPort));
        inputAdmission.add("requiredSliceInputs", singletonString(inputPort));
        inputAdmission.add("admittedVmIntrinsicPlaceholderInputs",
                singletonString(inputPort));
        inputAdmission.add("unforcedEnvironmentValidationRequirements",
                requirements.deepCopy());
        inputAdmission.add("failures", new JsonArray());
        inputAdmission.addProperty("authority",
                "STATIC_GLOBAL_SLICE_DEMAND_REFINED_BY_EXACT_"
                        + "TRANSFORMER_RUNTIME_PATH_PROOFS");
        inputAdmission.addProperty("vmIntrinsicPlaceholderAuthority",
                "EXACT_SCHEDULER_BINDING_PLUS_CUSTOM_JDK_STRUCTURED_"
                        + "PLACEHOLDER_EVIDENCE");
        container.add("inputMaterializationAdmission", inputAdmission);
        container.add("unforcedEnvironmentValidationRequirements",
                requirements);

        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind",
                "VM_INTRINSIC_PLACEHOLDER_PORT_BINDING");
        binding.addProperty("placeholderIdentity", identity);
        binding.addProperty("placeholderFunction", "currentTimeMills");
        binding.addProperty("placeholderCount", count);
        binding.addProperty("inputPort", inputPort);
        binding.addProperty("cell", vmCurrentTimeCell());
        binding.addProperty("javaTypeDescriptor", "J");
        binding.addProperty("sourceKind", "ENVIRONMENT");
        binding.addProperty("bindingMode", "VM_INTRINSIC_PLACEHOLDER");
        binding.addProperty("captureAuthority",
                "CUSTOM_JDK_SYMBOLIC_ND_FUNC");
        binding.addProperty("evidenceAuthority",
                "CUSTOM_JDK_STRUCTURED_PLACEHOLDER_EXPRESSION");
        binding.addProperty("modelControllable", false);
        binding.addProperty("replayPolicy",
                "UNFORCED_CONCRETE_ENVIRONMENT_VALIDATION");
        binding.addProperty("ownerAuthority",
                "UNIQUE_USED_PLACEHOLDER_IDENTITY_TO_EXACT_SLICE_INPUT");
        binding.addProperty("required", true);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        container.add("vmIntrinsicPlaceholderBindings", bindings);

        JsonObject admission = new JsonObject();
        admission.addProperty("schemaVersion", 1);
        admission.addProperty("kind",
                "VM_INTRINSIC_PLACEHOLDER_BINDING_ADMISSION");
        admission.addProperty("complete", true);
        admission.addProperty("bindingCount", 1);
        admission.add("bindings", bindings.deepCopy());
        admission.add("failures", new JsonArray());
        admission.addProperty("authority",
                "OWNER_EXACT_UNIQUE_USED_CUSTOM_JDK_PLACEHOLDER_V1");
        container.add("vmIntrinsicPlaceholderBindingAdmission", admission);
    }

    private static JsonObject arrayLoad(String array, String value) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "_array_expr");
        result.addProperty("_is_load", true);
        result.addProperty("_arr_str", array);
        result.add("_index_exp", constant("I", "Y_I_0"));
        result.add("_value_exp", symbol("I", value));
        return result;
    }

    private static JsonObject binaryCondition(com.google.gson.JsonElement left,
                                              String operator,
                                              com.google.gson.JsonElement right) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "BinaryExpression");
        result.add("_left", left);
        result.addProperty("_op", operator);
        result.add("_right", right);
        return result;
    }

    private static void prepareOutputCase(JsonObject summary, String operator,
                                          String observationId,
                                          String valueSymbol) {
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        summary.add("requestedOutput", requested);
        summary.getAsJsonArray("pathCondition").add(
                integerCondition(operator, 0));
        JsonArray observations = new JsonArray();
        observations.add(heapObservation(observationId, valueSymbol));
        summary.add("heapObservations", observations);
    }

    private static void prepareDynamicOutputCase(JsonObject summary,
                                                 String operator,
                                                 String observationId,
                                                 String valueSymbol,
                                                 String dynamicFieldSymbol) {
        summary.add("captureGoal", RegionCaptureGoal.outputClosure().toJson());
        JsonObject requested = new JsonObject();
        requested.addProperty("portId", "REGION.P.out.0");
        summary.add("requestedOutput", requested);
        summary.getAsJsonArray("pathCondition").add(binaryCondition(
                symbol("J", "M_J_field_" + dynamicFieldSymbol + "_expiry"),
                operator, constant("J", "Y_J_0")));
        JsonArray observations = new JsonArray();
        observations.add(dynamicHeapObservation(observationId, valueSymbol,
                dynamicFieldSymbol));
        summary.add("heapObservations", observations);
        JsonArray dynamicBindings = new JsonArray();
        dynamicBindings.add(runtimeDynamicFieldBinding(observationId,
                dynamicFieldSymbol, summary.get("activationId").getAsString()));
        summary.add("dynamicFieldBindings", dynamicBindings);
    }

    private static JsonObject heapObservation(String id, String valueSymbol) {
        JsonObject result = new JsonObject();
        result.addProperty("kind", "MAP_ENTRY_READ");
        result.addProperty("complete", true);
        result.addProperty("observationId", id);
        result.addProperty("statePort", "REGION.P.in.0");
        result.add("keyExpression", constant("I", "Y_I_7"));
        result.add("valueExpression", symbol("example/Value", valueSymbol));
        result.addProperty("entryBindingAuthority",
                "RUNTIME_BOUND_MAP_ENTRY_READ");
        result.addProperty("entryValueFieldBindingComplete", true);
        JsonObject binding = new JsonObject();
        binding.addProperty("fieldSymbol", "REGION.P.in.3");
        binding.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        binding.addProperty("fieldJavaType", "J");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        binding.add("fieldPath", fieldPath);
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        result.add("entryFieldBindings", bindings);
        return result;
    }

    private static JsonObject dynamicHeapObservation(
            String id, String valueSymbol, String dynamicFieldSymbol) {
        JsonObject result = heapObservation(id, valueSymbol);
        JsonObject binding = new JsonObject();
        binding.addProperty("schemaVersion", 1);
        binding.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        binding.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicFieldSymbol);
        binding.addProperty("baseInputSymbol", "REGION.P.in.3");
        binding.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
        binding.add("fieldExpression", symbol("J",
                "M_J_field_" + dynamicFieldSymbol + "_expiry"));
        binding.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        binding.addProperty("fieldJavaType", "long");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        binding.add("fieldPath", fieldPath);
        binding.addProperty("materializationSiteId",
                "<example.Store: void prune()>#u4");
        binding.addProperty("materializationOccurrence",
                dynamicFieldSymbol.endsWith(".2") ? 2 : 1);
        binding.addProperty("entryReadObservationId", id);
        binding.add("keyExpression", constant("I", "Y_I_7"));
        binding.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        binding.addProperty("baseInputRole",
                "FIELD_FAMILY_TEMPLATE_ONLY");
        binding.addProperty("authority",
                "RUNTIME_DYNAMIC_FIELD_INSTANCE_EXACT_EXPRESSION_AND_"
                        + "ENTRY_VALUE_TOKEN_JOIN");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        result.add("entryFieldBindings", bindings);
        return result;
    }

    private static JsonObject runtimeDynamicFieldBinding(
            String observationId, String dynamicFieldSymbol,
            String activationId) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "DYNAMIC_MAP_ENTRY_FIELD_BINDING");
        result.addProperty("dynamicBindingId",
                "DYNAMIC_FIELD:" + dynamicFieldSymbol);
        result.addProperty("baseInputSymbol", "REGION.P.in.3");
        result.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
        result.addProperty("materializationSiteId",
                "<example.Store: void prune()>#u4");
        result.addProperty("materializationOccurrence",
                dynamicFieldSymbol.endsWith(".2") ? 2 : 1);
        result.addProperty("fieldSignature",
                "<example.Value: long expiry>");
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        result.add("fieldPath", fieldPath);
        result.addProperty("leafOwnerObjectToken", 41);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", activationId);
        result.addProperty("entryReadObservationId", observationId);
        result.add("keyExpression", constant("I", "Y_I_7"));
        result.addProperty("keyExpressionAuthority",
                "CONCRETE_IMMUTABLE_ENTRY_KEY_AT_NEXT");
        result.addProperty("authority",
                "ACTIVATION_LOCAL_ENTRY_VALUE_IDENTITY_AND_STABLE_"
                        + "FIELD_SITE_OCCURRENCE");
        result.addProperty("complete", true);
        return result;
    }

    private static JsonObject runtimeContainerFieldBinding(String dynamic) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 2);
        result.addProperty("kind",
                "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
        result.addProperty("dynamicBindingId", "DYNAMIC_FIELD:" + dynamic);
        result.addProperty("baseInputSymbol", "REGION.P.in.3");
        result.addProperty("dynamicFieldSymbol", dynamic);
        result.addProperty("materializationSiteId", "SITE.CONTAINER");
        result.addProperty("materializationOccurrence", 1);
        result.addProperty("fieldSignature", "<example.Key: int id>");
        JsonArray path = new JsonArray();
        path.add("id");
        result.add("fieldPath", path);
        result.addProperty("leafOwnerObjectToken", 302L);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", "ACT.P");
        result.addProperty("containerBindingId", "BIND.ARRAY.1");
        result.addProperty("containerInputPort", "REGION.P.in.4");
        result.addProperty("containerInputCell", "<Keys: Key[] keys>");
        result.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        result.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        result.addProperty("elementIndex", 2);
        result.addProperty("elementOccurrence", 1);
        result.addProperty("declaredFieldOwnerClass", "example.Key");
        result.addProperty("declaredFieldType", "int");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "ARRAY_INDEX");
        selector.addProperty("bindingId", "BIND.ARRAY.1");
        selector.addProperty("containerInputPort", "REGION.P.in.4");
        selector.addProperty("containerInputCell", "<Keys: Key[] keys>");
        selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
        selector.addProperty("resolvedFromSelectorAuthority",
                "EXACT_ARRAY_INDEX");
        selector.addProperty("elementIndex", 2);
        selector.addProperty("elementOccurrence", 1);
        selector.addProperty("declaredFieldOwnerClass", "example.Key");
        selector.addProperty("declaredFieldType", "int");
        selector.addProperty("containerObjectToken", 301L);
        selector.addProperty("elementObjectToken", 302L);
        selector.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        selector.addProperty("objectTokenScope", "ACT.P");
        selector.addProperty("authority",
                "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                        + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
        selector.addProperty("complete", true);
        result.add("containerSelector", selector);
        result.addProperty("authority",
                "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_IDENTITY_AND_"
                        + "STABLE_FIELD_SITE_OCCURRENCE");
        result.addProperty("complete", true);
        return result;
    }

    private static JsonArray runtimeMapProjectionFieldBindings(
            String operation) {
        JsonArray result = new JsonArray();
        JsonArray tokens = new JsonArray();
        tokens.add(601L);
        tokens.add(602L);
        JsonArray keys = new JsonArray();
        keys.add(constant("java/lang/Integer", "Y_I_11"));
        keys.add(constant("java/lang/Integer", "Y_I_22"));
        for (int index = 0; index < 2; index++) {
            String dynamic = "REGION.P.in.5.field.cccccccccccc.occ."
                    + (index + 1);
            JsonObject binding = new JsonObject();
            binding.addProperty("schemaVersion", 3);
            binding.addProperty("kind",
                    "DYNAMIC_MAP_VALUE_OUTPUT_ARRAY_ELEMENT_FIELD_BINDING");
            binding.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            binding.addProperty("baseInputSymbol", "REGION.P.in.5");
            binding.addProperty("dynamicFieldSymbol", dynamic);
            binding.addProperty("materializationSiteId",
                    "SITE.MAP#map-element:BIND.MAP.FIELD");
            binding.addProperty("materializationOccurrence", index + 1);
            binding.addProperty("fieldSignature",
                    "<example.Value: long expiry>");
            JsonArray path = new JsonArray();
            path.add("expiry");
            binding.add("fieldPath", path);
            binding.addProperty("leafOwnerObjectToken", 601L + index);
            binding.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            binding.addProperty("objectTokenScope", "ACT.P");
            binding.addProperty("fieldJavaType", "long");
            binding.addProperty("entrySnapshotElementCount", 2);
            binding.addProperty("outputElementCount", 2);
            binding.add("entrySnapshotElementObjectTokens",
                    tokens.deepCopy());
            binding.add("entrySnapshotMapKeyExpressions",
                    keys.deepCopy());
            binding.addProperty("entryKeyExpressionAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
            binding.addProperty("entrySetViewOrderAuthority",
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            binding.addProperty("runtimeSymbolizationAuthority",
                    "EXACT_SYMBOLIZE_FIELD_OBSERVATION_AND_SYMBOLIZED_INPUT");
            binding.addProperty("projectionEvidenceAuthority",
                    "UNIQUE_ENTRYSET_KEYED_SNAPSHOT_AND_OUTPUT_IDENTITY_"
                            + "VALIDATION");
            binding.addProperty("outputValidationMode",
                    "ROOT_RETURN_PROJECTED_FIELD");
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "MAP_OUTPUT_ARRAY_INDEX");
            selector.addProperty("bindingId", "BIND.MAP.FIELD");
            selector.addProperty("mapInputPort", "REGION.P.in.5");
            selector.addProperty("mapInputCell",
                    "<example.Producer: java.util.Map values>");
            selector.addProperty("outputPort", "REGION.P.out.2");
            selector.addProperty("outputCell",
                    "<example.Payload: example.Value[] values>");
            selector.addProperty("mapProjectionOperation", operation);
            selector.addProperty("outputIndex", index);
            selector.addProperty("elementOccurrence", index + 1);
            selector.addProperty("declaredFieldOwnerClass",
                    "example.Value");
            selector.addProperty("declaredFieldType", "long");
            selector.addProperty("declaredFieldSignature",
                    "<example.Value: long expiry>");
            selector.addProperty("mapObjectToken", 501L);
            selector.addProperty("elementObjectToken", 601L + index);
            selector.addProperty("outputArrayObjectToken", 701L);
            selector.addProperty("outputIdentityVerified", true);
            selector.addProperty("outputVerificationAuthority",
                    "ACTIVE_REGION_ROOT_RETURN_EXACT_PROJECTED_FIELD");
            selector.addProperty("mapImplementationClass",
                    "java.util.LinkedHashMap");
            selector.addProperty("mapImplementationAuthority",
                    "EXACT_RUNTIME_CLASS_JAVA_UTIL_HASHMAP_OR_"
                            + "LINKEDHASHMAP_JAVA_EQUALS_HASHCODE_"
                            + "EXTENSIONAL_V1");
            selector.addProperty("entryConcreteFieldValueCaptured", true);
            selector.addProperty("noInterveningFieldWriteVerified", true);
            selector.addProperty("outputFieldValueVerified", true);
            selector.addProperty("fieldValueFlowAuthority",
                    "SAME_EXECUTION_BOUNDED_OBSERVED_SCHEDULE_EXACT_"
                            + "DECLARED_FIELD_ENTRY_VALUE_PLUS_NO_"
                            + "INTERVENING_RUNTIME_FIELD_WRITE_AND_EXACT_"
                            + "OUTPUT_RECHECK");
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", "ACT.P");
            selector.addProperty("crossExecutionOrdinalAuthority", "NONE");
            selector.add("expectedMapKey", keys.get(index).deepCopy());
            selector.addProperty("expectedMapKeyAuthority",
                    "CONCRETE_IMMUTABLE_MAP_ENTRY_KEY_AT_ENTRYSET_SNAPSHOT");
            selector.addProperty("sourceOutputIndexAuthority",
                    "ENTRYSET_AND_MAP_VIEW_TO_ARRAY_SAME_EXECUTION_"
                            + "POSITIONAL_REFERENCE_EQUALITY");
            selector.addProperty("replaySelectionAuthority",
                    "IMMUTABLE_MAP_KEY_LOOKUP_THEN_SAME_OUTPUT_INDEX_AND_"
                            + "EXACT_OUTPUT_IDENTITY");
            selector.addProperty("authority",
                    "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                            + "EXACT_OUTPUT_IDENTITY");
            selector.addProperty("complete", true);
            binding.add("mapProjectionSelector", selector);
            binding.addProperty("authority",
                    "IMMUTABLE_MAP_ENTRY_KEY_AND_SAME_OUTPUT_INDEX_WITH_"
                            + "EXACT_OUTPUT_IDENTITY");
            binding.addProperty("complete", true);
            result.add(binding);
        }
        return result;
    }

    private static JsonArray runtimeMapProjectionFieldBindingsWithKeys(
            JsonArray keys) {
        if (keys == null || keys.size() != 2) {
            throw new IllegalArgumentException("exactly two map keys needed");
        }
        JsonArray result = runtimeMapProjectionFieldBindings(
                "MAP_VALUES_VIEW");
        for (int index = 0; index < result.size(); index++) {
            JsonObject binding = result.get(index).getAsJsonObject();
            binding.add("entrySnapshotMapKeyExpressions", keys.deepCopy());
            binding.getAsJsonObject("mapProjectionSelector").add(
                    "expectedMapKey", keys.get(index).deepCopy());
        }
        return result;
    }

    private static JsonObject closedPathManifest() {
        JsonObject result = new JsonObject();
        result.addProperty("complete", true);
        result.addProperty("status", "COMPLETE_BOUNDED_PATH_CLOSURE");
        return result;
    }

    private static JsonObject projectionBySource(JsonArray catalog,
                                                 String sourceSummaryId) {
        for (com.google.gson.JsonElement element : catalog) {
            JsonObject projection = element.getAsJsonObject();
            if (sourceSummaryId.equals(projection.get(
                    "sourceSummaryId").getAsString())) {
                return projection;
            }
        }
        throw new AssertionError("missing projection for " + sourceSummaryId
                + " in " + catalog);
    }

    private static JsonObject rawSymbolMapping(JsonObject projection,
                                               String rawEngineSymbol) {
        for (com.google.gson.JsonElement element : projection.getAsJsonArray(
                "rawEngineSymbolMappings")) {
            JsonObject mapping = element.getAsJsonObject();
            if (rawEngineSymbol.equals(mapping.get(
                    "rawEngineSymbol").getAsString())) {
                return mapping;
            }
        }
        throw new AssertionError("missing raw symbol " + rawEngineSymbol
                + " in " + projection);
    }

    private static int countDeclarationLines(String smt, String... fragments) {
        int count = 0;
        for (String line : smt.split("\\r?\\n")) {
            if (!line.startsWith("(declare-const ")) continue;
            boolean matches = true;
            for (String fragment : fragments) {
                matches &= line.contains(fragment);
            }
            if (matches) count++;
        }
        return count;
    }

    private static int countLines(String text, String... fragments) {
        int count = 0;
        for (String line : text.split("\\r?\\n")) {
            boolean matches = true;
            for (String fragment : fragments) matches &= line.contains(fragment);
            if (matches) count++;
        }
        return count;
    }

    private static java.util.List<String> linesContaining(String text,
                                                          String fragment) {
        java.util.List<String> result = new java.util.ArrayList<>();
        for (String line : text.split("\\r?\\n")) {
            if (line.contains(fragment)) result.add(line);
        }
        return result;
    }

    private static String lineContaining(String text, String fragment) {
        for (String line : text.split("\\r?\\n")) {
            if (line.contains(fragment)) return line;
        }
        return "";
    }

    private static String declaredSymbolContaining(String smt,
                                                   String fragment) {
        for (String line : smt.split("\\r?\\n")) {
            if (!line.startsWith("(declare-const ")
                    || !line.contains(fragment)) continue;
            int start = "(declare-const ".length();
            int end = line.indexOf(' ', start);
            if (end > start) return line.substring(start, end);
        }
        return "";
    }

    private static String declaredFunctionContaining(String smt,
                                                     String fragment) {
        for (String line : smt.split("\r?\n")) {
            if (!line.startsWith("(declare-fun ")
                    || !line.contains(fragment)) continue;
            int start = "(declare-fun ".length();
            int end = line.indexOf(' ', start);
            if (end > start) return line.substring(start, end);
        }
        return "";
    }

    private static JsonObject arrayValueExpression(
            String javaType, String componentType, boolean complete,
            JsonElement... values) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "ArrayValueExpression");
        result.addProperty("_schema_version", 1);
        result.addProperty("_java_type", javaType);
        result.addProperty("_component_java_type", componentType);
        result.addProperty("_concrete_length", values.length);
        result.add("_length_exp", constant("I", "Y_I_" + values.length));
        result.addProperty("_elements_complete", complete);
        result.addProperty("_authority", "VM_EXACT_FINITE_ARRAY_VALUE_V1");
        JsonArray elements = new JsonArray();
        for (int index = 0; index < values.length; index++) {
            JsonObject element = new JsonObject();
            element.addProperty("index", index);
            JsonObject expression = values[index].getAsJsonObject();
            String type = expression.get("_type").getAsString();
            String raw = expression.has("_exp")
                    ? expression.get("_exp").getAsString() : "";
            element.addProperty("provenance", "N".equals(raw)
                    ? "CONCRETE_NULL" : "ConstExpr".equals(type)
                    ? "CONCRETE_PRIMITIVE" : "SYMBOLIC_ELEMENT");
            element.add("expression", values[index].deepCopy());
            elements.add(element);
        }
        result.add("_elements", elements);
        return result;
    }

    private static JsonObject engineArrayInputBinding(
            String activationId, String inputPort, String inputCell,
            String descriptor, String engineArrayId, long objectToken,
            JsonElement... values) {
        JsonObject expression = arrayValueExpression(descriptor,
                descriptor.substring(1), true, values);
        expression.addProperty("_engine_array_id", engineArrayId);
        expression.addProperty("_engine_array_id_authority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "ENGINE_ARRAY_TO_INPUT_PORT");
        result.addProperty("sourceActivationId", activationId);
        result.addProperty("inputPort", inputPort);
        result.addProperty("inputCell", inputCell);
        result.addProperty("inputJavaType", descriptor);
        result.addProperty("inputJavaTypeDescriptor", descriptor);
        result.addProperty("symbolizationPrefix", inputPort);
        result.addProperty("symbolizationMode",
                "DIRECT_ARRAY_VALUE_WITH_CANONICAL_INPUT_PREFIX");
        result.addProperty("engineArrayId", engineArrayId);
        result.addProperty("engineArrayIdAuthority",
                "VM_ACTIVE_SYM_ARRAY_ID_V1");
        result.addProperty("arrayObjectToken", objectToken);
        result.addProperty("symbolizationArrayObjectToken", objectToken);
        result.addProperty("symbolizationIdentityAuthority",
                "SAME_JAVA_REFERENCE_PASSED_TO_SYMBOLIZE_AND_"
                        + "EXPRESSION_CAPTURE");
        result.addProperty("sameArrayObjectTokenVerified", true);
        result.addProperty("objectTokenAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
        result.addProperty("objectTokenScope", activationId);
        result.addProperty("captureAuthority",
                "SAME_LIVE_ARRAY_AFTER_EXACT_INPUT_ACTION_SYMBOLIZATION");
        result.add("arrayValueExpression", expression);
        result.addProperty("complete", true);
        return result;
    }

    private static JsonArray singleton(JsonElement value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static JsonArray singletonString(String value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }

    private static void installArrayProducerFlow(
            Fixture fixture, String producerCell, String consumerCell,
            JsonElement outputExpression) throws Exception {
        addRegionPort(fixture, "REGION.P", "outputs",
                port("REGION.P.out.2", producerCell));
        addRegionPort(fixture, "REGION.F", "symbolicInputs",
                port("REGION.F.in.8", consumerCell));
        JsonObject summary = producerSummary(singlePutEffect(), true);
        summary.getAsJsonObject("outputExpressions").add(
                "REGION.P.out.2", outputExpression.deepCopy());
        JsonArray bindings = new JsonArray();
        bindings.add(runtimeEdgeBinding("REGION.P",
                "REGION.P@fixture#call1", "REGION.P.out.0",
                "REGION.F", "REGION.F@fixture#call2", "REGION.F.in.0",
                10, 30, 101));
        bindings.add(runtimeEdgeBinding("REGION.P",
                "REGION.P@fixture#call1", "REGION.P.out.2",
                "REGION.F", "REGION.F@fixture#call2", "REGION.F.in.8",
                11, 31, 102));
        summary.add("edgeBindings", bindings);
        writeSummary(fixture, summary);
        installFatalRelations(fixture, bindings);
    }

    private static JsonObject containerFieldSummary(
            Fixture fixture, String selectorAuthority, int index,
            int occurrence, boolean runtimeDiscovery) throws Exception {
        String containerCell = "<example.Keys: example.Key[] allKeys>";
        addRegionPort(fixture, "REGION.P", "symbolicInputs",
                port("REGION.P.in.4", containerCell));
        JsonArray effects = new JsonArray();
        effects.add(mapEffect("MAP_IDENTITY", "REGION.P.in.0",
                "REGION.P.out.0", 0));
        JsonObject summary = producerSummary(effects, true);
        summary.add("requestedOutput", requestedOutput("REGION.P.out.0"));
        JsonObject slice = requestedSlice("REGION.P.in.0",
                "REGION.P.in.3", "REGION.P.in.4");
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion", 1);
        declaration.addProperty("kind", "ARRAY_ELEMENT_FIELD");
        declaration.addProperty("bindingId", "BIND.ARRAY.0");
        declaration.addProperty("baseInputSymbol", "REGION.P.in.3");
        declaration.addProperty("containerInputPort", "REGION.P.in.4");
        declaration.addProperty("containerInputCell", containerCell);
        declaration.addProperty("selectorAuthority", selectorAuthority);
        declaration.addProperty("elementIndex", index);
        declaration.addProperty("elementOccurrence", occurrence);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("expiry");
        declaration.add("fieldPath", fieldPath);
        declaration.addProperty("declaredFieldSignature",
                "<example.Key: long expiry>");
        declaration.addProperty("declaredFieldOwnerClass", "example.Key");
        declaration.addProperty("declaredFieldType", "long");
        declaration.addProperty("declaredFieldName", "expiry");
        declaration.addProperty("method",
                "<example.Store: void update(example.Keys)>");
        declaration.addProperty("fieldMaterializationSiteId",
                "<example.Store: void update(example.Keys)>#u14");
        declaration.addProperty("arrayLoadSiteId",
                "<example.Store: void update(example.Keys)>#u13");
        JsonArray proof = new JsonArray();
        proof.add("A");
        proof.add("C");
        proof.add("G");
        proof.add("P");
        declaration.add("proofCausalEdgeIds", proof);
        declaration.addProperty("proofAuthority",
                "STATIC_EXACT_CONTAINER_ARRAY_ACCESSOR_DECLARED_"
                        + "FIELD_FOUR_EDGE_JOIN_V1");
        declaration.addProperty("complete", true);
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        slice.add("containerElementFieldBindings", declarations);
        summary.add("requestedOutputSlice", slice);

        if (runtimeDiscovery) {
            String dynamic = "REGION.P.in.3.field.cccccccccccc.occ.1";
            JsonObject fieldExpression = symbol("J",
                    "M_J_field_" + dynamic + "_example/Key");
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    fieldExpression.deepCopy(), ">",
                    constant("J", "Y_J_0")));
            JsonObject runtime = new JsonObject();
            runtime.addProperty("schemaVersion", 2);
            runtime.addProperty("kind",
                    "DYNAMIC_CONTAINER_ELEMENT_FIELD_BINDING");
            runtime.addProperty("dynamicBindingId",
                    "DYNAMIC_FIELD:" + dynamic);
            runtime.addProperty("baseInputSymbol", "REGION.P.in.3");
            runtime.addProperty("dynamicFieldSymbol", dynamic);
            runtime.addProperty("materializationSiteId",
                    "<example.Store: void update(example.Keys)>#u14");
            runtime.addProperty("materializationOccurrence", 1);
            runtime.addProperty("fieldSignature",
                    "<example.Key: long expiry>");
            runtime.add("fieldPath", fieldPath.deepCopy());
            runtime.add("fieldExpression", fieldExpression.deepCopy());
            runtime.addProperty("fieldJavaType", "long");
            runtime.addProperty("containerBindingId", "BIND.ARRAY.0");
            runtime.addProperty("containerInputPort", "REGION.P.in.4");
            runtime.addProperty("containerInputCell", containerCell);
            runtime.addProperty("leafOwnerObjectToken", 202L);
            runtime.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            runtime.addProperty("objectTokenScope", "ACT.P");
            runtime.addProperty("authority",
                    "ACTIVATION_LOCAL_EXPLICIT_ARRAY_INDEX_OWNER_"
                            + "IDENTITY_AND_STABLE_FIELD_SITE_OCCURRENCE");
            runtime.addProperty("complete", true);
            JsonObject selector = new JsonObject();
            selector.addProperty("kind", "ARRAY_INDEX");
            selector.addProperty("bindingId", "BIND.ARRAY.0");
            selector.addProperty("containerInputPort", "REGION.P.in.4");
            selector.addProperty("containerInputCell", containerCell);
            selector.addProperty("selectorAuthority", "EXACT_ARRAY_INDEX");
            selector.addProperty("resolvedFromSelectorAuthority",
                    "DISCOVER_UNIQUE_IDENTITY_INDEX");
            selector.addProperty("elementIndex", 2);
            selector.addProperty("elementOccurrence", 1);
            selector.addProperty("declaredFieldOwnerClass", "example.Key");
            selector.addProperty("declaredFieldType", "long");
            selector.addProperty("containerObjectToken", 201L);
            selector.addProperty("elementObjectToken", 202L);
            selector.addProperty("objectTokenAuthority",
                    "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN");
            selector.addProperty("objectTokenScope", "ACT.P");
            selector.addProperty("authority",
                    "EXPLICIT_CONTAINER_INPUT_ARRAY_INDEX_AND_"
                            + "ACTIVATION_LOCAL_ELEMENT_IDENTITY");
            selector.addProperty("complete", true);
            runtime.add("containerSelector", selector);
            JsonArray runtimeBindings = new JsonArray();
            runtimeBindings.add(runtime);
            summary.add("dynamicFieldBindings", runtimeBindings);
        }
        return summary;
    }

    private static void writeSummary(Fixture fixture, JsonObject summary)
            throws Exception {
        Files.write(fixture.summaries,
                (summary.toString() + "\n").getBytes(StandardCharsets.UTF_8));
    }

    private static ConcolicSmtComposer.Arguments arguments(Fixture fixture) {
        return ConcolicSmtComposer.Arguments.parse(new String[]{
                "--fatal-query", fixture.fatal.toString(),
                "--summaries", fixture.summaries.toString(),
                "--regions", fixture.regions.toString(),
                "--merge-plan", fixture.merge.toString(),
                "--output", fixture.output.toString(),
                "--manifest", fixture.manifest.toString(),
                "--fatal-region", "REGION.F",
                "--activation-id", "ACT.F"
        });
    }

    private static Fixture fixture(Path root, boolean includeProducerSummary)
            throws Exception {
        Fixture fixture = new Fixture(root);
        String regions = "{\"regionId\":\"REGION.P\","
                + "\"symbolicInputs\":[{\"portId\":\"REGION.P.in.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.P.in.1\","
                + "\"cell\":\"<example.Source: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.P.in.2\","
                + "\"cell\":\"<example.Cache: int cachedValue>\"},"
                + "{\"portId\":\"REGION.P.in.3\","
                + "\"cell\":\"<example.Value: long expiry>\"},"
                + "{\"portId\":\"REGION.P.in.4\","
                + "\"cell\":\"<example.Keys: example.Key[] keys>\"},"
                + "{\"portId\":\"REGION.P.in.5\","
                + "\"cell\":\"<example.Producer: java.util.Map values>\"}],"
                + "\"outputs\":[{\"portId\":\"REGION.P.out.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.P.out.1\","
                + "\"cell\":\"<example.Codec: java.lang.String encode(int)>"
                + ".return\"},{\"portId\":\"REGION.P.out.2\","
                + "\"cell\":\"<example.Payload: example.Value[] values>\"}]}\n"
                + "{\"regionId\":\"REGION.F\","
                + "\"symbolicInputs\":[{\"portId\":\"REGION.F.in.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"},"
                + "{\"portId\":\"REGION.F.in.1\","
                + "\"cell\":\"<example.Request: int key>\"},"
                + "{\"portId\":\"REGION.F.in.2\","
                + "\"cell\":\"<example.Transport: java.lang.String value>\"},"
                + "{\"portId\":\"REGION.F.in.3\","
                + "\"cell\":\"<example.Store: int currentValue>\"},"
                + "{\"portId\":\"REGION.F.in.4\","
                + "\"cell\":\"<example.Clock: long now>\"},"
                + "{\"portId\":\"REGION.F.in.5\","
                + "\"cell\":\"<example.Policy: long updateInterval>\"},"
                + "{\"portId\":\"REGION.F.in.6\","
                + "\"cell\":\"<example.Policy: long lifetime>\"},"
                + "{\"portId\":\"REGION.F.in.7\","
                + "\"cell\":\"<example.Protocol: int constant>\"}],"
                + "\"outputs\":[]}\n";
        regions += "{\"regionId\":\"REGION.D\","
                + "\"symbolicInputs\":[{\"portId\":\"REGION.D.in.0\","
                + "\"cell\":\"<example.Store: java.util.Map state>\"}],"
                + "\"outputs\":[]}\n";
        Files.write(fixture.regions, regions.getBytes(StandardCharsets.UTF_8));

        String context = "{\"regionInstanceId\":"
                + "\"REGION.F@fixture#call2\","
                + "\"equalityClasses\":[{\"members\":["
                + "\"REGION.P.out.0\",\"REGION.F.in.0\","
                + "\"REGION.D.in.0\"]}],"
                + "\"equalityRelations\":[],"
                + "\"versionedStateMerges\":[{"
                + "\"edgeId\":\"EDGE.0\","
                + "\"fromEndpoint\":\"REGION.P.out.0\","
                + "\"toEndpoint\":\"REGION.F.in.0\","
                + "\"selectedBindings\":[{\"orderConfirmed\":true,"
                + "\"writeSeq\":10,\"readSeq\":20}]}]}";
        String fatal = "{\"activationId\":\"ACT.F\","
                + "\"regionId\":\"REGION.F\",\"siteId\":\"F#u2\","
                + "\"readyForSolver\":true,\"constraints\":[{"
                + "\"_type\":\"MethodExpression\","
                + "\"_name\":\"java/util/HashMap get\","
                + "\"_param_list\":[{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"L\","
                + "\"_exp\":\"M_L_field_REGION.F.in.0_example/Store\"},"
                + "{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"I\","
                + "\"_exp\":\"M_I_field_REGION.F.in.1_example/Request\"}],"
                + "\"_res_exp\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"example/Value\","
                + "\"_exp\":\"map_result\"}},{"
                + "\"_type\":\"BinaryExpression\","
                + "\"_left\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"example/Value\","
                + "\"_exp\":\"map_result\"},\"_op\":\"==\","
                + "\"_right\":{\"_type\":\"SymbolExpression\","
                + "\"_java_type\":\"\",\"_exp\":\"N\"}}],"
                + "\"symbolicContext\":" + context + "}\n";
        Files.write(fixture.fatal, fatal.getBytes(StandardCharsets.UTF_8));

        Files.write(fixture.merge, context.getBytes(StandardCharsets.UTF_8));
        if (includeProducerSummary) {
            writeSummary(fixture, producerSummary(singlePutEffect(), true));
        } else {
            Files.write(fixture.summaries, new byte[0]);
        }
        return fixture;
    }

    private static final class Fixture {
        private final Path fatal;
        private final Path summaries;
        private final Path regions;
        private final Path merge;
        private final Path output;
        private final Path manifest;

        private Fixture(Path root) {
            fatal = root.resolve("fatal.jsonl");
            summaries = root.resolve("summaries.jsonl");
            regions = root.resolve("regions.jsonl");
            merge = root.resolve("merge.json");
            output = root.resolve("composed.smt2");
            manifest = root.resolve("manifest.json");
        }
    }
}
