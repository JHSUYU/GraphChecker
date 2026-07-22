package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
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
            assertTrue(manifest.has("fatalRegionInstanceId"));
            assertTrue(manifest.has("fatalOccurrence"));
            assertTrue(manifest.has("fatalDesiredOutcome"));
            assertFalse(manifest.has("fatalReplayContractId"));
            assertFalse(manifest.has("fatalSolverPathContextId"));
            assertEquals(1, manifest.getAsJsonArray(
                    "summaryInputArtifacts").size());
            assertEquals(4, relationships.size());
            assertFalse(relationships.has("fatalRegionInstanceId"));
            assertFalse(relationships.has("composedSmtArtifact"));
            BooleanReachConditionExtractor.validateArtifactBindings(
                    fixture.output, fixture.regions, relationshipsPath,
                    manifest);
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

            assertFalse(result.manifest.toString(), candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "MissingTargetInstanceSymbolicContext"));
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

            assertTrue(candidateReady(result.manifest));
            assertEquals(2, result.relationships.get(
                    "schemaVersion").getAsInt());
            assertEquals("CANDIDATE_ONLY", result.relationships.get(
                    "trustState").getAsString());
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

            assertFalse(candidateReady(result.manifest));
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
            JsonArray constraints = fatalConstraints(fatal);
            JsonObject lookup = constraints.get(0)
                    .getAsJsonObject();
            lookup.getAsJsonArray("_param_list").set(1,
                    placeholderExpression("java/lang/String.split", 3));
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(candidateReady(result.manifest));
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
            JsonArray constraints = fatalConstraints(fatal);
            constraints.add(binaryCondition(
                    placeholderExpression("currentTimeMills", 3), ">",
                    constant("J", "Y_J_0")));
            setFatalConstraints(fatal, constraints);
            addVmPlaceholderCertificate(fatal, "REGION.F.in.8", 3);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(candidateReady(result.manifest));
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
            String vmClock = currentTimeMillisCell();
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.6", vmClock));
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonArray("pathCondition").add(binaryCondition(
                    placeholderExpression("currentTimeMills", 3), ">",
                    constant("J", "Y_J_0")));
            addVmPlaceholderCertificate(summary, "REGION.P.in.6", 3,
                    vmClock);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(candidateReady(result.manifest));
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
                assertEquals(1, element.getAsJsonObject().getAsJsonArray(
                        "unforcedEnvironmentValidationRequirements").size());
            }
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(candidateReady(result.manifest));
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
    public void rejectsTamperedVmPlaceholderBinding()
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
            summary.getAsJsonArray("vmIntrinsicPlaceholderBindings")
                    .get(0).getAsJsonObject()
                    .addProperty("placeholderCount", 2);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "BINDING_INVALID"));
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
            JsonObject username = opString("concat", conString(""),
                    codecUsername(upstreamKey, " ",
                            "nn_username_suffix"));
            JsonObject equality = runtimeValueEqualityBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.1",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.2", 11, 21);

            // The producer summary exercises the standalone concat and
            // primitive-int toString encoding used before transport.
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.1", username.deepCopy());
            JsonArray edgeBindings = new JsonArray();
            edgeBindings.add(equality.deepCopy());
            summary.add("edgeBindings", edgeBindings);
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
            JsonObject transportedUsername = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            parse.getAsJsonArray("_param_list").get(0).getAsJsonObject()
                    .getAsJsonArray("_param_list").set(0,
                    transportedUsername.deepCopy());
            JsonObject computedPoolKey = method(
                    "java/lang/String splitElement",
                    symbol("java/lang/String", "M_L_pool_key"),
                    username.deepCopy(), conString(" "),
                    constant("I", "Y_I_1"));
            JsonObject poolManager = symbol("example/SecretManager",
                    "M_L_pool_manager");
            JsonObject poolLookup = method("java/util/HashMap get",
                    poolManager.deepCopy(),
                    symbol("java/util/HashMap", "M_L_pool_managers"),
                    computedPoolKey);
            JsonArray oldConstraints = fatalConstraints(fatal);
            JsonObject lookup = oldConstraints.get(0).getAsJsonObject();
            lookup.getAsJsonArray("_param_list").set(1,
                    serverKey.deepCopy());
            JsonArray constraints = new JsonArray();
            constraints.add(parse);
            constraints.add(poolLookup);
            constraints.add(binaryCondition(poolManager.deepCopy(), "!=",
                    symbol("", "N")));
            for (JsonElement constraint : oldConstraints) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            JsonObject context = fatal.getAsJsonObject("symbolicContext");
            JsonObject equalityRelation = new JsonObject();
            equalityRelation.addProperty("edgeId",
                    equality.get("edgeId").getAsString());
            equalityRelation.addProperty("fromEndpoint",
                    "REGION.P.out.1");
            equalityRelation.addProperty("toEndpoint", "REGION.F.in.2");
            JsonArray selectedBindings = new JsonArray();
            selectedBindings.add(equality.deepCopy());
            equalityRelation.add("selectedBindings", selectedBindings);
            context.getAsJsonArray("equalityRelations").add(
                    equalityRelation);
            JsonObject equalityClass = new JsonObject();
            JsonArray members = new JsonArray();
            members.add("REGION.P.out.1");
            members.add("REGION.F.in.2");
            equalityClass.add("members", members);
            context.getAsJsonArray("equalityClasses").add(equalityClass);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(0, result.manifest.getAsJsonArray(
                    "unsupportedExpressions").size());
            JsonObject opaqueKey = result.manifest.getAsJsonArray(
                    "opaqueComputedMapKeys").get(0).getAsJsonObject();
            assertEquals("CONCOLIC_TYPED_METHOD_RESULT_ONE_LOOKUP_KEY_V1",
                    opaqueKey.get("authority").getAsString());
            assertEquals("STRING",
                    opaqueKey.get("boxedKeyKind").getAsString());
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
            assertTrue(result.smtLib.contains("(VMapString "));
            assertTrue(result.smtLib.contains("(map_has "));
            assertFalse(result.smtLib.contains(
                    "uf__java_lang_Integer_parseInt"));
            assertFalse(result.smtLib.contains(
                    "uf__java_lang_String_splitElement"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void lowersCapturedStringContainsPredicatesExactly()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonObject positive = opString("contains", receiver.deepCopy(),
                    conString("needle_with_underscore"));
            JsonObject negative = opString("contains", receiver.deepCopy(),
                    conString("absent"));
            negative.addProperty("_is_not", true);
            JsonArray constraints = new JsonArray();
            constraints.add(positive);
            constraints.add(negative);
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "OpStrExpression.contains"));
            assertTrue(fatalPath, fatalPath.contains("(str.contains "));
            assertTrue(fatalPath, fatalPath.contains(
                    "\"needle_with_underscore\""));
            assertTrue(fatalPath, fatalPath.contains(
                    "(not (str.contains "));
            assertTrue(fatalPath, fatalPath.contains("\"absent\""));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void lowersComposedStringPredicatesAsBooleanLogic()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonArray constraints = new JsonArray();
            constraints.add(binaryCondition(
                    opString("contains", receiver.deepCopy(),
                            conString("ready")),
                    "&&",
                    opString("contains", receiver.deepCopy(),
                            conString("stable"))));
            constraints.add(binaryCondition(
                    opString("contains", receiver.deepCopy(),
                            conString("primary")),
                    "||",
                    opString("contains", receiver.deepCopy(),
                            conString("fallback"))));
            constraints.add(binaryCondition(
                    opString("contains", receiver.deepCopy(),
                            conString("enabled")),
                    "==", constant("Z", "Y_Z_1")));
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(fatalPath, fatalPath.contains(
                    "(and (str.contains "));
            assertTrue(fatalPath, fatalPath.contains(
                    "(or (str.contains "));
            assertTrue(fatalPath, fatalPath.contains(
                    "(= (str.contains "));
            assertTrue(fatalPath, fatalPath.contains(" true)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void lowersCoreStringOperationsWithBothPredicatePolarities()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonArray constraints = new JsonArray();
            constraints.add(opString("equals", receiver.deepCopy(),
                    conString("prefix_tail")));
            constraints.add(negatedOpString("equals", receiver.deepCopy(),
                    conString("other")));
            constraints.add(opString("startsWith", receiver.deepCopy(),
                    conString("prefix")));
            constraints.add(negatedOpString("startsWith",
                    receiver.deepCopy(), conString("tail")));
            constraints.add(opString("endsWith", receiver.deepCopy(),
                    conString("tail")));
            constraints.add(negatedOpString("endsWith",
                    receiver.deepCopy(), conString("prefix")));
            constraints.add(opString("isEmpty", conString("")));
            constraints.add(negatedOpString("isEmpty",
                    receiver.deepCopy()));
            constraints.add(binaryCondition(opString("length",
                    receiver.deepCopy()), "==", constant("I", "Y_I_11")));
            constraints.add(opString("equals",
                    opString("concat", conString("prefix"),
                            conString("_tail")),
                    conString("prefix_tail")));
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(fatalPath, fatalPath.contains("(= sym__"));
            assertTrue(fatalPath,
                    fatalPath.contains("(not (= sym__"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(str.prefixof \"prefix\" sym__"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(not (str.prefixof \"tail\" sym__"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(str.suffixof \"tail\" sym__"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(not (str.suffixof \"prefix\" sym__"));
            assertTrue(fatalPath,
                    fatalPath.contains("(= (str.len \"\") 0)"));
            assertTrue(fatalPath,
                    fatalPath.contains("(not (= (str.len sym__"));
            assertTrue(fatalPath,
                    fatalPath.contains("(= (str.len sym__"));
            assertTrue(fatalPath, fatalPath.contains(") 11)"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(str.++ \"prefix\" \"_tail\")"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void modelsNullableStringPortsAndNullGuardsExactly()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonElement erasedReceiver = symbol("L",
                    "M_L_field_REGION.F.in.2_example/Transport");
            JsonArray constraints = new JsonArray();
            constraints.add(binaryCondition(erasedReceiver, "!=",
                    symbol("", "N")));
            constraints.add(negatedOpString("equals", receiver.deepCopy(),
                    symbol("", "N")));
            constraints.add(opString("contains", receiver.deepCopy(),
                    conString("ready")));
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String companion =
                    "sym__port__REGION_F_in_2__string_is_null";
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(declare-const " + companion + " Bool)"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(ite " + companion + " (VRef nullRef) (VString "
                            + "sym__port__REGION_F_in_2__string))"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(= (= sym__port__REGION_F_in_2__ref nullRef) "
                            + companion + ")"));
            assertFalse(result.smtLib, result.smtLib.contains(
                    "(= port__REGION_F_in_2 "
                            + "(VRef sym__port__REGION_F_in_2__ref))"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(not " + companion + ")"));
            assertTrue(fatalPath, fatalPath.contains("(str.contains "
                    + "sym__port__REGION_F_in_2__string \"ready\")"));
            assertZ3Status(result.smtLib, "sat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void nullableStringShortCircuitAndDereferenceDefinednessMatchJava()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject original = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonElement isNull = binaryCondition(receiver.deepCopy(), "==",
                    symbol("", "N"));
            JsonArray shortCircuitConstraints = new JsonArray();
            shortCircuitConstraints.add(binaryCondition(isNull, "||",
                    opString("contains", receiver.deepCopy(),
                            conString("ready"))));
            for (JsonElement constraint : fatalConstraints(original)) {
                shortCircuitConstraints.add(constraint.deepCopy());
            }
            JsonObject shortCircuit = original.deepCopy();
            setFatalConstraints(shortCircuit, shortCircuitConstraints);
            Files.write(fixture.fatal, (shortCircuit + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result shortCircuitResult =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String companion =
                    "sym__port__REGION_F_in_2__string_is_null";
            String forceNull = shortCircuitResult.smtLib.replace(
                    "(check-sat)", "(assert " + companion
                            + ")\n(check-sat)");
            assertEquals(shortCircuitResult.manifest.toString(), 0,
                    shortCircuitResult.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertZ3Status(forceNull, "sat");

            JsonArray invalidDereferenceConstraints = new JsonArray();
            invalidDereferenceConstraints.add(binaryCondition(
                    receiver.deepCopy(), "==", symbol("", "N")));
            invalidDereferenceConstraints.add(opString("contains",
                    receiver.deepCopy(), conString("ready")));
            for (JsonElement constraint : fatalConstraints(original)) {
                invalidDereferenceConstraints.add(constraint.deepCopy());
            }
            JsonObject invalidDereference = original.deepCopy();
            setFatalConstraints(invalidDereference,
                    invalidDereferenceConstraints);
            Files.write(fixture.fatal, (invalidDereference + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result invalidDereferenceResult =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertZ3Status(invalidDereferenceResult.smtLib, "unsat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void javaStringReferenceEqualityRequiresExactProvenance()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject original = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonArray sameConstraints = new JsonArray();
            sameConstraints.add(binaryCondition(receiver.deepCopy(), "==",
                    receiver.deepCopy()));
            for (JsonElement constraint : fatalConstraints(original)) {
                sameConstraints.add(constraint.deepCopy());
            }
            JsonObject same = original.deepCopy();
            setFatalConstraints(same, sameConstraints);
            Files.write(fixture.fatal, (same + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result sameResult =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertEquals(sameResult.manifest.toString(), 0,
                    sameResult.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());

            JsonArray distinctConstraints = new JsonArray();
            distinctConstraints.add(binaryCondition(receiver.deepCopy(),
                    "==", symbol("java/lang/String",
                            "M_L'String'_distinct_reference")));
            for (JsonElement constraint : fatalConstraints(original)) {
                distinctConstraints.add(constraint.deepCopy());
            }
            JsonObject distinct = original.deepCopy();
            setFatalConstraints(distinct, distinctConstraints);
            Files.write(fixture.fatal, (distinct + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result distinctResult =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertFalse(candidateReady(distinctResult.manifest));
            assertTrue(distinctResult.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString(),
                    distinctResult.manifest.getAsJsonArray(
                            "unsupportedExpressions").toString().contains(
                            "MODEL_SEMANTICS_MISSING:"
                                    + "JAVA_STRING_REFERENCE_IDENTITY:=="));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void inexactStringVariantsAndNonStringOperandsFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonElement receiver = symbol("java/lang/String",
                    "M_L'String'_REGION.F.in.2_example/Transport");
            JsonArray constraints = new JsonArray();
            constraints.add(opString("startsWith", receiver.deepCopy(),
                    conString("prefix"), constant("I", "Y_I_1")));
            constraints.add(opString("equalsIgnoreCase",
                    receiver.deepCopy(), conString("PREFIX_TAIL")));
            constraints.add(opString("matches", receiver.deepCopy(),
                    conString("prefix.*")));
            constraints.add(opString("equals", symbol("I",
                    "M_I_non_string_parameter"), conString("1")));
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String unsupported = result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString();

            assertFalse(candidateReady(result.manifest));
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:"
                            + "OpStrExpression.startsWith:ARITY"));
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:"
                            + "OpStrExpression.equalsIgnoreCase:"
                            + "UNSUPPORTED_OPERATION"));
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:OpStrExpression.matches:"
                            + "UNSUPPORTED_OPERATION"));
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:OpStrExpression.equals:"
                            + "NON_STRING_PARAMETER"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void normalizesVmExponentAndLongMinLiteralsWithoutRounding()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(binaryCondition(
                    constant("J", "Y_J_-9223372036854775808"), "==",
                    constant("J", "Y_J_-9223372036854775808")));
            constraints.add(binaryCondition(
                    constant("F", "Y_F_1.250000000e-03"), "<",
                    constant("D", "Y_D_1.25000000000000000e+02")));
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(fatalPath,
                    fatalPath.contains("(- 9223372036854775808)"));
            assertTrue(fatalPath, fatalPath.contains(
                    "((_ to_fp 8 24) #x3aa3d70a)"));
            assertTrue(fatalPath, fatalPath.contains(
                    "((_ to_fp 11 53) #x405f400000000000)"));
            assertTrue(fatalPath, fatalPath.contains(
                    "((_ to_fp 11 53) RNE ((_ to_fp 8 24)"));
            assertFalse(fatalPath, fatalPath.contains("e-03"));
            assertFalse(fatalPath, fatalPath.contains("e+02"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void nonFiniteVmFloatingLiteralsRetainExactIeeeSemantics()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            JsonArray constraints = new JsonArray();
            constraints.add(binaryCondition(constant("D", "Y_D_nan"),
                    "==", constant("D", "Y_D_0.0")));
            constraints.add(binaryCondition(constant("F", "Y_F_inf"),
                    "==", constant("F", "Y_F_0.0")));
            constraints.add(binaryCondition(constant("D", "Y_D_-0.0"),
                    "==", constant("D", "Y_D_0.0")));
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(result.smtLib, result.smtLib.contains(
                    "#x7ff8000000000000"));
            assertTrue(result.smtLib, result.smtLib.contains("#x7f800000"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "#x8000000000000000"));
            assertTrue(result.smtLib, result.smtLib.contains("(fp.eq "));
            assertZ3Status(result.smtLib, "unsat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void jvmCompareResultsPreserveNanVariantAndLongTrichotomy()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            prependFatalConstraints(fixture,
                    binaryCondition(binaryCondition(
                            constant("D", "Y_D_nan"), "--l",
                            constant("D", "Y_D_0.0")), "==",
                            constant("I", "Y_I_-1")),
                    binaryCondition(binaryCondition(
                            constant("D", "Y_D_nan"), "--g",
                            constant("D", "Y_D_0.0")), "==",
                            constant("I", "Y_I_1")),
                    binaryCondition(binaryCondition(
                            constant("J", "Y_J_1"), "--",
                            constant("J", "Y_J_2")), "==",
                            constant("I", "Y_I_-1")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(ite (or (fp.isNaN "));
            assertTrue(result.smtLib, result.smtLib.contains(
                    ") (- 1) (ite (fp.lt "));
            assertTrue(result.smtLib, result.smtLib.contains(
                    ") 1 (ite (fp.lt "));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(ite (< 1 2) (- 1) (ite (> 1 2) 1 0))"));
            assertZ3Status(result.smtLib, "sat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void canonicalPortFloatDoubleConflictsFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8",
                            "<example.Signal: float value>"));
            prependFatalConstraints(fixture, binaryCondition(
                    symbol("D", "M_D_field_REGION.F.in.8_example/Signal"),
                    "==", constant("D", "Y_D_0.0")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String unsupported = result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString();

            assertFalse(result.manifest.toString(), candidateReady(result.manifest));
            assertTrue(unsupported, unsupported.contains(
                    "CanonicalPortFloatingSortConflict:REGION.F.in.8:"));
            assertTrue(unsupported, unsupported.contains(
                    "CanonicalPortFloatingTypeConflict:REGION.F.in.8:"));
            assertZ3Parses(result.smtLib);
        } finally {
            folder.delete();
        }
    }

    @Test
    public void exactWideningRealDivisionAndUnaryNegationRemainComplete()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            prependFatalConstraints(fixture,
                    binaryCondition(cast(constant("B", "Y_B_7"), "I"),
                            "==", constant("I", "Y_I_7")),
                    binaryCondition(cast(constant("I", "Y_I_7"), "L"),
                            "==", constant("J", "Y_J_7")),
                    binaryCondition(binaryCondition(
                            constant("D", "Y_D_-7.5"), "@",
                            constant("D", "Y_D_2.5")), "==",
                            constant("D", "Y_D_-3.0")),
                    binaryCondition(unaryNegation(
                            constant("I", "Y_I_4")), "==",
                            constant("I", "Y_I_-4")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(fatalPath, fatalPath.contains("(fp.div RNE "));
            assertTrue(fatalPath, fatalPath.contains("(- 4)"));
            assertFalse(fatalPath, fatalPath.contains("(div "));
            assertFalse(fatalPath, fatalPath.contains("(mod "));
            assertZ3Parses(result.smtLib);
        } finally {
            folder.delete();
        }
    }

    @Test
    public void primitiveCastsPreserveJavaBoundarySemanticsInComposition()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            prependFatalConstraints(fixture,
                    binaryCondition(explicitCast(
                            constant("J", "Y_J_4294967297"), "J", "I"),
                            "==", constant("I", "Y_I_1")),
                    binaryCondition(explicitCast(
                            constant("I", "Y_I_257"), "I", "B"),
                            "==", constant("B", "Y_B_1")),
                    binaryCondition(explicitCast(
                            constant("I", "Y_I_65535"), "I", "S"),
                            "==", constant("S", "Y_S_-1")),
                    binaryCondition(explicitCast(
                            constant("I", "Y_I_-1"), "I", "C"),
                            "==", constant("C", "Y_C_65535")),
                    binaryCondition(explicitCast(
                            constant("I", "Y_I_-1"), "I", "J"),
                            "==", constant("J", "Y_J_-1")),
                    binaryCondition(explicitCast(
                            constant("J", "Y_J_4294967297"), "J", "D"),
                            "==", constant("D", "Y_D_4294967297.0")),
                    binaryCondition(explicitCast(
                            constant("F", "Y_F_1.5"), "F", "D"),
                            "==", constant("D", "Y_D_1.5")),
                    binaryCondition(explicitCast(
                            constant("D", "Y_D_1.5"), "D", "F"),
                            "==", constant("F", "Y_F_1.5")),
                    binaryCondition(explicitCast(
                            constant("D", "Y_D_NaN"), "D", "I"),
                            "==", constant("I", "Y_I_0")),
                    binaryCondition(explicitCast(
                            constant("D", "Y_D_Infinity"), "D", "I"),
                            "==", constant("I", "Y_I_2147483647")),
                    binaryCondition(explicitCast(
                            constant("D", "Y_D_-Infinity"), "D", "I"),
                            "==", constant("I", "Y_I_-2147483648")),
                    binaryCondition(explicitCast(
                            constant("D", "Y_D_-2.9"), "D", "I"),
                            "==", constant("I", "Y_I_-2")),
                    binaryCondition(explicitCast(
                            constant("F", "Y_F_Infinity"), "F", "J"),
                            "==", constant("J",
                                    "Y_J_9223372036854775807")),
                    // Old captures carry only _java_type; retain that path.
                    binaryCondition(cast(constant("I", "Y_I_257"), "B"),
                            "==", constant("B", "Y_B_1")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(java_int_wrap 4294967297)"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(fp.isNaN "));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "((_ fp.to_sbv 32) RTZ "));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "((_ fp.to_sbv 64) RTZ "));
            assertZ3Status(result.smtLib, "sat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composedIntAndLongArithmeticWrapsAtJavaWidths()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject intInput = symbol("I",
                    "M_I_field_REGION.F.in.1_example/Request");
            JsonObject longInput = symbol("J",
                    "M_J_field_REGION.F.in.4_example/Clock");
            prependFatalConstraints(fixture,
                    binaryCondition(binaryCondition(
                            constant("I", "Y_I_10"), "+",
                            intInput.deepCopy()), "<",
                            constant("I", "Y_I_0")),
                    binaryCondition(longInput.deepCopy(), "==",
                            constant("J", "Y_J_9223372036854775807")),
                    binaryCondition(binaryCondition(longInput.deepCopy(),
                            "+", constant("J", "Y_J_1")), "==",
                            constant("J", "Y_J_-9223372036854775808")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String fatalPath = lineContaining(result.smtLib,
                    ":named fatal_path");

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(result.manifest.toString(), 0,
                    result.manifest.getAsJsonArray(
                            "unsupportedExpressions").size());
            assertTrue(fatalPath, fatalPath.contains(
                    "(java_int_wrap (+ 10 sym__port__REGION_F_in_1__int))"));
            assertTrue(fatalPath, fatalPath.contains(
                    "(java_long_wrap (+ sym__port__REGION_F_in_4__int 1))"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    ":named java_integral_domain_"));
            assertZ3Status(result.smtLib, "sat");
        } finally {
            folder.delete();
        }
    }

    @Test
    public void unknownMethodsCastsAndNonNumericOperatorsFailClosed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            prependFatalConstraints(fixture,
                    method("example/Codec mystery",
                            constant("I", "Y_I_0"),
                            constant("I", "Y_I_1")),
                    method("example/Codec mystery", conString("result"),
                            conString("argument")),
                    binaryCondition(cast(constant("I", "Y_I_257"), "B"),
                            "==", constant("I", "Y_I_1")),
                    binaryCondition(cast(constant("I", "Y_I_1"), "D"),
                            "==", constant("D", "Y_D_1.0")),
                    binaryCondition(cast(conString("payload"),
                            "Ljava/lang/Object;"), "==",
                            symbol("Ljava/lang/Object;", "N")),
                    binaryCondition(conString("a"), "<", conString("b")),
                    binaryCondition(binaryCondition(conString("a"), "+",
                            conString("b")), "==", conString("ab")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String unsupported = result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString();

            assertFalse(candidateReady(result.manifest));
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:MethodExpression:"
                            + "example/Codec mystery"));
            assertFalse(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:TypeCastExpression:I->B"));
            assertFalse(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:TypeCastExpression:I->D"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "((_ to_fp 11 53) RNE (to_real 1))"));
            assertTrue(unsupported, unsupported.contains(
                    "MODEL_SEMANTICS_MISSING:TypeCastExpression:"
                            + "java/lang/String->Ljava/lang/Object;"));
            assertTrue(unsupported, unsupported.contains(
                    "NonNumericComparison:<:STRING"));
            assertTrue(unsupported, unsupported.contains(
                    "NonNumericArithmetic:+:STRING"));
            assertTrue(result.smtLib, result.smtLib.contains(
                    "(declare-fun uf__example_Codec_mystery"));
            assertZ3Parses(result.smtLib);
        } finally {
            folder.delete();
        }
    }

    @Test
    public void javaIntegralDivisionAndRemainderNeverUseSmtEuclideanOps()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            prependFatalConstraints(fixture,
                    binaryCondition(binaryCondition(
                            constant("I", "Y_I_-7"), "@",
                            constant("I", "Y_I_2")), "==",
                            constant("I", "Y_I_-3")),
                    binaryCondition(binaryCondition(
                            constant("I", "Y_I_-7"), "%",
                            constant("I", "Y_I_2")), "==",
                            constant("I", "Y_I_-1")));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String unsupported = result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString();

            assertFalse(candidateReady(result.manifest));
            assertTrue(unsupported, unsupported.contains(
                    "JavaIntegralDivisionUnmodeled"));
            assertTrue(unsupported, unsupported.contains(
                    "JavaIntegralRemainderUnmodeled"));
            assertFalse(result.smtLib, result.smtLib.contains("(div "));
            assertFalse(result.smtLib, result.smtLib.contains(
                    "(mod (- 7) 2)"));
            assertZ3Parses(result.smtLib);
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
            for (JsonElement constraint : fatalConstraints(fatal)) {
                constraints.add(constraint);
            }
            setFatalConstraints(fatal, constraints);
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));
            String unsupported = result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString();

            assertFalse(candidateReady(result.manifest));
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
    public void canonicalFatalContractIsTheOnlyBranchAuthority()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(fixture.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            BranchReplayContract contract = BranchReplayContract.fromJson(
                    fatal.getAsJsonObject("replayContract"));
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(contract.sameContent(BranchReplayContract.fromJson(
                    fatal.getAsJsonObject("replayContract"))));
            assertFalse(result.manifest.has("fatalSolverPathContextId"));
            assertEquals("F#u2", result.manifest.get(
                    "fatalSite").getAsString());
            assertEquals(1, result.manifest.get(
                    "fatalOccurrence").getAsInt());
            assertTrue(result.manifest.get(
                    "fatalDesiredOutcome").getAsBoolean());
            assertFalse(result.manifest.has("validatedSummaryId"));
            assertFalse(result.manifest.has(
                    "validatedFatalReplaySummary"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void rejectsRetiredFatalReplayAliases() throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            for (String alias : new String[]{"targetReplayValidated",
                    "replayAlreadyValidated", "validatedTargetSummary"}) {
                Fixture fixture = fixture(folder.newFolder(alias).toPath(),
                        true);
                JsonObject fatal = JsonParser.parseString(new String(
                        Files.readAllBytes(fixture.fatal),
                        StandardCharsets.UTF_8).trim()).getAsJsonObject();
                if ("validatedTargetSummary".equals(alias)) {
                    fatal.add(alias, new JsonObject());
                } else {
                    fatal.addProperty(alias, true);
                }
                Files.write(fixture.fatal, (fatal + "\n").getBytes(
                        StandardCharsets.UTF_8));
                assertFatalQueryRejected(fixture,
                        "rejects retired branch alias: " + alias);
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void requiresCanonicalFatalContractAndSolverContext()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture missingContract = fixture(folder.newFolder(
                    "missing-contract").toPath(), true);
            JsonObject fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(missingContract.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.remove("replayContract");
            Files.write(missingContract.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));
            assertFatalQueryRejected(missingContract,
                    "requires replayContract");

            Fixture missingContext = fixture(folder.newFolder(
                    "missing-context").toPath(), true);
            fatal = JsonParser.parseString(new String(
                    Files.readAllBytes(missingContext.fatal),
                    StandardCharsets.UTF_8).trim()).getAsJsonObject();
            fatal.remove("solverPathContext");
            Files.write(missingContext.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));
            assertFatalQueryRejected(missingContext,
                    "requires solverPathContext");
        } finally {
            folder.delete();
        }
    }

    private static void assertFatalQueryRejected(Fixture fixture,
                                                 String message)
            throws Exception {
        try {
            ConcolicSmtComposer.compose(arguments(fixture));
            throw new AssertionError("expected fatal query rejection");
        } catch (java.io.IOException expected) {
            assertTrue(expected.getMessage(), expected.getMessage()
                    .contains(message));
        }
    }
    @Test
    public void composesAndSolvesVersionedJavaMapMutationChain()
            throws Exception {
        Assume.assumeTrue(z3Available());
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            writeSummary(fixture, producerSummary(mutationChain(), true));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(candidateReady(result.manifest));
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
            assertZ3Status(result.smtLib, "sat");
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
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(positive, nonPositive),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(candidateReady(result.manifest));
            assertTrue(result.smtLib.contains(
                    "region_case_selector_coverage_REGION_P"));
            assertTrue(result.smtLib.contains(
                    "region_case_selector_exclusive_REGION_P_0_1"));
            assertTrue(result.smtLib.contains("(=>"));
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            assertEquals(2, catalog.size());
            for (com.google.gson.JsonElement element : catalog) {
                JsonObject pathCase = element.getAsJsonObject();
                assertEquals(3, pathCase.size());
                assertFalse(pathCase.get("caseId").getAsString().isEmpty());
                String selector = pathCase.get(
                        "selectorTerm").getAsString();
                assertTrue(result.smtLib.contains(
                        "(declare-const " + selector + " Bool)"));
                assertTrue(result.smtLib.contains("(= " + selector + " "));
                JsonObject mapping = bindingForPort(pathCase,
                        "REGION.P.in.2");
                assertEquals("sym__port__REGION_P_in_2__int",
                        mapping.get("term").getAsString());
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void contextualBooleanLiteralIsNotAProjectionRoot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.add("captureGoal",
                    RegionCaptureGoal.outputClosure().toJson());
            summary.add("requestedOutput",
                    requestedOutput("REGION.P.out.0"));

            JsonArray conditions = summary.getAsJsonArray("pathCondition");
            conditions.add(binaryCondition(
                    symbol("I", "M_I_field_REGION.P.in.2_example/Cache"),
                    "==", constant("Z", "Y_Z_0")));
            conditions.add(binaryCondition(
                    opString("contains", conString("rpc-ready"),
                            conString("ready")),
                    "!=", constant("Z", "Y_Z_0")));

            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Collections.singletonList(summary),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            JsonObject projection = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog").get(0).getAsJsonObject();
            assertEquals(3, projection.size());
            assertFalse(projection.getAsJsonArray("bindings")
                    .toString().contains("Y_Z_0"));
            assertTrue(result.smtLib.contains(
                    "sym__port__REGION_P_in_2__int 0"));
            assertTrue(result.smtLib.contains("(str.contains "));
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
                JsonObject mapping = bindingForPort(
                        element.getAsJsonObject(), "REGION.P.in.4");
                assertEquals("REGION.P.in.4",
                        mapping.get("portId").getAsString());
                assertFalse(mapping.get("term").getAsString().isEmpty());
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
            assertFalse(candidateReady(missingResult.manifest));
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
            assertFalse(candidateReady(malformedResult.manifest));
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
            assertFalse(candidateReady(storeResult.manifest));
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
            JsonArray constraints = fatalConstraints(fatal);
            constraints.add(arrayLoad("VM_FATAL_ARRAY", "VM_FATAL_VALUE"));
            setFatalConstraints(fatal, constraints);
            fatal.add("engineArrayInputBindings", singleton(
                    engineArrayInputBinding("ACT.F", "REGION.F.in.8",
                            cell, "[I", "VM_FATAL_ARRAY", 81,
                            constant("I", "Y_I_5"))));
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
            JsonArray constraints = fatalConstraints(fatal);
            constraints.add(arrayLoad("VM_FATAL_LENGTH_ONE",
                    "VM_FATAL_VALUE"));
            setFatalConstraints(fatal, constraints);
            fatal.add("engineArrayInputBindings", singleton(
                    engineArrayInputBinding("ACT.F", "REGION.F.in.8",
                            consumerCell, "[I", "VM_FATAL_LENGTH_ONE", 82,
                            constant("I", "Y_I_5"))));
            Files.write(fixture.fatal, (fatal + "\n").getBytes(
                    StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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

            assertTrue(candidateReady(result.manifest));
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
            String removeObservation = lineContaining(result.smtLib,
                    ":named heap_observation_key_present_OBS_REMOVE");
            String noRemoveObservation = lineContaining(result.smtLib,
                    ":named heap_observation_key_present_OBS_NO_REMOVE");
            String removeSelector = selectorInLine(catalog,
                    removeObservation);
            String noRemoveSelector = selectorInLine(catalog,
                    noRemoveObservation);
            assertTrue(removeObservation.contains("(=> " + removeSelector));
            assertTrue(noRemoveObservation.contains(
                    "(=> " + noRemoveSelector));
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
                    candidateReady(result.manifest));
            JsonArray catalog = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog");
            JsonObject removeProjection = null;
            JsonObject noRemoveProjection = null;
            for (JsonElement element : catalog) {
                JsonObject projection = element.getAsJsonObject();
                JsonObject binding = bindingForPort(projection,
                        "REGION.P.in.3");
                String selector = projection.get(
                        "selectorTerm").getAsString();
                String term = binding.get("term").getAsString();
                if (result.smtLib.contains("(= " + selector
                        + " (> " + term + " 0))")) {
                    removeProjection = projection;
                } else if (result.smtLib.contains("(= " + selector
                        + " (<= " + term + " 0))")) {
                    noRemoveProjection = projection;
                }
            }
            assertNotNull(removeProjection);
            assertNotNull(noRemoveProjection);
            JsonObject removeMapping = bindingForPort(removeProjection,
                    "REGION.P.in.3");
            JsonObject noRemoveMapping = bindingForPort(noRemoveProjection,
                    "REGION.P.in.3");
            String removeTerm = removeMapping.get("term").getAsString();
            String noRemoveTerm = noRemoveMapping.get("term").getAsString();

            assertEquals(3, removeProjection.size());
            assertEquals("REGION.P.in.3",
                    removeMapping.get("portId").getAsString());
            String assertionName = removeMapping.get(
                    "bridgeAssertionName").getAsString();
            assertEquals(1, linesContaining(result.smtLib,
                    ":named " + assertionName).size());
            assertFalse(removeTerm.equals(noRemoveTerm));
            assertFalse(removeTerm.contains("port__REGION_P_in_3"));
            assertTrue(result.smtLib.contains("(= "
                    + removeProjection.get("selectorTerm").getAsString()
                    + " (> " + removeTerm + " 0))"));
            assertTrue(result.smtLib.contains("(= "
                    + noRemoveProjection.get(
                    "selectorTerm").getAsString()
                    + " (<= " + noRemoveTerm + " 0))"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void twoDynamicMapEntriesWithOneBaseCannotBecomeOneRoot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String first = "REGION.P.in.3.field.firstentry.occ.1";
            String second = "REGION.P.in.3.field.secondentry.occ.2";
            JsonObject summary = producerSummary(singlePutEffect(), true);
            prepareDynamicOutputCase(summary, ">", "OBS.ENTRY.FIRST",
                    "entry_value_first", first);
            summary.getAsJsonArray("dynamicFieldBindings").add(
                    runtimeDynamicFieldBinding("OBS.ENTRY.SECOND", second,
                            "ACT.P"));
            summary.getAsJsonArray("heapObservations").add(
                    dynamicHeapObservation("OBS.ENTRY.SECOND",
                            "entry_value_second", second));
            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Collections.singletonList(summary),
                    closedPathManifest());
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(result.manifest.toString(), candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "AMBIGUOUS_DYNAMIC_BASE_ROOT:REGION.P.in.3:2"));
            JsonObject projection = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog").get(0).getAsJsonObject();
            assertEquals(0, projection.getAsJsonArray("bindings").size());
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            JsonObject projection = result.manifest.getAsJsonArray(
                    "caseProjectionCatalog").get(0).getAsJsonObject();
            JsonObject mapping = bindingForPort(projection,
                    "REGION.P.in.3");
            assertEquals("REGION.P.in.3", mapping.get(
                    "portId").getAsString());
            assertFalse(mapping.get("term").getAsString().isEmpty());
            assertEquals(1, linesContaining(result.smtLib,
                    ":named " + mapping.get(
                            "bridgeAssertionName").getAsString()).size());
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
                            candidateReady(result.manifest));
                    assertTrue(result.manifest.toString(),
                            result.manifest.toString().contains(
                                    "MAP_PROJECTION"));
                    continue;
                }
                assertTrue(result.manifest.toString(),
                        candidateReady(result.manifest));
                assertTrue(result.smtLib.contains(
                        "(forall ((q Value)) (= (map_has "));
                assertTrue(result.smtLib.contains(
                        "finite_array_length port__REGION_P_out_2"));
                assertTrue(result.smtLib.contains(
                        "exact_field__"));
                assertTrue(result.smtLib.contains("(map_select "));
                assertTrue(result.smtLib.contains("(VMapInteger 11)"));
                JsonObject projection = result.manifest.getAsJsonArray(
                        "caseProjectionCatalog").get(0).getAsJsonObject();
                assertEquals(3, projection.size());
                assertTrue(projection.get("bindings").isJsonArray());

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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
                        candidateReady(result.manifest));
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
                    JsonArray constraints = fatalConstraints(fatal);
                    constraints.get(0)
                            .getAsJsonObject().getAsJsonArray("_param_list")
                            .set(1, constant("example/CustomKey",
                                    "Y_L_custom"));
                    setFatalConstraints(fatal, constraints);
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
                        candidateReady(result.manifest));
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
            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
                        candidateReady(result.manifest));
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

        JsonObject deep = valid.deepCopy();
        JsonArray deepPath = new JsonArray();
        deepPath.add("state");
        deepPath.add("guard");
        deepPath.add("enabled");
        deep.add("fieldPath", deepPath);
        deep.addProperty("leafOwnerObjectToken", 303L);
        deep.addProperty("actualHookSiteId",
                "CONTAINER_SNAPSHOT:BIND.ARRAY.1");
        deep.addProperty("actualHookOccurrence", 1);
        deep.addProperty("effectiveMaterializationSiteId",
                "SITE.CONTAINER");
        deep.addProperty("effectiveMaterializationOccurrence", 1);
        deep.addProperty("materializationSiteBridgeAuthority",
                "STATIC_CONTAINER_SELECTOR_AND_ACTIVATION_LOCAL_EXACT_"
                        + "ELEMENT_IDENTITY_TO_DECLARED_FIELD_HOOK_V1");
        deep.addProperty("materializationSiteBridgeBindingId",
                "BIND.ARRAY.1");
        deep.addProperty("materializationSiteBridgeElementObjectToken",
                302L);
        deep.addProperty("materializationSiteBridgeObjectTokenScope",
                "ACT.P");
        assertTrue(ConcolicSmtComposer.completeContainerSelectorForTests(
                deep));
        JsonObject metadata = ConcolicSmtComposer
                .projectionDynamicMetadataForTests(deep);
        assertEquals(deep, metadata.getAsJsonObject("runtimeBinding"));
        for (String member : new String[]{
                "resolvedFromSelectorAuthority", "actualHookSiteId",
                "actualHookOccurrence", "effectiveMaterializationSiteId",
                "effectiveMaterializationOccurrence",
                "materializationSiteBridgeAuthority",
                "materializationSiteBridgeBindingId",
                "materializationSiteBridgeElementObjectToken",
                "materializationSiteBridgeObjectTokenScope"}) {
            assertEquals(member, deep.get(member), metadata.get(member));
        }
        deep.addProperty("materializationSiteBridgeElementObjectToken",
                304L);
        assertFalse(ConcolicSmtComposer.completeContainerSelectorForTests(
                deep));
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

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
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

            assertFalse(result.manifest.toString(), candidateReady(result.manifest));
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
                    candidateReady(result.manifest));
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
    public void composesNonMutatingMapReadFromSyntheticObservationState()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.9",
                            "<example.Value: boolean enabled>"));
            JsonObject summary = producerSummary(new JsonArray(), true);
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("L", "producer_map_state"));
            String dynamic =
                    "REGION.P.in.9.field.nonmutating.occ.1";
            JsonObject observation = nonMutatingDynamicHeapObservation(
                    "OBS.NON_MUTATING", "entry_value_non_mutating",
                    dynamic, "REGION.P.in.9");
            summary.add("heapObservations", singleton(observation));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            String statePort = observation.get("statePort").getAsString();
            String digestPrefix = statePort.substring(
                    statePort.lastIndexOf('.') + 1);
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString(),
                    candidateReady(result.manifest));
            assertTrue(lineContaining(result.smtLib, digestPrefix)
                    .contains("MapState"));
            String keyPresent = lineContaining(result.smtLib,
                    ":named heap_observation_key_present_OBS_NON_MUTATING");
            assertTrue(keyPresent.contains(digestPrefix));
            assertFalse(keyPresent.contains("port__REGION_P_in_9"));
            assertTrue(lineContaining(result.smtLib,
                    ":named heap_observation_value_OBS_NON_MUTATING")
                    .contains(digestPrefix));
            assertTrue(lineContaining(result.smtLib,
                    ":named heap_observation_field_OBS_NON_MUTATING_0")
                    .contains("dynamic_field"));
            assertFalse(result.smtLib.contains(
                    "(declare-const port__REGION_P_in_9 MapState)"));
            for (String line : linesContaining(result.smtLib,
                    digestPrefix)) {
                assertFalse(line, line.contains("emptyMapState"));
            }
        } finally {
            folder.delete();
        }
    }

    @Test
    public void mergedCasesUseSourceActivationForObservationStateProof()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            String observationId = "OBS.MERGED.NON_MUTATING";
            String dynamic =
                    "REGION.P.in.3.field.mergednonmutating.occ.1";

            JsonObject positive = producerSummary(new JsonArray(), true);
            prepareDynamicOutputCase(positive, ">", observationId,
                    "entry_value_merged_non_mutating", dynamic);
            positive.add("heapObservations", singleton(
                    nonMutatingDynamicHeapObservation(observationId,
                            "entry_value_merged_non_mutating", dynamic)));
            positive.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("L", "producer_map_state"));

            JsonObject negative = producerSummary(new JsonArray(), true);
            negative.addProperty("summaryId",
                    "SUMMARY.P.NON_MUTATING.NEGATIVE");
            prepareDynamicOutputCase(negative, "<=", observationId,
                    "entry_value_merged_non_mutating", dynamic);
            negative.add("heapObservations", singleton(
                    nonMutatingDynamicHeapObservation(observationId,
                            "entry_value_merged_non_mutating", dynamic)));
            negative.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("L", "producer_map_state"));

            RegionSummaryMerger.Result merged = RegionSummaryMerger.merge(
                    java.util.Arrays.asList(positive, negative),
                    closedPathManifest());
            JsonArray cases = merged.summaries.get(0).getAsJsonObject(
                    "regionRelation").getAsJsonArray("cases");
            assertEquals(2, cases.size());
            for (JsonElement element : cases) {
                JsonObject item = element.getAsJsonObject();
                assertFalse(item.has("activationId"));
                assertEquals("ACT.P",
                        item.get("sourceActivationId").getAsString());
            }
            writeSummary(fixture, merged.summaries.get(0));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            String statePort = cases.get(0).getAsJsonObject()
                    .getAsJsonArray("heapObservations").get(0)
                    .getAsJsonObject().get("statePort").getAsString();
            String digestPrefix = statePort.substring(
                    statePort.lastIndexOf('.') + 1);
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString(),
                    candidateReady(result.manifest));
            assertEquals(2, countDeclarationLines(result.smtLib,
                    digestPrefix));
            assertEquals(2, linesContaining(result.smtLib,
                    ":named heap_observation_key_present_"
                            + "OBS_MERGED_NON_MUTATING").size());
        } finally {
            folder.delete();
        }
    }

    @Test
    public void canonicalDynamicFieldBaseCannotMasqueradeAsMapReadState()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.9",
                            "<example.Value: boolean enabled>"));
            JsonObject summary = producerSummary(new JsonArray(), true);
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("L", "producer_map_state"));
            JsonObject observation = nonMutatingDynamicHeapObservation(
                    "OBS.CANONICAL.BASE", "entry_value_bad_base",
                    "REGION.P.in.9.field.badbase.occ.1",
                    "REGION.P.in.9");
            observation.addProperty("statePort", "REGION.P.in.9");
            observation.getAsJsonObject("stateBaseProof").addProperty(
                    "statePort", "REGION.P.in.9");
            summary.add("heapObservations", singleton(observation));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "InvalidOrAmbiguousHeapObservationStateBase"));
            assertFalse(result.smtLib.contains(
                    "heap_observation_key_present_OBS_CANONICAL_BASE"));
            assertFalse(result.smtLib.contains(
                    "(declare-const port__REGION_P_in_9 MapState)"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void emptyMapInitializerCannotAuthenticateObservationStateBase()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonArray initializers = new JsonArray();
            initializers.add(emptyMapInitializer());
            JsonObject summary = producerSummary(new JsonArray(),
                    initializers, true);
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("L", "producer_map_state"));
            JsonObject observation = nonMutatingDynamicHeapObservation(
                    "OBS.EMPTY.INIT", "entry_value_empty_init",
                    "REGION.P.in.3.field.emptyinit.occ.1");
            summary.add("heapObservations", singleton(observation));
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "InvalidOrAmbiguousHeapObservationStateBase"));
            assertFalse(result.smtLib.contains(
                    "heap_observation_key_present_OBS_EMPTY_INIT"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void duplicateSyntheticObservationStateProofsFailClosed()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = producerSummary(new JsonArray(), true);
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("L", "producer_map_state"));
            JsonObject first = nonMutatingDynamicHeapObservation(
                    "OBS.PROOF.1", "entry_value_proof_1",
                    "REGION.P.in.3.field.proof.occ.1");
            JsonObject second = nonMutatingDynamicHeapObservation(
                    "OBS.PROOF.2", "entry_value_proof_2",
                    "REGION.P.in.3.field.proof.occ.2");
            String duplicatedPort = first.get("statePort").getAsString();
            String duplicatedDigest = first.getAsJsonObject(
                    "stateBaseProof").get("selectorDigest").getAsString();
            second.addProperty("statePort", duplicatedPort);
            second.getAsJsonObject("stateBaseProof").addProperty(
                    "statePort", duplicatedPort);
            second.getAsJsonObject("stateBaseProof").addProperty(
                    "selectorDigest", duplicatedDigest);
            JsonArray observations = new JsonArray();
            observations.add(first);
            observations.add(second);
            summary.add("heapObservations", observations);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "InvalidOrAmbiguousHeapObservationStateBase"));
            assertFalse(result.smtLib.contains(
                    "heap_observation_key_present_OBS_PROOF_1"));
            assertFalse(result.smtLib.contains(
                    "heap_observation_key_present_OBS_PROOF_2"));
            assertFalse(result.smtLib.contains(duplicatedPort.replace('.',
                    '_') + " MapState"));
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

            assertFalse(candidateReady(result.manifest));
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
    public void incompleteRelationalSummaryIsAnExplicitCompositionGap()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            writeSummary(fixture, producerSummary(singlePutEffect(), false));

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertFalse(candidateReady(result.manifest));
            assertTrue(result.manifest.getAsJsonArray(
                    "incompleteSummaryRegions").toString()
                    .contains("REGION.P"));
            assertTrue(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString()
                    .contains("IncompleteRelationalSummary@REGION.P"));

            JsonObject outputOnly = producerSummary(new JsonArray(), true);
            outputOnly.addProperty("relationallyComplete", false);
            outputOnly.add("requestedOutput",
                    requestedOutput("REGION.P.out.0"));
            outputOnly.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.0", symbol("java/util/Map",
                            "M_L_field_REGION.P.in.0_example/Store"));
            outputOnly.addProperty("requestedOutputCaptureComplete", true);
            JsonObject slice = requestedSlice("REGION.P.in.0");
            slice.addProperty("outputPort", "REGION.P.out.0");
            slice.addProperty("complete", false);
            slice.addProperty("structuralComplete", true);
            outputOnly.add("requestedOutputSlice", slice);
            JsonObject capture = new JsonObject();
            capture.addProperty("outputPort", "REGION.P.out.0");
            JsonArray captures = new JsonArray();
            captures.add(capture);
            outputOnly.add("requestedOutputCapture", captures);
            writeSummary(fixture, outputOnly);

            ConcolicSmtComposer.Result rejected =
                    ConcolicSmtComposer.compose(arguments(fixture));
            assertFalse(rejected.manifest.toString(), candidateReady(rejected.manifest));
            assertTrue(rejected.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "IncompleteRelationalSummary@REGION.P"));
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

            assertFalse(candidateReady(result.manifest));
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

            assertTrue(candidateReady(result.manifest));
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

            assertFalse(candidateReady(result.manifest));
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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

            assertFalse(candidateReady(result.manifest));
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
            assertFalse(candidateReady(arrayToScalar.manifest));
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
            assertFalse(candidateReady(scalarToArray.manifest));
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

            assertFalse(candidateReady(result.manifest));
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
    public void containerFieldExpressionIdentityIgnoresJsonMemberOrder()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            JsonObject summary = containerFieldSummary(fixture,
                    "DISCOVER_UNIQUE_IDENTITY_INDEX", -1, -1, true);
            JsonObject runtime = summary.getAsJsonArray(
                    "dynamicFieldBindings").get(0).getAsJsonObject();
            JsonObject original = runtime.getAsJsonObject(
                    "fieldExpression");
            JsonObject reordered = new JsonObject();
            reordered.add("_exp", original.get("_exp").deepCopy());
            reordered.add("_type", original.get("_type").deepCopy());
            reordered.add("_java_type",
                    original.get("_java_type").deepCopy());
            runtime.add("fieldExpression", reordered);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "DYNAMIC_FIELD_EXPRESSION_AMBIGUOUS"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void deepContainerSnapshotProjectsPrimitiveLeafFromArrayRoot()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), true);
            addRegionPort(fixture, "REGION.P", "symbolicInputs",
                    port("REGION.P.in.9",
                            "<example.Guard: boolean enabled>"));
            JsonObject summary = containerFieldSummary(fixture,
                    "EXACT_ARRAY_INDEX", 1, 1, false);
            JsonObject slice = summary.getAsJsonObject(
                    "requestedOutputSlice");
            slice.getAsJsonArray("inputPorts").add("REGION.P.in.9");
            JsonObject declaration = slice.getAsJsonArray(
                    "containerElementFieldBindings").get(0)
                    .getAsJsonObject();
            declaration.addProperty("schemaVersion", 2);
            declaration.addProperty("materializationMode",
                    "CONTAINER_SNAPSHOT");
            declaration.addProperty("baseInputSymbol", "REGION.P.in.9");
            JsonArray path = new JsonArray();
            path.add("state");
            path.add("guard");
            path.add("enabled");
            declaration.add("fieldPath", path);
            declaration.addProperty("declaredFieldSignature",
                    "<example.Guard: boolean enabled>");
            declaration.addProperty("declaredFieldOwnerClass",
                    "example.Guard");
            declaration.addProperty("declaredFieldType", "boolean");
            declaration.addProperty("declaredFieldName", "enabled");
            declaration.addProperty("proofAuthority",
                    "STATIC_EXACT_DIRECT_ARRAY_ELEMENT_FIELD_PATH_"
                            + "CHAIN_V1");
            String method = declaration.get("method").getAsString();
            JsonArray methods = new JsonArray();
            methods.add(method);
            slice.add("methods", methods);
            JsonArray sites = new JsonArray();
            sites.add(declaration.get("arrayLoadSiteId").getAsString());
            sites.add(declaration.get(
                    "fieldMaterializationSiteId").getAsString());
            slice.add("sites", sites);
            JsonArray proof = new JsonArray();
            JsonArray causalEdges = new JsonArray();
            for (int index = 0; index < 12; index++) {
                String edgeId = "DEEP." + index;
                proof.add(edgeId);
                JsonObject edge = new JsonObject();
                edge.addProperty("edgeId", edgeId);
                causalEdges.add(edge);
            }
            declaration.add("proofCausalEdgeIds", proof.deepCopy());
            slice.add("causalEdgeIds", proof.deepCopy());
            slice.add("causalEdges", causalEdges);
            writeSummary(fixture, summary);

            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            String projection = lineContaining(result.smtLib,
                    ":named container_element_field_BIND_ARRAY_0");
            assertTrue(projection.contains("exact_field__"));
            assertTrue(projection, projection.contains(
                    "sym__port__REGION_P_in_9__int"));
            assertTrue(result.smtLib.contains(
                    "(declare-fun exact_field__"));
            assertTrue(lineContaining(result.smtLib,
                    "(declare-fun exact_field__").endsWith("(Ref) Int)"));
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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

            assertFalse(candidateReady(result.manifest));
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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

            assertFalse(candidateReady(result.manifest));
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
            ConcolicSmtComposer.Result result = ConcolicSmtComposer.compose(
                    arguments(fixture));

            assertTrue(candidateReady(result.manifest));
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
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P"
                    });
            ConcolicSmtComposer.Result bounded =
                    ConcolicSmtComposer.compose(boundedArguments);

            assertTrue(bounded.manifest.toString(), candidateReady(bounded.manifest));
            assertEquals(1, bounded.manifest.getAsJsonArray(
                    "boundedUpstreamRegions").size());
            assertTrue(bounded.smtLib.contains(
                    "(= port__REGION_P_out_0 port__REGION_F_in_0)"));
            assertFalse(bounded.smtLib.contains("writer_guard__right"));

            // A static graph may project the same concrete writer/read event
            // through aliases whose producer regions were not replayed.  Do
            // not turn those alternatives into mandatory summaries.  The
            // one exact producer becomes a direct versioned merge, and an
            // all-concrete alias group is omitted with explicit audit counts.
            JsonObject concreteOnly = new JsonObject();
            concreteOnly.addProperty("groupId", "CONCRETE.ALIASES");
            concreteOnly.addProperty("downstreamEndpoint",
                    "REGION.F.in.0");
            concreteOnly.addProperty("selectionSemantics",
                    "EXACTLY_ONE_GUARDED");
            JsonArray concreteAlternatives = new JsonArray();
            concreteAlternatives.add(guardedWriter(
                    "writer_guard__concrete_0", "REGION.Q.out.1",
                    22, 30));
            concreteAlternatives.add(guardedWriter(
                    "writer_guard__concrete_1", "REGION.Q.out.2",
                    23, 30));
            concreteOnly.add("alternatives", concreteAlternatives);
            groups.add(concreteOnly);
            fatal.add("symbolicContext", context.deepCopy());
            Files.write(fixture.fatal,
                    (fatal.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));
            Files.write(fixture.summaries,
                    (leftSummary.toString() + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result concreteFallback =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(concreteFallback.manifest.toString(),
                    candidateReady(concreteFallback.manifest));
            assertFalse(concreteFallback.manifest.getAsJsonArray(
                    "missingSummaryRegions").toString().contains(
                    "REGION.Q"));
            assertFalse(concreteFallback.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "MissingExactProducerSummary:REGION.Q"));
            assertFalse(concreteFallback.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "IncompleteAlternativeWriterGroup"));
            assertTrue(concreteFallback.smtLib.contains(
                    "(= port__REGION_P_out_0 port__REGION_F_in_0)"));
            assertFalse(concreteFallback.smtLib.contains(
                    "writer_guard__concrete"));
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
            JsonObject binding = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 30, 40, 17);
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
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments);

            assertTrue(candidateReady(result.manifest));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void composesEvidenceBackedObjectOutputFieldProjection()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            String baseCell =
                    "<example.Manager: example.Key currentKey>";
            String projectedCell = baseCell + "#field:keyId";
            addRegionPort(fixture, "REGION.P", "outputs",
                    port("REGION.P.out.3", baseCell));
            addRegionPort(fixture, "REGION.F", "symbolicInputs",
                    port("REGION.F.in.8", projectedCell));

            JsonObject summary = producerSummary(singlePutEffect(), true);
            summary.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            summary.getAsJsonObject("outputExpressions").add(
                    "REGION.P.out.3", symbol("Lexample/Key;",
                            "producer_key_ref"));
            JsonArray bindings = new JsonArray();
            bindings.add(runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 10, 30, 101));
            JsonObject projection = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.3",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.8", 11, 31, 102);
            projection.addProperty("fromOutputCell", baseCell);
            projection.addProperty("rawToInputCell", baseCell);
            projection.addProperty("toInputCell", projectedCell);
            projection.addProperty("canonicalInputResolutionUsed", true);
            projection.addProperty("canonicalInputResolutionAuthority",
                    ConcolicSmtComposer
                            .STATIC_INPUT_FIELD_PROJECTION_AUTHORITY);
            projection.addProperty("inputProjectionUsed", true);
            projection.addProperty("inputProjectionComplete", true);
            projection.add("inputProjectionPath",
                    singletonString("keyId"));
            JsonArray proofIds = new JsonArray();
            proofIds.add("DF.BASE");
            proofIds.add("DF.PROJECTION");
            proofIds.add("DF.DECLARATION");
            projection.add("inputProjectionEvidenceEdgeIds", proofIds);
            projection.addProperty("inputProjectionEvidenceAuthority",
                    ConcolicSmtComposer
                            .STATIC_INPUT_FIELD_PROJECTION_AUTHORITY);
            projection.addProperty("inputProjectionBaseCell", baseCell);
            projection.addProperty("inputProjectionTargetCell",
                    projectedCell);
            projection.addProperty(
                    "inputProjectionDeclaredFieldSignature",
                    "<example.Key: int keyId>");
            projection.addProperty("inputProjectionDeclaredFieldType",
                    "int");
            projection.addProperty(
                    "inputProjectionDeclaredFieldAuthority",
                    "SOOT_RESOLVED_DECLARATION_HIERARCHY");
            projection.addProperty(
                    "inputProjectionValueObjectIdentityConfirmed", true);
            projection.addProperty("valueObjectId", 707);
            projection.addProperty("readerValueObjectId", 707);
            bindings.add(projection);
            summary.add("edgeBindings", bindings);
            writeSummary(fixture, summary);
            installFatalRelations(fixture, bindings);

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertTrue(result.smtLib.contains(
                    "(declare-fun exact_field__"));
            String projectedEquality = lineContaining(result.smtLib,
                    "_field_projection");
            assertTrue(projectedEquality, projectedEquality.contains(
                    "sym__port__REGION_P_out_3__ref"));
            assertTrue(projectedEquality, projectedEquality.contains(
                    "sym__port__REGION_F_in_8__int"));
            assertFalse(result.smtLib.contains(
                    "(= port__REGION_P_out_3 port__REGION_F_in_8)"));
            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "InputFieldProjection"));
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
            JsonObject exactBinding = runtimeEdgeBinding("REGION.U",
                    "REGION.U@fixture#call0", "REGION.U.out.0",
                    "REGION.P", "REGION.P@fixture#call1",
                    "REGION.P.in.0", 5, 8, 91);
            bindings.add(exactBinding);
            upstream.add("edgeBindings", bindings);
            Files.write(fixture.summaries,
                    (intermediate + "\n" + upstream + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicSmtComposer.Arguments bounded =
                    ConcolicSmtComposer.Arguments.parse(new String[]{
                            "--fatal-query", fixture.fatal.toString(),
                            "--summaries", fixture.summaries.toString(),
                            "--regions", fixture.regions.toString(),
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
    public void recursivelyComposesRuntimeValueEqualityWithoutObjectIdentity()
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
            bindings.add(runtimeValueEqualityBinding("REGION.U",
                    "REGION.U@fixture#call0", "REGION.U.out.0",
                    "REGION.P", "REGION.P@fixture#call1",
                    "REGION.P.in.0", 5, 8));
            upstream.add("edgeBindings", bindings);
            Files.write(fixture.summaries,
                    (intermediate + "\n" + upstream + "\n").getBytes(
                            StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(
                            ConcolicSmtComposer.Arguments.parse(new String[]{
                                    "--fatal-query", fixture.fatal.toString(),
                                    "--summaries", fixture.summaries.toString(),
                                    "--regions", fixture.regions.toString(),
                                    "--output", fixture.output.toString(),
                                    "--manifest", fixture.manifest.toString(),
                                    "--fatal-region", "REGION.F",
                                    "--activation-id", "ACT.F",
                                    "--bounded-upstream-region", "REGION.P",
                                    "--bounded-upstream-region", "REGION.U"
                            }));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            JsonObject recursive = result.manifest.getAsJsonArray(
                    "resolvedEdgeBindings").get(0).getAsJsonObject();
            assertEquals("RUNTIME_CONFIRMED_VALUE_EQUALITY", recursive.get(
                    "selectionAuthority").getAsString());
            assertTrue(recursive.get("recursive").getAsBoolean());
            assertTrue(result.smtLib.contains(
                    "port__REGION_U_out_0 port__REGION_P_in_0"));
            assertFalse(result.smtLib.contains(
                    "identity_edge_binding_REGION_U_to_REGION_P"));
        } finally {
            folder.delete();
        }
    }

    @Test
    public void contextReadFromDoesNotBecomeAmbiguousWithEndpointEquality()
            throws Exception {
        TemporaryFolder folder = new TemporaryFolder();
        folder.create();
        try {
            Fixture fixture = fixture(folder.getRoot().toPath(), false);
            JsonObject producer = producerSummary(singlePutEffect(), true);
            producer.add("requestedOutput", requestedOutput(
                    "REGION.P.out.0"));
            JsonObject readFrom = runtimeEdgeBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 10, 20, 101);
            readFrom.addProperty("edgeId", "EDGE.0");
            JsonObject equality = runtimeValueEqualityBinding("REGION.P",
                    "REGION.P@fixture#call1", "REGION.P.out.0",
                    "REGION.F", "REGION.F@fixture#call2",
                    "REGION.F.in.0", 5, 8);
            // Deliberately share the context READ_FROM edge id and endpoints.
            // The relation kind must still keep the two semantics disjoint.
            equality.addProperty("edgeId", "EDGE.0");
            JsonArray bindings = new JsonArray();
            bindings.add(readFrom);
            bindings.add(equality);
            producer.add("edgeBindings", bindings);
            Files.write(fixture.summaries,
                    (producer + "\n").getBytes(StandardCharsets.UTF_8));

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(arguments(fixture));

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertFalse(result.manifest.getAsJsonArray(
                    "unsupportedExpressions").toString().contains(
                    "AmbiguousDirectEdgeBinding"));
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
            assertEquals(1, result.manifest.getAsJsonArray(
                    "includedSummaries").size());
            assertEquals(6, result.manifest.getAsJsonArray(
                    "resolvedProducerKeys").size());
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

            assertFalse(candidateReady(result.manifest));
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

            assertFalse(candidateReady(result.manifest));
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
            addRegionPort(fixture, "REGION.Q", "symbolicInputs",
                    port("REGION.Q.in.1",
                            "<example.Flow: int transportedInt>"));
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
            q.getAsJsonObject("outputExpressions").add(
                    "REGION.Q.out.0", symbol("I",
                            "M_I_field_REGION.Q.in.1_example/Flow"));
            JsonObject qSlice = requestedSlice("REGION.Q.in.0",
                    "REGION.Q.in.1");
            JsonArray qInputBindings = new JsonArray();
            JsonObject qSourceBinding = new JsonObject();
            qSourceBinding.addProperty("dependencyCell",
                    "<example.REGION.Q: int intermediateInt>");
            qSourceBinding.addProperty("inputPort", "REGION.Q.in.0");
            qSourceBinding.addProperty("bindingAuthority",
                    "EXACT_CELL_IDENTITY");
            qInputBindings.add(qSourceBinding);
            JsonObject qTargetBinding = new JsonObject();
            qTargetBinding.addProperty("dependencyCell",
                    "<example.Flow: int transportedInt>");
            qTargetBinding.addProperty("inputPort", "REGION.Q.in.1");
            qTargetBinding.addProperty("bindingAuthority",
                    "EXACT_CELL_IDENTITY");
            qInputBindings.add(qTargetBinding);
            qSlice.add("inputBindings", qInputBindings);
            JsonObject qCausalEdge = new JsonObject();
            qCausalEdge.addProperty("edgeId", "DF.Q.VALUE.PASS");
            qCausalEdge.addProperty("fromCell",
                    "<example.REGION.Q: int intermediateInt>");
            qCausalEdge.addProperty("toCell",
                    "<example.Flow: int transportedInt>");
            qCausalEdge.addProperty("transferKind", "VALUE_PASS");
            JsonArray qCausalEdges = new JsonArray();
            qCausalEdges.add(qCausalEdge);
            qSlice.add("causalEdges", qCausalEdges);
            qSlice.add("causalEdgeIds", singletonString(
                    "DF.Q.VALUE.PASS"));
            q.add("requestedOutputSlice", qSlice);
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

            assertTrue(result.manifest.toString(), candidateReady(result.manifest));
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
            assertTrue(result.smtLib.contains(
                    "port__REGION_U1_out_0 port__REGION_P_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_P_out_0 port__REGION_F_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_U2_out_0 port__REGION_Q_in_0"));
            assertTrue(result.smtLib.contains(
                    "port__REGION_Q_out_0 port__REGION_F_in_1"));
            assertTrue(result.manifest.getAsJsonArray(
                    "exactCausalInputAliases").toString().contains(
                    "DF.Q.VALUE.PASS"));
            assertTrue(result.smtLib.contains(
                    ":named exact_causal_input_alias_0"));
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
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });
            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertFalse(candidateReady(result.manifest));
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

            assertFalse(candidateReady(result.manifest));
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
                            "--output", fixture.output.toString(),
                            "--manifest", fixture.manifest.toString(),
                            "--fatal-region", "REGION.F",
                            "--activation-id", "ACT.F",
                            "--bounded-upstream-region", "REGION.P",
                            "--bounded-upstream-region", "REGION.U"
                    });

            ConcolicSmtComposer.Result result =
                    ConcolicSmtComposer.compose(bounded);

            assertFalse(candidateReady(result.manifest));
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
        binding.addProperty("relation", "READ_FROM");
        binding.addProperty("relationKind", "READ_FROM");
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("objectIdentityConfirmed", true);
        binding.addProperty("fieldReceiverIdentityConfirmed", true);
        binding.addProperty("writeSeq", writeSeq);
        binding.addProperty("readSeq", readSeq);
        binding.addProperty("receiverObjectId", 41);
        binding.addProperty("writeEvidenceKind", "FIELD_ASSIGNMENT");
        binding.addProperty("writeEvidenceAuthority",
                "RUNTIME_EXACT_FIELD_WRITE_EVENT_V1");
        binding.addProperty("orderAuthority",
                "GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1");
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
        summary.addProperty("relationallyComplete", complete);
        summary.add("pathCondition", new JsonArray());
        summary.add("outputExpressions", new JsonObject());
        summary.add("heapStateInitializers", initializers);
        summary.add("heapEffects", effects);
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
        binding.addProperty("relation", "READ_FROM");
        binding.addProperty("relationKind", "READ_FROM");
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
        binding.addProperty("fieldReceiverIdentityConfirmed", true);
        binding.addProperty("writeEvidenceKind", "FIELD_ASSIGNMENT");
        binding.addProperty("writeEvidenceAuthority",
                "RUNTIME_EXACT_FIELD_WRITE_EVENT_V1");
        binding.addProperty("orderAuthority",
                "GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1");
        binding.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_READ_FROM");
        return binding;
    }

    private static JsonObject runtimeValueEqualityBinding(
            String fromRegion, String fromInstance, String fromOutput,
            String toRegion, String toInstance, String toInput,
            int writerSeq, int readerSeq) {
        JsonObject binding = new JsonObject();
        binding.addProperty("edgeId", "EDGE." + fromRegion + ".TO."
                + toRegion);
        binding.addProperty("relation", "EQUALITY");
        binding.addProperty("relationKind", "EQUALITY");
        binding.addProperty("fromRegion", fromRegion);
        binding.addProperty("toRegion", toRegion);
        binding.addProperty("fromRegionInstance", fromInstance);
        binding.addProperty("toRegionInstance", toInstance);
        binding.addProperty("fromOutputPort", fromOutput);
        binding.addProperty("toInputPort", toInput);
        binding.addProperty("writerEventSeq", writerSeq);
        binding.addProperty("readerEventSeq", readerSeq);
        binding.addProperty("orderConfirmed", true);
        binding.addProperty("valueEqualityObserved", true);
        binding.addProperty("valueEqualityAuthority",
                "RUNTIME_COMPLETE_VALUE_FINGERPRINT");
        binding.addProperty("endpointOrderAuthority",
                "GLOBAL_TRACE_ENDPOINT_SEQUENCE");
        binding.addProperty("valueFingerprint", "sha256:" + fromInstance
                + ":" + toInstance + ":" + writerSeq + ":" + readerSeq);
        binding.addProperty("selectionAuthority",
                "RUNTIME_CONFIRMED_VALUE_EQUALITY");
        binding.addProperty("objectIdentityRequired", false);
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

    private static JsonObject negatedOpString(String operation,
                                              JsonElement... params) {
        JsonObject result = opString(operation, params);
        result.addProperty("_is_not", true);
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

    private static JsonObject cast(JsonElement source, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("_type", "TypeCastExpression");
        result.addProperty("_java_type", javaType);
        result.add("_exp", source);
        return result;
    }

    private static JsonObject explicitCast(JsonElement source,
                                           String sourceJavaType,
                                           String targetJavaType) {
        JsonObject result = cast(source, targetJavaType);
        result.addProperty("sourceJavaType", sourceJavaType);
        result.addProperty("targetJavaType", targetJavaType);
        return result;
    }

    private static JsonObject unaryNegation(JsonElement operand) {
        return binaryCondition(JsonNull.INSTANCE, "-", operand);
    }

    private static JsonArray fatalConstraints(JsonObject fatal) {
        BranchReplayContract contract = BranchReplayContract.fromJson(
                fatal.getAsJsonObject("replayContract"));
        SolverPathContext context = SolverPathContext.fromJson(
                fatal.getAsJsonObject("solverPathContext"));
        JsonArray result = context.expressions();
        for (JsonElement predicate : contract.requiredPathPredicates()) {
            result.add(predicate);
        }
        return result;
    }

    /** Rebuilds the immutable test protocol after changing a path formula. */
    private static void setFatalConstraints(JsonObject fatal,
                                            JsonArray constraints) {
        if (constraints == null || constraints.size() == 0) {
            throw new IllegalArgumentException(
                    "fatal test path requires a target predicate");
        }
        int targetPosition = constraints.size() - 1;
        java.util.List<BranchWitness> prefix = new java.util.ArrayList<>();
        java.util.Set<Integer> branchPositions =
                new java.util.LinkedHashSet<>();
        for (int index = 0; index < targetPosition; index++) {
            JsonElement expression = constraints.get(index);
            String type = expression.isJsonObject()
                    && expression.getAsJsonObject().has("_type")
                    ? expression.getAsJsonObject().get("_type").getAsString()
                    : "";
            if ("MethodExpression".equals(type)
                    || "_array_expr".equals(type)) {
                continue;
            }
            branchPositions.add(index);
            prefix.add(testBranchWitness("TEST#u" + (100 + index),
                    100 + index, expression, index));
        }
        JsonElement requiredTarget = constraints.get(targetPosition);
        BranchWitness source = BranchWitness.vmPc("F#u2",
                "<test.Fatal: void run()>", 2, 1, false,
                BranchPredicateAlgebra.complement(requiredTarget),
                targetPosition, testVmEvent(targetPosition));
        BranchReplayContract contract = BranchReplayContract.flip(prefix,
                source);
        SolverPathContext context = SolverPathContext.fromPath(constraints,
                branchPositions, targetPosition);
        fatal.add("replayContract", contract.toJson());
        fatal.add("solverPathContext", context.toJson());
    }

    private static BranchWitness testBranchWitness(String siteId,
                                                   int unitIndex,
                                                   JsonElement predicate,
                                                   int pcIndex) {
        return BranchWitness.vmPc(siteId, "<test.Fatal: void run()>",
                unitIndex, 1, true, predicate, pcIndex,
                testVmEvent(pcIndex));
    }

    private static JsonObject testVmEvent(int pcIndex) {
        JsonObject event = new JsonObject();
        event.addProperty("eventId", pcIndex + 1);
        return event;
    }

    private static void prependFatalConstraints(Fixture fixture,
                                                JsonElement... added)
            throws Exception {
        JsonObject fatal = JsonParser.parseString(new String(
                Files.readAllBytes(fixture.fatal),
                StandardCharsets.UTF_8).trim()).getAsJsonObject();
        JsonArray constraints = new JsonArray();
        for (JsonElement constraint : added) constraints.add(constraint);
        for (JsonElement constraint : fatalConstraints(fatal)) {
            constraints.add(constraint);
        }
        setFatalConstraints(fatal, constraints);
        Files.write(fixture.fatal, (fatal + "\n").getBytes(
                StandardCharsets.UTF_8));
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

    private static String currentTimeMillisCell() {
        return "<java.lang.System: long currentTimeMillis()>.return";
    }

    private static void addVmPlaceholderCertificate(
            JsonObject container, String inputPort, int count) {
        addVmPlaceholderCertificate(container, inputPort, count,
                vmCurrentTimeCell());
    }

    private static void addVmPlaceholderCertificate(
            JsonObject container, String inputPort, int count, String cell) {
        String identity = "currentTimeMills#" + count;
        JsonObject requirement = new JsonObject();
        requirement.addProperty("kind",
                "UNFORCED_ENVIRONMENT_VALIDATION_REQUIREMENT");
        requirement.addProperty("required", true);
        requirement.addProperty("inputPort", inputPort);
        requirement.addProperty("cell", cell);
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
        binding.addProperty("cell", cell);
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

    private static JsonObject nonMutatingDynamicHeapObservation(
            String id, String valueSymbol, String dynamicFieldSymbol) {
        return nonMutatingDynamicHeapObservation(id, valueSymbol,
                dynamicFieldSymbol, "REGION.P.in.3");
    }

    private static JsonObject nonMutatingDynamicHeapObservation(
            String id, String valueSymbol, String dynamicFieldSymbol,
            String baseInputSymbol) {
        JsonObject result = dynamicHeapObservation(id, valueSymbol,
                dynamicFieldSymbol);
        String region = "REGION.P";
        String activationId = "ACT.P";
        String dynamicBindingId = "DYNAMIC_FIELD:" + dynamicFieldSymbol;
        String selectorDigest = ConcolicSmtComposer
                .heapObservationStateSelectorDigestForTests(id,
                        baseInputSymbol, dynamicBindingId);
        String statePort = ConcolicSmtComposer
                .heapObservationStatePortForTests(region, id,
                        baseInputSymbol, dynamicBindingId);
        long mapToken = 101L;
        String mapWitness = "CAUSYNTH_REF_WITNESS_V1_A10_4143542e50_T"
                + mapToken;
        JsonObject mapExpression = symbol("L", mapWitness);
        result.addProperty("statePort", statePort);
        result.addProperty("stateBindingAuthority",
                "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1");
        result.addProperty("stateBaseComplete", true);
        result.add("mapExpression", mapExpression.deepCopy());
        result.addProperty("expressionAuthority",
                "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1");
        result.addProperty("backingMapObjectToken", mapToken);
        result.addProperty("objectTokenScope", activationId);
        result.addProperty("mapExpressionWitnessSchemaVersion", 1);
        result.addProperty("mapExpressionWitnessKind",
                "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS");
        result.addProperty("mapExpressionWitnessObjectToken", mapToken);
        result.addProperty("mapExpressionWitnessObjectTokenScope",
                activationId);
        result.addProperty("mapExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");

        JsonObject binding = result.getAsJsonArray("entryFieldBindings")
                .get(0).getAsJsonObject();
        binding.addProperty("baseInputSymbol", baseInputSymbol);
        if ("REGION.P.in.9".equals(baseInputSymbol)) {
            binding.add("fieldExpression", symbol("Z",
                    "M_Z_field_" + dynamicFieldSymbol + "_enabled"));
            binding.addProperty("fieldSignature",
                    "<example.Value: boolean enabled>");
            binding.addProperty("fieldJavaType", "boolean");
            JsonArray fieldPath = new JsonArray();
            fieldPath.add("enabled");
            binding.add("fieldPath", fieldPath);
        }
        binding.addProperty("fieldExpressionAuthority",
                "EXACT_VM_BRANCH_MAPPING_DYNAMIC_SYMBOL_AND_REQUESTED_"
                        + "SLICE_BASE_V1");
        binding.addProperty("observationStateBindingAuthority",
                "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1");

        JsonObject proof = new JsonObject();
        proof.addProperty("schemaVersion", 1);
        proof.addProperty("kind",
                "NON_MUTATING_MAP_ENTRY_READ_STATE_BASE");
        proof.addProperty("statePort", statePort);
        proof.addProperty("observationId", id);
        proof.addProperty("entryReadObservationId", id);
        proof.addProperty("regionId", region);
        proof.addProperty("activationId", activationId);
        proof.addProperty("baseInputSymbol", baseInputSymbol);
        proof.addProperty("dynamicBindingId", dynamicBindingId);
        proof.addProperty("dynamicFieldSymbol", dynamicFieldSymbol);
        proof.add("mapExpression", mapExpression.deepCopy());
        proof.addProperty("expressionAuthority",
                "ACTIVATION_LOCAL_MAP_OBJECT_TOKEN_REF_WITNESS_V1");
        proof.addProperty("backingMapObjectToken", mapToken);
        proof.addProperty("objectTokenScope", activationId);
        proof.addProperty("mapExpressionWitnessSchemaVersion", 1);
        proof.addProperty("mapExpressionWitnessKind",
                "ACTIVATION_LOCAL_MAP_REF_SYMBOL_WITNESS");
        proof.addProperty("mapExpressionWitnessObjectToken", mapToken);
        proof.addProperty("mapExpressionWitnessObjectTokenScope",
                activationId);
        proof.addProperty("mapExpressionWitnessAuthority",
                "ACTIVATION_LOCAL_IDENTITY_MAP_MONOTONIC_TOKEN_TO_"
                        + "SCOPED_REF_SYMBOL_V1");
        proof.addProperty("candidateMutationCount", 0);
        proof.addProperty("heapEffectCount", 0);
        proof.addProperty("ignoredRuntimeHeapEvidenceCount", 0);
        proof.addProperty("selectorDigest", selectorDigest);
        proof.addProperty("statePortDerivationAuthority",
                "REGION_AND_STATIC_OBSERVATION_SELECTOR_SHA256_V1");
        proof.addProperty("authority",
                "NON_MUTATING_MAP_ENTRY_READ_EXACT_DYNAMIC_FIELD_BASE_V1");
        proof.addProperty("complete", true);
        result.add("stateBaseProof", proof);
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
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "REGION_PATH_WORKLIST");
        result.addProperty("regionId", "REGION.P");
        result.addProperty("state", RegionPathWorklist.State.CLOSED.name());
        JsonObject bounds = new JsonObject();
        bounds.addProperty("maxPathsPerRegion", 64);
        bounds.addProperty("maxFlipsPerPath", 32);
        bounds.addProperty("maxTasks", 256);
        bounds.addProperty("maxWallClockMillis", 30_000L);
        result.add("bounds", bounds);
        result.addProperty("observedPathCount", 1);
        result.addProperty("pendingTaskCount", 0);
        result.add("gaps", new JsonArray());
        return result;
    }

    private static JsonObject bindingForPort(JsonObject projection,
                                             String portId) {
        for (JsonElement element : projection.getAsJsonArray("bindings")) {
            JsonObject binding = element.getAsJsonObject();
            if (portId.equals(binding.get("portId").getAsString())) {
                return binding;
            }
        }
        throw new AssertionError("missing port binding " + portId
                + " in " + projection);
    }

    private static String selectorInLine(JsonArray catalog, String smtLine) {
        for (JsonElement element : catalog) {
            String selector = element.getAsJsonObject().get(
                    "selectorTerm").getAsString();
            if (smtLine.contains(selector)) return selector;
        }
        throw new AssertionError("no case selector in " + smtLine);
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
        java.util.List<String> values = new java.util.ArrayList<>(
                java.util.Arrays.asList(
                "--fatal-query", fixture.fatal.toString(),
                "--summaries", fixture.summaries.toString(),
                "--regions", fixture.regions.toString(),
                "--output", fixture.output.toString(),
                "--manifest", fixture.manifest.toString(),
                "--fatal-region", "REGION.F",
                "--activation-id", "ACT.F"));
        return ConcolicSmtComposer.Arguments.parse(
                values.toArray(new String[0]));
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception ignored) {
            return false;
        }
    }

    private static void assertZ3Parses(String smt) throws Exception {
        Process process = new ProcessBuilder("z3", "-in")
                .redirectErrorStream(true).start();
        try (OutputStream input = process.getOutputStream()) {
            input.write(smt.getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = process.getInputStream().read(buffer)) >= 0) {
            output.write(buffer, 0, count);
        }
        int exit = process.waitFor();
        String text = new String(output.toByteArray(),
                StandardCharsets.UTF_8);
        assertEquals(text, 0, exit);
        assertFalse(text, text.contains("(error"));
    }

    private static void assertZ3Status(String smt, String expected)
            throws Exception {
        Process process = new ProcessBuilder("z3", "-in")
                .redirectErrorStream(true).start();
        try (OutputStream input = process.getOutputStream()) {
            input.write(smt.getBytes(StandardCharsets.UTF_8));
        }
        ByteArrayOutputStream output = new ByteArrayOutputStream();
        byte[] buffer = new byte[4096];
        int count;
        while ((count = process.getInputStream().read(buffer)) >= 0) {
            output.write(buffer, 0, count);
        }
        int exit = process.waitFor();
        String text = new String(output.toByteArray(),
                StandardCharsets.UTF_8).trim();
        assertEquals(text, 0, exit);
        assertFalse(text, text.contains("(error"));
        assertTrue(text, text.equals(expected)
                || text.startsWith(expected + "\n"));
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
                + "\"selectedBindings\":[{"
                + "\"relation\":\"READ_FROM\","
                + "\"relationKind\":\"READ_FROM\","
                + "\"fromRegion\":\"REGION.P\","
                + "\"toRegion\":\"REGION.F\","
                + "\"fromRegionInstance\":"
                + "\"REGION.P@fixture#call1\","
                + "\"toRegionInstance\":"
                + "\"REGION.F@fixture#call2\","
                + "\"fromOutputPort\":\"REGION.P.out.0\","
                + "\"toInputPort\":\"REGION.F.in.0\","
                + "\"writerEventSeq\":10,\"readerEventSeq\":20,"
                + "\"writeSeq\":10,\"readSeq\":20,"
                + "\"receiverObjectId\":41,"
                + "\"orderConfirmed\":true,"
                + "\"objectIdentityConfirmed\":true,"
                + "\"fieldReceiverIdentityConfirmed\":true,"
                + "\"writeEvidenceKind\":\"FIELD_ASSIGNMENT\","
                + "\"writeEvidenceAuthority\":"
                + "\"RUNTIME_EXACT_FIELD_WRITE_EVENT_V1\","
                + "\"orderAuthority\":"
                + "\"GLOBAL_RECORDER_MONOTONIC_SEQUENCE_ORDER_V1\","
                + "\"selectionAuthority\":"
                + "\"RUNTIME_CONFIRMED_READ_FROM\"}]}]}";
        JsonObject fatal = new JsonObject();
        fatal.addProperty("schemaVersion", 1);
        fatal.addProperty("kind", "TARGET_BRANCH_SOLVER_QUERY");
        fatal.addProperty("activationId", "ACT.F");
        fatal.addProperty("regionId", "REGION.F");
        fatal.addProperty("regionInstanceId", "REGION.F@fixture#call2");
        fatal.addProperty("readyForSolver", true);
        JsonArray fatalPath = JsonParser.parseString("[{"
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
                + "\"_java_type\":\"\",\"_exp\":\"N\"}}]")
                .getAsJsonArray();
        setFatalConstraints(fatal, fatalPath);
        fatal.add("symbolicContext", JsonParser.parseString(context));
        Files.write(fixture.fatal, (fatal + "\n").getBytes(
                StandardCharsets.UTF_8));

        if (includeProducerSummary) {
            writeSummary(fixture, producerSummary(singlePutEffect(), true));
        } else {
            Files.write(fixture.summaries, new byte[0]);
        }
        return fixture;
    }

    private static boolean candidateReady(JsonObject manifest) {
        return manifest != null
                && manifest.has("schemaVersion")
                && manifest.get("schemaVersion").getAsInt() == 2
                && "CONCOLIC_COMPOSED_SMT".equals(
                manifest.get("kind").getAsString())
                && "CANDIDATE_ONLY".equals(
                manifest.get("trustState").getAsString())
                && "CANDIDATE_READY".equals(
                manifest.get("state").getAsString());
    }

    private static final class Fixture {
        private final Path fatal;
        private final Path summaries;
        private final Path regions;
        private final Path output;
        private final Path manifest;

        private Fixture(Path root) {
            fatal = root.resolve("fatal.jsonl");
            summaries = root.resolve("summaries.jsonl");
            regions = root.resolve("regions.jsonl");
            output = root.resolve("composed.smt2");
            manifest = root.resolve("manifest.json");
        }
    }
}
