package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Assume;
import org.junit.Test;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class BooleanReachConditionExtractorTest {
    @Test
    public void cliWritesAuditableReportFromFileArtifacts()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();
        Path directory = Files.createTempDirectory("boolean-reach-cli-");
        Path smt = directory.resolve("composed.smt2");
        Path manifest = directory.resolve("manifest.json");
        Path regions = directory.resolve("regions.jsonl");
        Path relationships = directory.resolve("relationships.json");
        Path output = directory.resolve("reach.json");
        try {
            Files.write(smt, fixture.smt.getBytes(StandardCharsets.UTF_8));
            StringBuilder regionLines = new StringBuilder();
            for (JsonObject region : fixture.regions) {
                regionLines.append(region).append('\n');
            }
            Files.write(regions, regionLines.toString().getBytes(
                    StandardCharsets.UTF_8));
            bindCliArtifacts(fixture.manifest, smt, regions);
            Files.write(relationships, fixture.relationships.toString()
                    .getBytes(StandardCharsets.UTF_8));
            fixture.manifest.add("relationshipCandidatesArtifact",
                    BooleanReachConditionExtractor.artifact(relationships));
            Files.write(manifest, fixture.manifest.toString().getBytes(
                    StandardCharsets.UTF_8));

            BooleanReachConditionExtractor.main(new String[]{
                    "--smt", smt.toString(),
                    "--manifest", manifest.toString(),
                    "--regions", regions.toString(),
                    "--relationships", relationships.toString(),
                    "--output", output.toString(),
                    "--z3", "z3",
                    "--timeout-ms", "10000"
            });

            JsonObject report = JsonParser.parseString(new String(
                    Files.readAllBytes(output), StandardCharsets.UTF_8))
                    .getAsJsonObject();
            assertTrue(report.get("complete").getAsBoolean());
            assertEquals("BOOLEAN_REACH_CONDITION_REPORT",
                    report.get("kind").getAsString());
            assertEquals("COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL",
                    report.get("status").getAsString());
            assertEquals(2, report.getAsJsonArray(
                    "rootBooleanInputs").size());
            assertEquals(4, report.getAsJsonArray("truthTable").size());
            assertTrue(report.has("reachCondition"));
            assertTrue(report.has("reachConditionSmtLib"));
            assertEquals(Files.size(smt), report.getAsJsonObject(
                    "composedSmtArtifact").get("sizeBytes").getAsLong());
            assertTrue(report.getAsJsonObject("composedSmtArtifact")
                    .get("sha256").getAsString().matches("[0-9a-f]{64}"));
            assertTrue(report.getAsJsonObject("solverArtifact")
                    .get("version").getAsString().contains("Z3"));
            assertTrue(report.getAsJsonObject("solverArtifact")
                    .get("sha256").getAsString().matches("[0-9a-f]{64}"));
        } finally {
            Files.deleteIfExists(output);
            Files.deleteIfExists(relationships);
            Files.deleteIfExists(regions);
            Files.deleteIfExists(manifest);
            Files.deleteIfExists(smt);
            Files.deleteIfExists(directory);
        }
    }

    @Test
    public void enumeratesAutomaticallyDiscoveredRootsWithActualZ3()
            throws Exception {
        Assume.assumeTrue(z3Available());
        Fixture fixture = fixture();

        BooleanReachConditionExtractor.Extraction extraction =
                BooleanReachConditionExtractor.extract(fixture.smt,
                        fixture.manifest, fixture.regions,
                        fixture.relationships,
                        new BooleanReachConditionExtractor.Z3Solver(
                                "z3", 10_000L), 8, 256);

        JsonObject report = extraction.report;
        assertTrue(report.toString(), report.get("complete").getAsBoolean());
        assertEquals("COMPLETE_BOOTSTRAP_BOOLEAN_REPLAY_MODEL",
                report.get("status").getAsString());
        assertTrue(report.get("replayBootstrapOnly").getAsBoolean());
        assertFalse(report.get("reportableFinalReachCondition")
                .getAsBoolean());
        assertFalse(report.get("callerProvidedConditionUsed").getAsBoolean());
        assertEquals(3, report.get("staticBooleanInputCount").getAsInt());
        assertEquals(3, report.get("usedBooleanInputCount").getAsInt());
        assertEquals(1, report.get(
                "upstreamSuppliedBooleanInputCount").getAsInt());
        assertEquals(2, report.get("rootBooleanInputCount").getAsInt());
        assertEquals(3, report.get("projectionDomainInputCount").getAsInt());
        assertEquals(4, report.get("valuationCount").getAsInt());
        assertEquals(2, report.get("satisfyingValuationCount").getAsInt());
        assertEquals(2, report.get("unsatisfyingValuationCount").getAsInt());
        assertTrue(report.get("baseImpliesReachCondition").getAsBoolean());
        assertEquals("unsat", report.get(
                "baseImpliesReachConditionStatus").getAsString());
        assertEquals("COMPOSED_SMT_AND_JAVA_BOOLEAN_PROJECTION_DOMAIN",
                report.get("implicationPremise").getAsString());

        JsonArray roots = report.getAsJsonArray("rootBooleanInputs");
        assertEquals("ROOT.A.in.0", roots.get(0).getAsJsonObject()
                .get("portId").getAsString());
        assertEquals("ROOT.B.in.0", roots.get(1).getAsJsonObject()
                .get("portId").getAsString());
        assertFalse(roots.toString().contains("SUPPLIED.C.in.0"));
        for (JsonElement root : roots) {
            assertEquals("JAVA_BOOLEAN_AS_INT_0_1",
                    root.getAsJsonObject().get("booleanEncoding")
                            .getAsString());
        }

        JsonArray truthTable = report.getAsJsonArray("truthTable");
        JsonArray clauses = report.getAsJsonObject("reachCondition")
                .getAsJsonArray("clauses");
        assertEquals(report.get("satisfyingValuationCount").getAsInt(),
                clauses.size());
        for (JsonElement clauseElement : clauses) {
            JsonObject clause = clauseElement.getAsJsonObject();
            int ordinal = clause.get("valuationOrdinal").getAsInt();
            JsonObject truth = truthTable.get(ordinal).getAsJsonObject();
            assertTrue(truth.get("reachesBug").getAsBoolean());
            assertEquals(roots.size(), clause.getAsJsonArray(
                    "literals").size());
        }
        assertFalse(report.get("reachConditionSmtLib").getAsString()
                .isEmpty());
    }

    @Test
    public void reportsNonBooleanScalarRootsAsExistentialWithoutEnumerating()
            throws Exception {
        Fixture fixture = fixture();
        String integer = "ROOT.A.in.1";
        String longValue = "ROOT.A.in.2";
        String text = "ROOT.A.in.3";
        String unused = "ROOT.A.in.4";
        String supplied = "SUPPLIED.C.in.1";
        String suppliedOutput = "PRODUCER.C.out.1";
        JsonArray rootInputs = fixture.regions.get(0).getAsJsonArray(
                "symbolicInputs");
        rootInputs.add(input(integer, "int"));
        rootInputs.add(input(longValue, "long"));
        rootInputs.add(input(text, "java.lang.String"));
        rootInputs.add(input(unused, "double"));
        fixture.regions.get(2).getAsJsonArray("symbolicInputs").add(
                input(supplied, "int"));
        fixture.regions.get(3).getAsJsonArray("outputs").add(
                output(suppliedOutput, "int"));

        JsonArray mappings = fixture.manifest.getAsJsonArray(
                "caseProjectionCatalog").get(0).getAsJsonObject()
                .getAsJsonArray("rawEngineSymbolMappings");
        mappings.add(scalarMapping(integer, "INT", "Int", "int"));
        mappings.add(scalarMapping(longValue, "INT", "Int", "int"));
        mappings.add(scalarMapping(text, "STRING", "String", "string"));
        mappings.add(scalarMapping(supplied, "INT", "Int", "int"));

        JsonObject relation = new JsonObject();
        JsonObject roles = new JsonObject();
        roles.addProperty("left", suppliedOutput);
        roles.addProperty("right", supplied);
        relation.add("roles", roles);
        JsonArray relationshipRows = fixture.relationships.getAsJsonArray(
                "relationships");
        relationshipRows.add(relation);

        StringBuilder scalarSmt = new StringBuilder();
        appendScalarPort(scalarSmt, integer, "Int", "int", "VInt");
        appendScalarPort(scalarSmt, longValue, "Int", "int", "VInt");
        appendScalarPort(scalarSmt, text, "String", "string", "VString");
        appendScalarPort(scalarSmt, supplied, "Int", "int", "VInt");
        scalarSmt.append("(declare-const port__")
                .append(smtName(suppliedOutput)).append(" Value)\n");
        String smt = fixture.smt.replace(
                "(declare-datatypes () ((Value (VInt (v Int)))))",
                "(declare-sort Ref 0)\n"
                        + "(declare-datatypes () ((Value (VInt (v Int)) "
                        + "(VString (s String)) (VRef (r Ref)))))\n"
                        + "(declare-const nullRef Ref)")
                .replace("(check-sat)\n",
                        scalarSmt + "(check-sat)\n");

        BooleanReachConditionExtractor.Extraction extraction =
                BooleanReachConditionExtractor.extract(smt,
                        fixture.manifest, fixture.regions,
                        fixture.relationships, query -> query.contains(
                                "(assert (not true))")
                                ? new BooleanReachConditionExtractor
                                .SolverResult("unsat", "unsat")
                                : new BooleanReachConditionExtractor
                                .SolverResult("sat", "sat"),
                        8, 256);

        JsonObject report = extraction.report;
        assertTrue(report.toString(), report.get("complete").getAsBoolean());
        assertEquals(2, report.get("rootBooleanInputCount").getAsInt());
        assertEquals(4, report.get("valuationCount").getAsInt());
        assertEquals(4, report.getAsJsonArray("truthTable").size());
        assertEquals(5, report.get(
                "staticNonBooleanScalarInputCount").getAsInt());
        assertEquals(4, report.get(
                "usedNonBooleanScalarInputCount").getAsInt());
        assertEquals(1, report.get(
                "upstreamSuppliedNonBooleanScalarInputCount").getAsInt());
        assertEquals(3, report.get(
                "existentialNonBooleanRootInputCount").getAsInt());
        assertTrue(report.get("nullableJavaStringModeled").getAsBoolean());
        assertEquals(1, report.get(
                "nullableJavaStringInputCount").getAsInt());
        assertEquals("JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1",
                report.get("nullableStringEncodingAuthority").getAsString());

        JsonArray existential = report.getAsJsonArray(
                "existentialNonBooleanRootInputs");
        assertScalarInput(existential.get(0).getAsJsonObject(), integer,
                "I", "Int", "int");
        assertScalarInput(existential.get(1).getAsJsonObject(), longValue,
                "J", "Int", "int");
        assertScalarInput(existential.get(2).getAsJsonObject(), text,
                "Ljava/lang/String;", "String", "string");
        assertFalse(existential.toString().contains(unused));
        assertFalse(existential.toString().contains(supplied));
        for (JsonElement row : report.getAsJsonArray("truthTable")) {
            assertEquals(2, row.getAsJsonObject().getAsJsonArray(
                    "assignments").size());
            assertFalse(row.toString().contains(integer));
            assertFalse(row.toString().contains(longValue));
            assertFalse(row.toString().contains(text));
        }
    }

    @Test
    public void incompleteCompositionFailsBeforeAnySolverInvocation()
            throws Exception {
        Fixture fixture = fixture();
        fixture.manifest.addProperty("structurallyComplete", false);
        final int[] invocations = {0};

        BooleanReachConditionExtractor.Extraction extraction =
                BooleanReachConditionExtractor.extract(fixture.smt,
                        fixture.manifest, fixture.regions,
                        fixture.relationships,
                        new BooleanReachConditionExtractor.Solver() {
                            @Override
                            public BooleanReachConditionExtractor.SolverResult
                            check(String smt) {
                                invocations[0]++;
                                return new BooleanReachConditionExtractor
                                        .SolverResult("sat", "sat");
                            }
                        }, 8, 256);

        assertFalse(extraction.report.get("complete").getAsBoolean());
        assertEquals(0, invocations[0]);
        assertEquals(0, extraction.report.get(
                "solverInvocationCount").getAsInt());
        assertTrue(extraction.report.getAsJsonArray("discoveryGaps")
                .toString().contains(
                        "COMPOSITION_MANIFEST_NOT_BOOTSTRAP_MODEL_ELIGIBLE"));
    }

    @Test
    public void completeUnsatBootstrapHasExplicitNonReplayTerminalStatus()
            throws Exception {
        Fixture fixture = fixture();
        configureBootstrap(fixture);

        BooleanReachConditionExtractor.Extraction bootstrap =
                BooleanReachConditionExtractor.extract(fixture.smt,
                        fixture.manifest, fixture.regions,
                        fixture.relationships, alwaysUnsatSolver(),
                        8, 256);

        JsonObject bootstrapReport = bootstrap.report;
        assertTrue(bootstrapReport.toString(), bootstrapReport.get(
                "complete").getAsBoolean());
        assertEquals("COMPLETE_BOOTSTRAP_UNREACHABLE",
                bootstrapReport.get("status").getAsString());
        assertEquals("UNREACHABLE", bootstrapReport.get(
                "reachabilityStatus").getAsString());
        assertEquals(0, bootstrapReport.get(
                "satisfyingValuationCount").getAsInt());
        assertEquals(4, bootstrapReport.get(
                "unsatisfyingValuationCount").getAsInt());
        assertFalse(bootstrapReport.get(
                "bootstrapReplayModelAvailable").getAsBoolean());
        assertFalse(bootstrapReport.get(
                "reportableFinalReachCondition").getAsBoolean());
        assertFalse(bootstrapReport.get(
                "fatalReplayValidated").getAsBoolean());
    }

    @Test
    public void finalArtifactBindingsRejectCrossWiredInputs()
            throws Exception {
        Fixture fixture = fixture();
        Path directory = Files.createTempDirectory("boolean-reach-bindings-");
        Path smt = directory.resolve("composed.smt2");
        Path regions = directory.resolve("regions.jsonl");
        Path relationships = directory.resolve("relationships.json");
        try {
            byte[] exactSmt = fixture.smt.getBytes(StandardCharsets.UTF_8);
            StringBuilder regionLines = new StringBuilder();
            for (JsonObject region : fixture.regions) {
                regionLines.append(region).append('\n');
            }
            byte[] exactRegions = regionLines.toString().getBytes(
                    StandardCharsets.UTF_8);
            Files.write(smt, exactSmt);
            Files.write(regions, exactRegions);
            bindCliArtifacts(fixture.manifest, smt, regions);
            byte[] exactRelationships = fixture.relationships.toString()
                    .getBytes(StandardCharsets.UTF_8);
            Files.write(relationships, exactRelationships);
            fixture.manifest.add("relationshipCandidatesArtifact",
                    BooleanReachConditionExtractor.artifact(relationships));

            BooleanReachConditionExtractor.validateArtifactBindings(smt,
                    regions, relationships, fixture.manifest);

            Files.write(smt, (fixture.smt + "; cross-wired\n").getBytes(
                    StandardCharsets.UTF_8));
            assertArtifactRejected(smt, regions, relationships,
                    fixture.manifest);
            Files.write(smt, exactSmt);

            Files.write(regions, (regionLines + "{}\n").getBytes(
                    StandardCharsets.UTF_8));
            assertArtifactRejected(smt, regions, relationships,
                    fixture.manifest);
            Files.write(regions, exactRegions);

            JsonObject otherRelationships = fixture.relationships.deepCopy();
            otherRelationships.addProperty("crossWired", true);
            Files.write(relationships, otherRelationships.toString().getBytes(
                    StandardCharsets.UTF_8));
            assertArtifactRejected(smt, regions, relationships,
                    fixture.manifest);
        } finally {
            Files.deleteIfExists(relationships);
            Files.deleteIfExists(regions);
            Files.deleteIfExists(smt);
            Files.deleteIfExists(directory);
        }
    }

    @Test
    public void solverStatusUsesOnlyFirstNonEmptyStdoutLine() {
        assertEquals("sat", BooleanReachConditionExtractor.solverStatus(
                "\n sat\nwarning"));
        assertEquals("unknown", BooleanReachConditionExtractor.solverStatus(
                "diagnostic\nsat"));
    }

    @Test
    public void z3SolverAttestsExecutableAndRejectsNonzeroSatOutput()
            throws Exception {
        Path directory = Files.createTempDirectory("fake-z3-");
        Path executable = directory.resolve("z3-fake");
        try {
            Files.write(executable, ("#!/bin/sh\n"
                    + "if [ \"$1\" = \"-version\" ]; then\n"
                    + "  echo 'Z3 version 0.0-test'\n"
                    + "  exit 0\n"
                    + "fi\n"
                    + "echo sat\n"
                    + "exit 7\n").getBytes(StandardCharsets.UTF_8));
            assertTrue(executable.toFile().setExecutable(true));
            BooleanReachConditionExtractor.Z3Solver solver =
                    new BooleanReachConditionExtractor.Z3Solver(
                            executable.toString(), 5_000L);
            BooleanReachConditionExtractor.SolverResult result =
                    solver.check("(check-sat)\n");
            assertEquals("error", result.status);
            JsonObject identity = solver.artifact();
            assertEquals(executable.toRealPath().toString(),
                    identity.get("path").getAsString());
            assertEquals("Z3 version 0.0-test",
                    identity.get("version").getAsString());
            assertTrue(identity.get("sha256").getAsString().matches(
                    "[0-9a-f]{64}"));
        } finally {
            Files.deleteIfExists(executable);
            Files.deleteIfExists(directory);
        }
    }

    @Test
    public void shortCircuitCaseMayOmitAnUnusedBooleanRootMapping()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject firstCase = fixture.manifest.getAsJsonArray(
                "caseProjectionCatalog").get(0).getAsJsonObject();
        firstCase.addProperty("regionId", "ROOT.A");
        firstCase.addProperty("caseId", "CASE.ROOT.A.1");
        JsonObject secondCase = firstCase.deepCopy();
        secondCase.addProperty("caseId", "CASE.ROOT.A.2");
        JsonArray secondMappings = secondCase.getAsJsonArray(
                "rawEngineSymbolMappings");
        for (int index = secondMappings.size() - 1; index >= 0; index--) {
            if ("ROOT.A.in.0".equals(secondMappings.get(index)
                    .getAsJsonObject().get("canonicalPort").getAsString())) {
                secondMappings.remove(index);
            }
        }
        fixture.manifest.getAsJsonArray("caseProjectionCatalog").add(
                secondCase);
        fixture.manifest.addProperty("caseProjectionCatalogCount", 2);
        final int[] invocations = {0};

        BooleanReachConditionExtractor.Extraction extraction =
                BooleanReachConditionExtractor.extract(fixture.smt,
                        fixture.manifest, fixture.regions,
                        fixture.relationships, smt -> {
                            invocations[0]++;
                            return new BooleanReachConditionExtractor
                                    .SolverResult(smt.contains(
                                    "(assert (not true))")
                                    ? "unsat" : "sat", smt.contains(
                                    "(assert (not true))")
                                    ? "unsat" : "sat");
                        }, 8, 256);

        assertTrue(extraction.report.toString(), extraction.report.get(
                "complete").getAsBoolean());
        assertTrue(invocations[0] > 0);
        assertFalse(extraction.report.getAsJsonArray("discoveryGaps")
                .toString().contains("CASE_MAPPING"));
        JsonArray evidence = extraction.report.getAsJsonArray(
                "rootBooleanInputs").get(0).getAsJsonObject()
                .getAsJsonArray("caseProjectionEvidence");
        assertEquals(1, evidence.size());
    }

    @Test
    public void duplicatedDynamicBridgeAssertionFailsClosed()
            throws Exception {
        Fixture fixture = fixture();
        JsonObject pathCase = fixture.manifest.getAsJsonArray(
                "caseProjectionCatalog").get(0).getAsJsonObject();
        pathCase.addProperty("regionId", "ROOT.A");
        pathCase.addProperty("selectorSolverSymbol", "case_root_a");
        JsonObject mapping = pathCase.getAsJsonArray(
                "rawEngineSymbolMappings").get(0).getAsJsonObject();
        String port = "ROOT.A.in.0";
        String canonical = solverTerm(port);
        String actual = "actual_dynamic_root_a";
        String id = "DYNAMIC_FIELD:ROOT.A.in.0.field.exact.occ.1";
        String expression = "(= " + actual + " " + canonical + ")";
        String formula = "(=> case_root_a " + expression + ")";
        String assertionName = "bridge_root_a";
        String assertion = "(assert (! " + formula + " :named "
                + assertionName + "))";
        mapping.addProperty("solverTerm", actual);
        mapping.addProperty("sort", "INT");
        mapping.addProperty("solverSort", "Int");
        mapping.addProperty("termKind", "SCOPED_DYNAMIC_FIELD");
        JsonArray ids = new JsonArray();
        ids.add(id);
        mapping.add("dynamicBindingIds", ids);
        mapping.addProperty("canonicalSolverTerm", canonical);
        mapping.addProperty("canonicalBridgeGuard", "case_root_a");
        mapping.addProperty("canonicalBridgeExpression", expression);
        mapping.addProperty("canonicalBridgeFormula", formula);
        mapping.addProperty("canonicalBridgeAssertionName", assertionName);
        mapping.addProperty("canonicalBridgeAssertion", assertion);
        mapping.addProperty("canonicalBridgeAssertionSha256",
                sha256(assertion));
        mapping.addProperty("canonicalBridgeAuthority",
                "CASE_UNIQUE_DYNAMIC_BASE_TO_CANONICAL_PORT_"
                        + "GUARDED_EQUALITY_V1");
        JsonObject binding = new JsonObject();
        binding.addProperty("dynamicBindingId", id);
        binding.addProperty("baseInputSymbol", port);
        binding.addProperty("solverTerm", actual);
        binding.addProperty("fieldExpressionRawEngineSymbol",
                mapping.get("rawEngineSymbol").getAsString());
        binding.addProperty("complete", true);
        binding.addProperty("observationMatched", true);
        binding.addProperty("termBindingAuthority",
                "EMITTER_ACTUAL_DYNAMIC_FIELD_TERM");
        JsonArray bindings = new JsonArray();
        bindings.add(binding);
        pathCase.add("dynamicFieldBindings", bindings);
        String bridge = "(declare-const actual_dynamic_root_a Int)\n"
                + "(declare-const case_root_a Bool)\n" + assertion + "\n"
                + assertion + "\n";
        String smt = fixture.smt.replace("(check-sat)\n",
                bridge + "(check-sat)\n");
        final int[] invocations = {0};

        BooleanReachConditionExtractor.Extraction extraction =
                BooleanReachConditionExtractor.extract(smt,
                        fixture.manifest, fixture.regions,
                        fixture.relationships, query -> {
                            invocations[0]++;
                            return new BooleanReachConditionExtractor
                                    .SolverResult("sat", "sat");
                        }, 8, 256);

        assertFalse(extraction.report.get("complete").getAsBoolean());
        assertEquals(0, invocations[0]);
        assertTrue(extraction.report.getAsJsonArray("discoveryGaps")
                .toString().contains(
                        "BOOLEAN_CASE_TERM_MISMATCH:ROOT.A.in.0"));
    }

    private static void configureBootstrap(Fixture fixture) {
        fixture.manifest.addProperty("compositionStage", "BOOTSTRAP");
        fixture.manifest.addProperty("structurallyComplete", true);
        fixture.manifest.addProperty("eligibleForBootstrapModel", true);
        fixture.manifest.addProperty("fatalReplayValidated", false);
        fixture.manifest.addProperty("complete", false);
        fixture.manifest.addProperty(
                "eligibleToReportAutomaticRelationship", false);
        fixture.relationships.addProperty(
                "eligibleForAutomaticVerification", false);
    }

    private static BooleanReachConditionExtractor.Solver alwaysUnsatSolver() {
        return query -> new BooleanReachConditionExtractor.SolverResult(
                "unsat", "unsat");
    }

    private static void bindCliArtifacts(JsonObject manifest,
                                         Path smt, Path regions)
            throws Exception {
        JsonObject smtArtifact = BooleanReachConditionExtractor.artifact(smt);
        JsonObject regionsArtifact =
                BooleanReachConditionExtractor.artifact(regions);
        JsonObject sourceArtifact = smtArtifact.deepCopy();
        JsonArray summaries = new JsonArray();
        summaries.add(sourceArtifact.deepCopy());
        manifest.addProperty("artifactBindingAuthority",
                "COMPOSER_EXACT_CLI_INPUT_AND_OUTPUT_SHA256_V1");
        manifest.add("composedSmtArtifact", smtArtifact);
        manifest.add("staticRegionsArtifact", regionsArtifact);
        manifest.add("fatalQueriesArtifact", sourceArtifact);
        manifest.add("summaryInputArtifacts", summaries);
    }

    private static void assertArtifactRejected(Path smt, Path regions,
                                               Path relationshipsPath,
                                               JsonObject manifest)
            throws Exception {
        boolean rejected = false;
        try {
            BooleanReachConditionExtractor.validateArtifactBindings(smt,
                    regions, relationshipsPath, manifest);
        } catch (java.io.IOException expected) {
            rejected = true;
        }
        assertTrue("cross-wired artifact must be rejected", rejected);
    }

    private static Fixture fixture() {
        String first = "ROOT.A.in.0";
        String second = "ROOT.B.in.0";
        String supplied = "SUPPLIED.C.in.0";
        String output = "PRODUCER.C.out.0";
        List<JsonObject> regions = Arrays.asList(
                region("ROOT.A", input(first, "boolean"), null),
                region("ROOT.B", input(second, "java.lang.Boolean"), null),
                region("SUPPLIED.C", input(supplied, "boolean"), null),
                region("PRODUCER.C", null,
                        output(output, "boolean")));

        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 1);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("compositionStage", "BOOTSTRAP");
        manifest.addProperty("structurallyComplete", true);
        manifest.addProperty("complete", false);
        manifest.addProperty("fatalReplayValidated", false);
        manifest.addProperty("eligibleForBootstrapModel", true);
        manifest.addProperty("eligibleToReportAutomaticRelationship", false);
        manifest.addProperty("caseProjectionCatalogComplete", true);
        JsonObject pathCase = caseProjection(first, second, supplied);
        JsonArray cases = new JsonArray();
        cases.add(pathCase);
        manifest.add("caseProjectionCatalog", cases);
        manifest.addProperty("caseProjectionCatalogCount", cases.size());

        JsonObject relationships = new JsonObject();
        relationships.addProperty("schemaVersion", 1);
        relationships.addProperty("kind",
                "SYMBOLIC_RELATIONSHIP_CANDIDATES");
        relationships.addProperty("eligibleForAutomaticVerification", false);
        JsonObject relation = new JsonObject();
        JsonObject roles = new JsonObject();
        roles.addProperty("left", output);
        roles.addProperty("right", supplied);
        relation.add("roles", roles);
        JsonArray relationshipRows = new JsonArray();
        relationshipRows.add(relation);
        relationships.add("relationships", relationshipRows);

        String firstTerm = solverTerm(first);
        String secondTerm = solverTerm(second);
        StringBuilder smt = new StringBuilder();
        smt.append("(set-logic ALL)\n")
                .append("(declare-datatypes () ((Value (VInt (v Int)))))\n");
        appendBooleanPort(smt, first);
        appendBooleanPort(smt, second);
        appendBooleanPort(smt, supplied);
        smt.append("(declare-const port__")
                .append(smtName(output)).append(" Value)\n")
                .append("(assert (= port__").append(smtName(output))
                .append(" port__").append(smtName(supplied)).append("))\n")
                .append("(assert (= (+ ").append(firstTerm).append(' ')
                .append(secondTerm).append(") 1))\n")
                .append("(check-sat)\n");
        return new Fixture(smt.toString(), manifest, regions,
                relationships);
    }

    private static String sha256(String value) throws Exception {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        StringBuilder result = new StringBuilder();
        for (byte current : digest.digest(value.getBytes(
                StandardCharsets.UTF_8))) {
            result.append(String.format("%02x", current & 0xff));
        }
        return result.toString();
    }

    private static JsonObject caseProjection(String... ports) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 1);
        result.addProperty("kind", "GUARDED_CASE_PROJECTION_CATALOG");
        result.addProperty("regionId", "ROOTS");
        result.addProperty("caseId", "CASE.ROOTS");
        result.addProperty("sourceSummaryId", "SUMMARY.ROOTS");
        result.addProperty("complete", true);
        result.addProperty("rawEngineSymbolMappingAuthority",
                "EMITTER_ACTUAL_TERM_CAPTURE_IN_CASE_SCOPE");
        JsonArray mappings = new JsonArray();
        for (String port : ports) {
            JsonObject mapping = new JsonObject();
            mapping.addProperty("rawEngineSymbol", "M_Z_" + smtName(port));
            mapping.addProperty("canonicalPort", port);
            mapping.addProperty("solverTerm", solverTerm(port));
            mapping.addProperty("solverSort", "Int");
            mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
            mappings.add(mapping);
        }
        result.add("rawEngineSymbolMappings", mappings);
        return result;
    }

    private static JsonObject region(String id, JsonObject input,
                                     JsonObject output) {
        JsonObject result = new JsonObject();
        result.addProperty("regionId", id);
        JsonArray inputs = new JsonArray();
        if (input != null) inputs.add(input);
        JsonArray outputs = new JsonArray();
        if (output != null) outputs.add(output);
        result.add("symbolicInputs", inputs);
        result.add("outputs", outputs);
        return result;
    }

    private static JsonObject input(String port, String javaType) {
        JsonObject result = new JsonObject();
        result.addProperty("portId", port);
        result.addProperty("cell", "<example.Input: " + javaType
                + " value>");
        result.addProperty("javaType", javaType);
        return result;
    }

    private static JsonObject output(String port, String javaType) {
        JsonObject result = input(port, javaType);
        result.addProperty("cell", "<example.Output: " + javaType
                + " value>");
        return result;
    }

    private static void appendBooleanPort(StringBuilder smt, String port) {
        String normalized = smtName(port);
        String term = solverTerm(port);
        smt.append("(declare-const port__").append(normalized)
                .append(" Value)\n")
                .append("(declare-const ").append(term).append(" Int)\n")
                .append("(assert (= port__").append(normalized)
                .append(" (VInt ").append(term).append(")))\n");
    }

    private static void appendScalarPort(StringBuilder smt, String port,
                                         String sort, String suffix,
                                         String constructor) {
        String normalized = smtName(port);
        String term = "sym__port__" + normalized + "__" + suffix;
        smt.append("(declare-const port__").append(normalized)
                .append(" Value)\n")
                .append("(declare-const ").append(term).append(' ')
                .append(sort).append(")\n");
        if ("String".equals(sort)) {
            String nullness = term + "_is_null";
            smt.append("(declare-const ").append(nullness)
                    .append(" Bool)\n")
                    .append("(assert (= port__").append(normalized)
                    .append(" (ite ").append(nullness)
                    .append(" (VRef nullRef) (VString ")
                    .append(term).append("))))\n");
        } else {
            smt.append("(assert (= port__").append(normalized)
                    .append(" (").append(constructor).append(' ')
                    .append(term).append(")))\n");
        }
    }

    private static JsonObject scalarMapping(String port, String sort,
                                            String solverSort,
                                            String suffix) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("rawEngineSymbol", "M_" + sort + "_"
                + smtName(port));
        mapping.addProperty("canonicalPort", port);
        mapping.addProperty("solverTerm", "sym__port__" + smtName(port)
                + "__" + suffix);
        mapping.addProperty("sort", sort);
        mapping.addProperty("solverSort", solverSort);
        mapping.addProperty("termKind", "CANONICAL_PORT_TERM");
        if ("STRING".equals(sort)) {
            mapping.addProperty("nullnessSolverTerm",
                    "sym__port__" + smtName(port)
                            + "__string_is_null");
            mapping.addProperty("canonicalNullnessSolverTerm",
                    "sym__port__" + smtName(port)
                            + "__string_is_null");
            mapping.addProperty("nullableStringEncodingAuthority",
                    "JAVA_STRING_CONTENT_PLUS_EXPLICIT_NULLNESS_BOOL_V1");
        }
        mapping.addProperty("authority", "EMITTER_ACTUAL_TERM");
        return mapping;
    }

    private static void assertScalarInput(JsonObject input, String port,
                                          String descriptor,
                                          String solverSort,
                                          String suffix) {
        assertEquals(port, input.get("portId").getAsString());
        assertEquals(descriptor,
                input.get("javaTypeDescriptor").getAsString());
        assertEquals("sym__port__" + smtName(port) + "__" + suffix,
                input.get("solverTerm").getAsString());
        assertEquals(solverSort, input.get("solverSort").getAsString());
        if ("String".equals(solverSort)) {
            assertEquals("sym__port__" + smtName(port)
                            + "__string_is_null",
                    input.get("nullnessSolverTerm").getAsString());
            assertEquals("Bool",
                    input.get("nullnessSolverSort").getAsString());
        }
        assertTrue(input.get("root").getAsBoolean());
        assertFalse(input.get("upstreamSupplied").getAsBoolean());
        assertEquals("EXISTENTIALLY_QUANTIFIED_IN_BOOLEAN_PROJECTION",
                input.get("projectionRole").getAsString());
        assertEquals("STATIC_JAVA_SCALAR_PORT_PLUS_COMPOSED_SMT_CANONICAL_"
                        + "BINDING_AND_RUNTIME_RELATIONSHIP_DIRECTION_V1",
                input.get("authority").getAsString());
    }

    private static String solverTerm(String port) {
        return "sym__port__" + smtName(port) + "__int";
    }

    private static String smtName(String value) {
        return value.replaceAll("[^A-Za-z0-9_]", "_");
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
        private final String smt;
        private final JsonObject manifest;
        private final List<JsonObject> regions;
        private final JsonObject relationships;

        private Fixture(String smt, JsonObject manifest,
                        List<JsonObject> regions,
                        JsonObject relationships) {
            this.smt = smt;
            this.manifest = manifest;
            this.regions = regions;
            this.relationships = relationships;
        }
    }
}
