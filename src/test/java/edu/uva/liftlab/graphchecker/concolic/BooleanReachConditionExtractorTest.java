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
            bindCliArtifacts(fixture.manifest, fixture.relationships,
                    smt, regions, relationships);
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
        assertEquals("COMPLETE_EXACT_BOOLEAN_REACH_CONDITION",
                report.get("status").getAsString());
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
    public void incompleteCompositionFailsBeforeAnySolverInvocation()
            throws Exception {
        Fixture fixture = fixture();
        fixture.manifest.addProperty("complete", false);
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
                        "COMPOSITION_MANIFEST_NOT_COMPLETE_AND_ELIGIBLE"));
    }

    @Test
    public void bootstrapCompositionCannotBeReportedAsFinalReachCondition()
            throws Exception {
        Fixture fixture = fixture();
        fixture.manifest.addProperty("compositionStage", "BOOTSTRAP");
        fixture.manifest.addProperty("structurallyComplete", true);
        fixture.manifest.addProperty("eligibleForBootstrapModel", true);
        fixture.manifest.addProperty("fatalReplayValidated", false);
        fixture.manifest.addProperty("complete", false);
        fixture.manifest.addProperty(
                "eligibleToReportAutomaticRelationship", false);
        fixture.relationships.addProperty("compositionStage", "BOOTSTRAP");
        fixture.relationships.addProperty("structurallyComplete", true);
        fixture.relationships.addProperty("fatalReplayValidated", false);
        fixture.relationships.addProperty("eligibleForBootstrapModel", true);
        fixture.relationships.addProperty(
                "eligibleForAutomaticVerification", false);
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
        assertTrue(extraction.report.getAsJsonArray("discoveryGaps")
                .toString().contains(
                        "COMPOSITION_MANIFEST_NOT_COMPLETE_AND_ELIGIBLE"));
    }

    @Test
    public void finalReportRejectsNonFinalRelationshipCatalog()
            throws Exception {
        Fixture fixture = fixture();
        fixture.relationships.addProperty("compositionStage", "BOOTSTRAP");
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
        assertTrue(extraction.report.getAsJsonArray("discoveryGaps")
                .toString().contains(
                        "RELATIONSHIP_CATALOG_NOT_COMPLETE_AND_ELIGIBLE"));
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
            bindCliArtifacts(fixture.manifest, fixture.relationships,
                    smt, regions, relationships);
            byte[] exactRelationships = fixture.relationships.toString()
                    .getBytes(StandardCharsets.UTF_8);
            Files.write(relationships, exactRelationships);
            fixture.manifest.add("relationshipCandidatesArtifact",
                    BooleanReachConditionExtractor.artifact(relationships));

            BooleanReachConditionExtractor.validateArtifactBindings(smt,
                    regions, relationships, fixture.manifest,
                    fixture.relationships);

            Files.write(smt, (fixture.smt + "; cross-wired\n").getBytes(
                    StandardCharsets.UTF_8));
            assertArtifactRejected(smt, regions, relationships,
                    fixture.manifest, fixture.relationships);
            Files.write(smt, exactSmt);

            Files.write(regions, (regionLines + "{}\n").getBytes(
                    StandardCharsets.UTF_8));
            assertArtifactRejected(smt, regions, relationships,
                    fixture.manifest, fixture.relationships);
            Files.write(regions, exactRegions);

            JsonObject otherRelationships = fixture.relationships.deepCopy();
            otherRelationships.addProperty("candidateCount", 99);
            Files.write(relationships, otherRelationships.toString().getBytes(
                    StandardCharsets.UTF_8));
            assertArtifactRejected(smt, regions, relationships,
                    fixture.manifest, otherRelationships);
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
    public void booleanRootMustHaveExactlyOneMappingInEveryRegionCase()
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
                                    .SolverResult("sat", "sat");
                        }, 8, 256);

        assertFalse(extraction.report.get("complete").getAsBoolean());
        assertEquals(0, invocations[0]);
        assertTrue(extraction.report.getAsJsonArray("discoveryGaps")
                .toString().contains(
                        "BOOLEAN_CASE_MAPPING_COVERAGE_MISMATCH:"
                                + "ROOT.A.in.0:2"));
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

    private static void bindCliArtifacts(JsonObject manifest,
                                         JsonObject relationships,
                                         Path smt, Path regions,
                                         Path relationshipPath)
            throws Exception {
        JsonObject smtArtifact = BooleanReachConditionExtractor.artifact(smt);
        JsonObject regionsArtifact =
                BooleanReachConditionExtractor.artifact(regions);
        JsonObject sourceArtifact = smtArtifact.deepCopy();
        JsonArray summaries = new JsonArray();
        summaries.add(sourceArtifact.deepCopy());
        for (JsonObject target : Arrays.asList(manifest, relationships)) {
            target.addProperty("artifactBindingAuthority",
                    "COMPOSER_EXACT_CLI_INPUT_AND_OUTPUT_SHA256_V1");
            target.add("composedSmtArtifact", smtArtifact.deepCopy());
            target.add("staticRegionsArtifact", regionsArtifact.deepCopy());
            target.add("fatalQueriesArtifact", sourceArtifact.deepCopy());
            target.add("symbolicMergePlanArtifact",
                    sourceArtifact.deepCopy());
            target.add("summaryInputArtifacts", summaries.deepCopy());
            target.addProperty("fatalRegion", "REGION.F");
            target.addProperty("fatalActivation", "ACT.F");
            target.addProperty("fatalRegionInstanceId", "INSTANCE.F");
            target.addProperty("fatalOccurrence", 1);
            target.addProperty("fatalDesiredOutcome", true);
            target.addProperty("validatedSummaryId", "SUMMARY.F");
        }
        String bindingId = BooleanReachConditionExtractor
                .compositionBindingId(manifest);
        manifest.addProperty("compositionBindingId", bindingId);
        relationships.addProperty("compositionBindingId", bindingId);
        relationships.addProperty("baseSmt",
                smt.toAbsolutePath().normalize().toString());
        relationships.addProperty("baseSmtSha256",
                smtArtifact.get("sha256").getAsString());
        relationships.addProperty("baseSmtSizeBytes",
                smtArtifact.get("sizeBytes").getAsLong());
        manifest.addProperty("relationshipCandidates",
                relationshipPath.toAbsolutePath().normalize().toString());
    }

    private static void assertArtifactRejected(Path smt, Path regions,
                                               Path relationshipsPath,
                                               JsonObject manifest,
                                               JsonObject relationships)
            throws Exception {
        boolean rejected = false;
        try {
            BooleanReachConditionExtractor.validateArtifactBindings(smt,
                    regions, relationshipsPath, manifest, relationships);
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
        manifest.addProperty("compositionStage", "VALIDATED_FINAL");
        manifest.addProperty("structurallyComplete", true);
        manifest.addProperty("complete", true);
        manifest.addProperty("fatalReplayValidated", true);
        manifest.addProperty("eligibleForBootstrapModel", false);
        manifest.addProperty("eligibleToReportAutomaticRelationship", true);
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
        relationships.addProperty("compositionStage", "VALIDATED_FINAL");
        relationships.addProperty("structurallyComplete", true);
        relationships.addProperty("fatalReplayValidated", true);
        relationships.addProperty("eligibleForBootstrapModel", false);
        relationships.addProperty("eligibleForAutomaticVerification", true);
        JsonObject relation = new JsonObject();
        JsonObject roles = new JsonObject();
        roles.addProperty("left", output);
        roles.addProperty("right", supplied);
        relation.add("roles", roles);
        JsonArray relationshipRows = new JsonArray();
        relationshipRows.add(relation);
        relationships.add("relationships", relationshipRows);
        relationships.addProperty("candidateCount", relationshipRows.size());

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
