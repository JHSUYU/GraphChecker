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
            Files.write(manifest, fixture.manifest.toString().getBytes(
                    StandardCharsets.UTF_8));
            StringBuilder regionLines = new StringBuilder();
            for (JsonObject region : fixture.regions) {
                regionLines.append(region).append('\n');
            }
            Files.write(regions, regionLines.toString().getBytes(
                    StandardCharsets.UTF_8));
            Files.write(relationships, fixture.relationships.toString()
                    .getBytes(StandardCharsets.UTF_8));

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
        manifest.addProperty("complete", true);
        manifest.addProperty("fatalReplayValidated", true);
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
