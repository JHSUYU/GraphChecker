package edu.uva.liftlab.graphchecker.concolic;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class BooleanReachConditionExtractorSolverTest {

    @Test
    public void configuredLongSourceIsPublishedWithItsSolverWitness()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray sources = new JsonArray();
        sources.add(configuredLong("SOURCE.A", "node/dn0#1",
                "<DataNode: long a>", "source__a"));
        manifest.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, sources);
        String smt = "(set-logic ALL)\n"
                + "(declare-const source__a Int)\n"
                + "(assert (= source__a 7))\n"
                + "(check-sat)\n";
        BooleanReachConditionExtractor.Z3Solver solver =
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L);

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.<JsonObject>emptyList(), solver,
                8, 64);

        assertEquals("CANDIDATE_READY",
                report.get("state").getAsString());
        assertEquals(1, report.getAsJsonObject("roots")
                .getAsJsonArray("existentialInputs").size());
        JsonObject witness = report.getAsJsonArray("valuations")
                .get(0).getAsJsonObject()
                .getAsJsonArray("configuredSourceWitness")
                .get(0).getAsJsonObject();
        assertEquals("SOURCE.A", witness.get("sourceId").getAsString());
        assertEquals("node/dn0#1",
                witness.get("sourceKey").getAsString());
        assertEquals("node/dn0#1",
                witness.get("sourceOccurrenceId").getAsString());
        assertEquals(sourcePhase("SOURCE.A", "a"),
                witness.get("sourcePhaseId").getAsString());
        assertEquals("7", witness.get("value").getAsString());
        JsonArray models = report.getAsJsonArray(
                BooleanReachConditionExtractor.SYMBOLIC_VARIABLE_MODELS);
        assertEquals(models.toString(), 1, models.size());
        JsonObject model = models.get(0).getAsJsonObject();
        assertEquals(0, model.get("valuationOrdinal").getAsInt());
        assertEquals(witness,
                model.getAsJsonArray("variables").get(0).getAsJsonObject());
        // One base solve plus one rejected neighboring value.  Witness
        // extraction is part of the base query and does not repeat it.
        assertEquals(solver.attempts().toString(), 2,
                solver.attempts().size());
    }

    @Test
    public void tracingSourceKeysDistinguishEveryPrintedSymbolicVariable()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray sources = new JsonArray();
        sources.add(configuredLong("RPC_COMPARE.A",
                "cluster/dn0#epoch0", "<DataNode: long a>",
                "source__a"));
        sources.add(configuredLong("RPC_COMPARE.B",
                "cluster/dn1#epoch0", "<DataNode: long b>",
                "source__b"));
        manifest.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, sources);
        String smt = "(set-logic ALL)\n"
                + "(declare-const source__a Int)\n"
                + "(declare-const source__b Int)\n"
                + "(assert (= source__a 7))\n"
                + "(assert (= source__b 9))\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L), 8, 64);

        JsonArray models = report.getAsJsonArray(
                BooleanReachConditionExtractor.SYMBOLIC_VARIABLE_MODELS);
        assertEquals(models.toString(), 1, models.size());
        JsonArray variables = models.get(0).getAsJsonObject()
                .getAsJsonArray("variables");
        assertEquals(variables.toString(), 2, variables.size());
        JsonObject a = variables.get(0).getAsJsonObject();
        JsonObject b = variables.get(1).getAsJsonObject();
        assertEquals("cluster/dn0#epoch0",
                a.get("sourceKey").getAsString());
        assertEquals("RPC_COMPARE.A", a.get("sourceId").getAsString());
        assertEquals("7", a.get("value").getAsString());
        assertTrue(a.get("displayName").getAsString().startsWith(
                "cluster/dn0#epoch0::RPC_COMPARE.A::SOURCE_PHASE."));
        assertEquals("cluster/dn1#epoch0",
                b.get("sourceKey").getAsString());
        assertEquals("RPC_COMPARE.B", b.get("sourceId").getAsString());
        assertEquals("9", b.get("value").getAsString());
    }

    @Test
    public void twoPhasesOfOneSourceBecomeTwoReachabilityRoots()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = candidateManifest();
        JsonArray sources = new JsonArray();
        sources.add(configuredLong("SOURCE.A", "node/dn0#1",
                "<DataNode: long a>", "source__a"));
        JsonObject second = configuredLong("SOURCE.A", "node/dn0#1",
                "<DataNode: long a>", "source__b");
        second.addProperty("sourcePhaseId", sourcePhase("SOURCE.A", "b"));
        sources.add(second);
        manifest.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, sources);
        String smt = "(set-logic ALL)\n"
                + "(declare-const source__a Int)\n"
                + "(declare-const source__b Int)\n"
                + "(assert (= source__a 7))\n"
                + "(assert (= source__b 9))\n"
                + "(check-sat)\n";

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L), 8, 64);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        JsonArray roots = report.getAsJsonObject("roots")
                .getAsJsonArray("existentialInputs");
        assertEquals(2, roots.size());
        assertTrue(roots.toString(), roots.toString().contains(
                sourcePhase("SOURCE.A", "a")));
        assertTrue(roots.toString(), roots.toString().contains(
                sourcePhase("SOURCE.A", "b")));
    }

    @Test
    public void missingOrUndeclaredConfiguredSourceCatalogFailsClosed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject missing = candidateManifest();
        JsonObject missingReport = BooleanReachConditionExtractor.extract(
                "(check-sat)\n", missing,
                Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L), 8, 64);
        assertEquals("CANDIDATE_WITH_GAPS",
                missingReport.get("state").getAsString());
        assertTrue(missingReport.getAsJsonArray("gaps").toString(),
                missingReport.getAsJsonArray("gaps").toString().contains(
                        "CONFIGURED_SOURCE_MATERIALIZATIONS_MISSING"));

        JsonObject undeclared = candidateManifest();
        JsonArray sources = new JsonArray();
        sources.add(configuredLong("SOURCE.A", "node/dn0#1",
                "<DataNode: long a>", "source__absent"));
        undeclared.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, sources);
        JsonObject undeclaredReport =
                BooleanReachConditionExtractor.extract(
                        "(check-sat)\n", undeclared,
                        Collections.<JsonObject>emptyList(),
                        new BooleanReachConditionExtractor.Z3Solver(
                                "z3", 20_000L), 8, 64);
        assertEquals("CANDIDATE_WITH_GAPS",
                undeclaredReport.get("state").getAsString());
        assertTrue(undeclaredReport.getAsJsonArray("gaps").toString(),
                undeclaredReport.getAsJsonArray("gaps").toString().contains(
                        "CONFIGURED_SOURCE_TERM_NOT_DECLARED"));

        JsonObject missingPhase = candidateManifest();
        JsonObject missingPhaseRow = configuredLong("SOURCE.A",
                "node/dn0#1", "<DataNode: long a>", "source__a");
        missingPhaseRow.remove("sourcePhaseId");
        JsonArray missingPhaseSources = new JsonArray();
        missingPhaseSources.add(missingPhaseRow);
        missingPhase.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD,
                missingPhaseSources);
        JsonObject missingPhaseReport =
                BooleanReachConditionExtractor.extract(
                        "(declare-const source__a Int)\n(check-sat)\n",
                        missingPhase,
                        Collections.<JsonObject>emptyList(),
                        new BooleanReachConditionExtractor.Z3Solver(
                                "z3", 20_000L), 8, 64);
        assertEquals("CANDIDATE_WITH_GAPS",
                missingPhaseReport.get("state").getAsString());
        assertTrue(missingPhaseReport.getAsJsonArray("gaps").toString(),
                missingPhaseReport.getAsJsonArray("gaps").toString()
                        .contains("CONFIGURED_SOURCE_MATERIALIZATION_MALFORMED"));
    }

    @Test
    public void openPathClosureAllowsSatButCannotProveUnsat()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject open = candidateManifest();
        open.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, new JsonArray());
        addUnsatClosure(open, false, true, false);
        BooleanReachConditionExtractor.Z3Solver solver =
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L);

        JsonObject sat = BooleanReachConditionExtractor.extract(
                "(assert true)\n(check-sat)\n", open,
                Collections.<JsonObject>emptyList(), solver, 8, 64);
        assertEquals("REACHABLE", sat.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());

        JsonObject unsat = BooleanReachConditionExtractor.extract(
                "(assert false)\n(check-sat)\n", open,
                Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L), 8, 64);
        assertEquals("UNKNOWN", unsat.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());
        assertEquals("INCONCLUSIVE_OPEN_PATH_CLOSURE",
                unsat.getAsJsonObject("reachCondition")
                        .get("coverageConclusion").getAsString());
    }

    @Test
    public void onlyClosedSelectedModelCanPublishUnreachable()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject closed = candidateManifest();
        closed.add(ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_FIELD, new JsonArray());
        addUnsatClosure(closed, true, true, true);

        JsonObject report = BooleanReachConditionExtractor.extract(
                "(assert false)\n(check-sat)\n", closed,
                Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver(
                        "z3", 20_000L), 8, 64);

        assertEquals("UNREACHABLE", report.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());
        assertTrue(report.get(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE)
                .getAsBoolean());
    }

    @Test
    public void tunedProbeTimeoutFallsBackToTheDefaultStrategy()
            throws Exception {
        Path fake = Files.createTempFile("causynth-z3-portfolio", ".sh");
        try {
            Files.write(fake, ("#!/bin/sh\n"
                    + "query=$(cat)\n"
                    + "case \"$query\" in\n"
                    + "  *':smt.auto_config false'*) sleep 1 ;;\n"
                    + "  *) echo sat ;;\n"
                    + "esac\n").getBytes(StandardCharsets.UTF_8));
            assertTrue(fake.toFile().setExecutable(true));
            BooleanReachConditionExtractor.Z3Solver solver =
                    new BooleanReachConditionExtractor.Z3Solver(
                            fake.toString(), 50L);

            assertEquals("sat", solver.check("(check-sat)\n").status());
            JsonArray attempts = solver.attempts();
            assertEquals(attempts.toString(), 2, attempts.size());
            assertEquals("timeout", attempts.get(0).getAsJsonObject()
                    .get("status").getAsString());
            assertEquals("sat", attempts.get(1).getAsJsonObject()
                    .get("status").getAsString());
            assertEquals("DEFAULT_SEED_7",
                    attempts.get(1).getAsJsonObject().get("strategy")
                            .getAsString());
            assertEquals(attempts.get(0).getAsJsonObject()
                            .get("baseQuerySha256").getAsString(),
                    attempts.get(1).getAsJsonObject()
                            .get("baseQuerySha256").getAsString());
            assertEquals(50L, attempts.get(1).getAsJsonObject()
                    .get("timeoutMillis").getAsLong());
        } finally {
            Files.deleteIfExists(fake);
        }
    }

    private static JsonObject candidateManifest() {
        JsonObject manifest = new JsonObject();
        manifest.addProperty("schemaVersion", 2);
        manifest.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        manifest.addProperty("state", "CANDIDATE_READY");
        manifest.addProperty("recordedModelComplete", true);
        manifest.addProperty(ConcolicSmtComposer.FINAL_STATUS,
                ConcolicSmtComposer.FINAL_READY);
        manifest.add("portOccurrences", new JsonArray());
        return manifest;
    }

    private static void addUnsatClosure(JsonObject manifest,
                                        boolean complete,
                                        boolean producerClosed,
                                        boolean targetClosed) {
        JsonObject evidence = new JsonObject();
        evidence.addProperty("schemaVersion", 1);
        evidence.addProperty("kind", "UNSAT_CLOSURE_EVIDENCE");
        evidence.addProperty("authority",
                ConcolicSmtComposer.UNSAT_CLOSURE_AUTHORITY);
        evidence.addProperty("recordedModelComplete", true);
        evidence.addProperty("producerPathsClosed", producerClosed);
        evidence.addProperty("targetPathsClosed", targetClosed);
        evidence.addProperty("compositionCoverageClosed", targetClosed);
        evidence.addProperty("finalStatusReady", true);
        evidence.addProperty("targetCoverageGapCount",
                targetClosed ? 0 : 1);
        evidence.addProperty("compositionCoverageGapCount",
                targetClosed ? 0 : 1);
        JsonArray partial = new JsonArray();
        if (!producerClosed) partial.add("SUMMARY.PARTIAL");
        evidence.add("partialProducerSummaryIds", partial);
        evidence.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE,
                complete);
        manifest.addProperty(ConcolicSmtComposer.UNSAT_CLOSURE_COMPLETE,
                complete);
        manifest.add(ConcolicSmtComposer.UNSAT_CLOSURE_EVIDENCE, evidence);
    }

    private static JsonObject configuredLong(
            String sourceId, String occurrence, String field,
            String solverTerm) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_KIND);
        row.addProperty("authority", ConcolicSmtComposer
                .CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY);
        row.addProperty("sourceKey", occurrence);
        row.addProperty("sourceId", sourceId);
        row.addProperty("sourcePhaseId", sourcePhase(sourceId, "a"));
        row.addProperty("sourceOccurrenceId", occurrence);
        row.addProperty("fieldSignature", field);
        row.addProperty("javaTypeDescriptor", "J");
        row.addProperty("sort", "INT");
        row.addProperty("smtSort", "Int");
        row.addProperty("solverTerm", solverTerm);
        return row;
    }

    private static String sourcePhase(String sourceId, String suffix) {
        return "SOURCE_PHASE." + CanonicalJson.sha256(sourceId + "\n"
                + suffix).substring(0, 16);
    }

    private static boolean z3Available() {
        try {
            Process process = new ProcessBuilder("z3", "-version").start();
            return process.waitFor() == 0;
        } catch (Exception unavailable) {
            return false;
        }
    }
}
