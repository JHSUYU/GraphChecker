package edu.uva.liftlab.graphchecker.concolic;

import java.util.Collections;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

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
                solver();

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.<JsonObject>emptyList(), solver,
                8, 64);

        assertEquals("CANDIDATE_READY",
                report.get("state").getAsString());
        assertEquals(1, report.getAsJsonObject("roots")
                .getAsJsonArray("existentialInputs").size());
        JsonArray models = report.getAsJsonArray(
                BooleanReachConditionExtractor.SYMBOLIC_VARIABLE_MODELS);
        assertEquals(models.toString(), 1, models.size());
        JsonObject model = models.get(0).getAsJsonObject();
        JsonObject witness = model.getAsJsonArray("variables")
                .get(0).getAsJsonObject();
        assertEquals("SOURCE.A", witness.get("sourceId").getAsString());
        assertEquals("node/dn0#1",
                witness.get("sourceKey").getAsString());
        assertEquals("node/dn0#1",
                witness.get("sourceOccurrenceId").getAsString());
        assertEquals(sourcePhase("SOURCE.A", "a"),
                witness.get("sourcePhaseId").getAsString());
        assertEquals("7", witness.get("value").getAsString());
        assertEquals(0, model.get("valuationOrdinal").getAsInt());
        // One base solve plus one rejected neighboring value.  Witness
        // extraction is part of the base query and does not repeat it.
        assertEquals(solver.attempts().toString(), 2,
                solver.attempts().size());
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
                solver();

        JsonObject sat = BooleanReachConditionExtractor.extract(
                "(assert true)\n(check-sat)\n", open,
                Collections.<JsonObject>emptyList(), solver, 8, 64);
        assertEquals("REACHABLE", sat.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());

        JsonObject unsat = BooleanReachConditionExtractor.extract(
                "(assert false)\n(check-sat)\n", open,
                Collections.<JsonObject>emptyList(),
                solver(), 8, 64);
        assertEquals("UNKNOWN", unsat.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());
        assertEquals("INCONCLUSIVE_OPEN_PATH_CLOSURE",
                unsat.getAsJsonObject("reachCondition")
                        .get("coverageConclusion").getAsString());
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

    private static BooleanReachConditionExtractor.Z3Solver solver()
            throws Exception {
        return new BooleanReachConditionExtractor.Z3Solver(
                "z3", 20_000L, new JsonArray(), 1);
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
