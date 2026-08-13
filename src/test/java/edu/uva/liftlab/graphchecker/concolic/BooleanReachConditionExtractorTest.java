package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Assume;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class BooleanReachConditionExtractorTest {
    @Test
    public void usesManifestCataloguedInvocationScopedBooleanTerm()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String instance = "REGION.3@Test#call7";
        String solverTerm =
                "sym__port__REGION_3_Test_call7_REGION_3_in_0__bool";
        String portTerm =
                "port__REGION_3_in_0__instance__REGION_3_Test_call7";
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VBool (valueBool Bool)))))\n"
                + "(declare-const " + solverTerm + " Bool)\n"
                + "(declare-const " + portTerm + " Value)\n"
                + "(assert (= " + portTerm + " (VBool "
                + solverTerm + ")))\n"
                + "(assert " + solverTerm + ")\n";

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest(instance, portTerm, solverTerm),
                Collections.singletonList(region()),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        assertEquals(report.toString(), "CANDIDATE_READY",
                report.get("state").getAsString());
        JsonArray roots = report.getAsJsonObject("roots")
                .getAsJsonArray("booleanInputs");
        assertEquals(1, roots.size());
        assertEquals(instance, roots.get(0).getAsJsonObject()
                .get("occurrenceId").getAsString());
        assertEquals(solverTerm, roots.get(0).getAsJsonObject()
                .get("solverTerm").getAsString());
        assertEquals("unsat", report.getAsJsonArray("valuations").get(0)
                .getAsJsonObject().get("status").getAsString());
        assertEquals("sat", report.getAsJsonArray("valuations").get(1)
                .getAsJsonObject().get("status").getAsString());
    }

    @Test
    public void missingOccurrenceCatalogIsAnExplicitGap() throws Exception {
        JsonObject manifest = manifest("", "", "");
        manifest.remove("portOccurrences");
        JsonObject report = BooleanReachConditionExtractor.extract(
                "(set-logic ALL)\n", manifest,
                Collections.singletonList(region()),
                null, 4, 16);

        assertEquals("CANDIDATE_WITH_GAPS",
                report.get("state").getAsString());
        assertTrue(report.getAsJsonArray("gaps").toString(),
                report.getAsJsonArray("gaps").toString().contains(
                        "PORT_OCCURRENCES_MISSING"));
    }

    @Test
    public void discoversLongRootThroughCanonicalVLongBinding()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String instance = "REGION.3@Test#call8";
        String solverTerm =
                "sym__port__REGION_3_Test_call8_REGION_3_in_0__int";
        String portTerm =
                "port__REGION_3_in_0__instance__REGION_3_Test_call8";
        JsonObject manifest = manifest(instance, portTerm, solverTerm);
        manifest.getAsJsonArray("portOccurrences").get(0)
                .getAsJsonObject().addProperty("sort", "INT");
        JsonObject input = region().getAsJsonArray("symbolicInputs").get(0)
                .getAsJsonObject();
        input.addProperty("javaType", "long");
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VLong (valueLong Int)))))\n"
                + "(declare-const " + solverTerm + " Int)\n"
                + "(declare-const " + portTerm + " Value)\n"
                + "(assert (= " + portTerm + " (VLong "
                + solverTerm + ")))\n";

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.singletonList(regionWith(input)),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        JsonArray roots = report.getAsJsonObject("roots")
                .getAsJsonArray("existentialInputs");
        assertEquals(1, roots.size());
        assertEquals("J", roots.get(0).getAsJsonObject()
                .get("javaTypeDescriptor").getAsString());
    }

    @Test
    public void observedPathCandidateCanBeCheckedWithoutBecomingClosedProof()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = manifest("", "", "");
        manifest.addProperty("trustState", "OBSERVED_PATH_UNDERAPPROX");
        manifest.addProperty("compositionMode",
                "EXISTENTIAL_OBSERVED_PATHS");
        manifest.addProperty("pathSetComplete", false);

        JsonObject report = BooleanReachConditionExtractor.extract(
                "(set-logic ALL)\n(assert true)\n", manifest,
                Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        assertEquals("REACHABLE", report.getAsJsonObject("reachCondition")
                .get("reachability").getAsString());
        assertEquals("OBSERVED_PATH_UNDERAPPROX",
                report.get("trustState").getAsString());
        // No root is no freedom, so there is nothing the condition could be
        // a tautology over.  That is not the degenerate answer, and it is
        // named rather than left to look like a check that ran clean.
        assertEquals(report.toString(), "NOT_APPLICABLE_NO_FREE_ROOTS",
                degeneracyCheck(report));
    }

    @Test
    public void observedUnsatIsInconclusive() throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = manifest("", "", "");
        manifest.addProperty("trustState", "OBSERVED_PATH_UNDERAPPROX");
        manifest.addProperty("compositionMode",
                "EXISTENTIAL_OBSERVED_PATHS");
        manifest.addProperty("pathSetComplete", false);

        JsonObject report = BooleanReachConditionExtractor.extract(
                "(set-logic ALL)\n(assert false)\n", manifest,
                Collections.<JsonObject>emptyList(),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        assertEquals("CANDIDATE_READY", report.get("state").getAsString());
        JsonObject reach = report.getAsJsonObject("reachCondition");
        assertEquals("UNKNOWN", reach.get("reachability").getAsString());
        assertEquals("INCONCLUSIVE_UNDERAPPROXIMATION",
                reach.get("coverageConclusion").getAsString());
    }

    /**
     * A refused Boolean valuation proves the condition cuts the root space.
     */
    @Test
    public void aRefusedValuationDecidesTheConditionConstrains()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject report = booleanRootReport("(assert " + BOOL_TERM + ")\n");

        assertEquals(report.toString(), "CONSTRAINED_ROOT_SPACE",
                degeneracyCheck(report));
    }

    /**
     * Every point of a finite root space admitted is the degenerate answer,
     * and it is the one shape the exhaustive table can prove.
     */
    @Test
    public void anEntirelyAdmittedFiniteRootSpaceIsDegenerate()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject report = booleanRootReport("");

        assertEquals(report.toString(), "true",
                report.getAsJsonObject("reachCondition")
                        .get("formula").getAsString());
        assertEquals(report.toString(),
                "DEGENERATE_UNCONSTRAINED_ROOT_SPACE",
                degeneracyCheck(report));
    }

    /**
     * An unsupplied input this report cannot decode is a freedom it never
     * enumerated, so the space was not covered whole and the degenerate
     * verdict is not available - even though every Boolean valuation reached.
     */
    @Test
    public void anUndecodableFreedomBlocksTheExhaustiveClaim()
            throws Exception {
        Assume.assumeTrue(z3Available());
        JsonObject manifest = manifest("REGION.3@Test#call7", BOOL_PORT_TERM,
                BOOL_TERM);
        JsonObject opaque = new JsonObject();
        opaque.addProperty("portId", "REGION.3.in.1");
        opaque.addProperty("occurrenceId", "source0#epoch0/region/REGION.3#1");
        opaque.addProperty("sort", "REF");
        opaque.addProperty("portTerm", "port__REGION_3_in_1");
        opaque.addProperty("solverTerm", "sym__port__REGION_3_in_1__ref");
        manifest.getAsJsonArray("portOccurrences").add(opaque);
        JsonObject region = region();
        JsonObject reference = new JsonObject();
        reference.addProperty("portId", "REGION.3.in.1");
        reference.addProperty("javaType", "java.lang.Object");
        region.getAsJsonArray("symbolicInputs").add(reference);
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VBool (valueBool Bool)))))\n"
                + "(declare-const " + BOOL_TERM + " Bool)\n"
                + "(declare-const " + BOOL_PORT_TERM + " Value)\n"
                + "(assert (= " + BOOL_PORT_TERM + " (VBool "
                + BOOL_TERM + ")))\n";

        JsonObject report = BooleanReachConditionExtractor.extract(smt,
                manifest, Collections.singletonList(region),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        assertEquals(report.toString(), "true",
                report.getAsJsonObject("reachCondition")
                        .get("formula").getAsString());
        assertEquals(report.toString(),
                "UNDECIDED_UNMODELLED_INPUT_FREEDOMS:1",
                degeneracyCheck(report));
    }

    /**
     * A surviving existential root leaves the space infinite, so the constant
     * "true" is the DNF's arity and decides nothing.  The check says it could
     * not decide instead of passing, and the formula it read is unchanged.
     */
    @Test
    public void anExistentialRootLeavesTheQuestionUndecidedNotPassed()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String instance = "REGION.3@Test#call8";
        String solverTerm =
                "sym__port__REGION_3_Test_call8_REGION_3_in_0__int";
        String portTerm =
                "port__REGION_3_in_0__instance__REGION_3_Test_call8";
        JsonObject manifest = manifest(instance, portTerm, solverTerm);
        manifest.getAsJsonArray("portOccurrences").get(0)
                .getAsJsonObject().addProperty("sort", "INT");
        JsonObject input = region().getAsJsonArray("symbolicInputs").get(0)
                .getAsJsonObject();
        input.addProperty("javaType", "long");
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VLong (valueLong Int)))))\n"
                + "(declare-const " + solverTerm + " Int)\n"
                + "(declare-const " + portTerm + " Value)\n"
                + "(assert (= " + portTerm + " (VLong "
                + solverTerm + ")))\n";

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.singletonList(regionWith(input)),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        // The baseline candidate's exact shape: no Boolean root, so the
        // formula is "true" and values is empty by arity, with one
        // existential root surviving.
        assertEquals(report.toString(), 0, report.getAsJsonObject("roots")
                .getAsJsonArray("booleanInputs").size());
        assertEquals(report.toString(), "true",
                report.getAsJsonObject("reachCondition")
                        .get("formula").getAsString());
        assertEquals(report.toString(), 0,
                report.getAsJsonArray("valuations").get(0).getAsJsonObject()
                        .getAsJsonArray("values").size());
        assertEquals(report.toString(),
                "UNDECIDED_UNENUMERATED_EXISTENTIAL_ROOTS:1",
                degeneracyCheck(report));
    }

    /**
     * One rejected neighboring scalar assignment is a finite proof that the
     * existential root space is constrained; it does not require pretending
     * to enumerate every Java long value.
     */
    @Test
    public void rejectedExistentialNeighborProvesRootSpaceIsConstrained()
            throws Exception {
        Assume.assumeTrue(z3Available());
        String instance = "REGION.3@Test#call8";
        String solverTerm =
                "sym__port__REGION_3_Test_call8_REGION_3_in_0__int";
        String portTerm =
                "port__REGION_3_in_0__instance__REGION_3_Test_call8";
        JsonObject manifest = manifest(instance, portTerm, solverTerm);
        manifest.getAsJsonArray("portOccurrences").get(0)
                .getAsJsonObject().addProperty("sort", "INT");
        JsonObject input = region().getAsJsonArray("symbolicInputs").get(0)
                .getAsJsonObject();
        input.addProperty("javaType", "long");
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VLong (valueLong Int)))))\n"
                + "(declare-const " + solverTerm + " Int)\n"
                + "(declare-const " + portTerm + " Value)\n"
                + "(assert (= " + portTerm + " (VLong "
                + solverTerm + ")))\n"
                + "(assert (= " + solverTerm + " 7))\n";

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest, Collections.singletonList(regionWith(input)),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        assertEquals(report.toString(), "CONSTRAINED_ROOT_SPACE",
                degeneracyCheck(report));
        JsonObject probe = report.getAsJsonObject("existentialRootProbe");
        assertEquals(report.toString(),
                "SOLVER_WITNESS_NEIGHBOR_PERTURBATION_V1",
                probe.get("authority").getAsString());
        assertTrue(report.toString(),
                probe.get("constrainsRootSpace").getAsBoolean());
        assertTrue(report.toString(), probe.getAsJsonArray("perturbations")
                .toString().contains("\"status\":\"unsat\""));
    }

    /**
     * The verdict is read off the table the report already computed, so the
     * SMT it was computed from is untouched and every field that existed
     * before still reads the same.
     */
    @Test
    public void publishingTheVerdictChangesNothingItRead() throws Exception {
        Assume.assumeTrue(z3Available());
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VBool (valueBool Bool)))))\n"
                + "(declare-const " + BOOL_TERM + " Bool)\n"
                + "(declare-const " + BOOL_PORT_TERM + " Value)\n"
                + "(assert (= " + BOOL_PORT_TERM + " (VBool "
                + BOOL_TERM + ")))\n"
                + "(assert " + BOOL_TERM + ")\n";
        String before = smt;

        JsonObject report = BooleanReachConditionExtractor.extract(
                smt, manifest("REGION.3@Test#call7", BOOL_PORT_TERM,
                        BOOL_TERM),
                Collections.singletonList(region()),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);

        assertEquals(before, smt);
        JsonObject reach = report.getAsJsonObject("reachCondition")
                .deepCopy();
        reach.remove("degeneracyCheck");
        assertEquals("{\"formula\":\"(= " + BOOL_TERM + " true)\","
                + "\"reachability\":\"REACHABLE\"}", reach.toString());
    }

    private static final String BOOL_TERM =
            "sym__port__REGION_3_Test_call7_REGION_3_in_0__bool";
    private static final String BOOL_PORT_TERM =
            "port__REGION_3_in_0__instance__REGION_3_Test_call7";

    private static String degeneracyCheck(JsonObject report) {
        return report.getAsJsonObject("reachCondition")
                .get("degeneracyCheck").getAsString();
    }

    private static JsonObject booleanRootReport(String extraAssertion)
            throws Exception {
        String smt = "(set-logic ALL)\n"
                + "(declare-datatypes () ((Value"
                + " (VBool (valueBool Bool)))))\n"
                + "(declare-const " + BOOL_TERM + " Bool)\n"
                + "(declare-const " + BOOL_PORT_TERM + " Value)\n"
                + "(assert (= " + BOOL_PORT_TERM + " (VBool "
                + BOOL_TERM + ")))\n" + extraAssertion;
        return BooleanReachConditionExtractor.extract(smt,
                manifest("REGION.3@Test#call7", BOOL_PORT_TERM, BOOL_TERM),
                Collections.singletonList(region()),
                new BooleanReachConditionExtractor.Z3Solver("z3", 5_000L),
                4, 16);
    }

    private static JsonObject manifest(String instance, String portTerm,
                                       String solverTerm) {
        JsonObject result = new JsonObject();
        result.addProperty("schemaVersion", 2);
        result.addProperty("kind", "CONCOLIC_COMPOSED_SMT");
        result.addProperty("state", "CANDIDATE_READY");
        result.addProperty("trustState", "CANDIDATE_ONLY");
        result.add("suppliedInputs", new JsonArray());
        JsonArray occurrences = new JsonArray();
        if (!instance.isEmpty()) {
            JsonObject occurrence = new JsonObject();
            occurrence.addProperty("portId", "REGION.3.in.0");
            occurrence.addProperty("occurrenceId", instance);
            occurrence.addProperty("sort", "BOOL");
            occurrence.addProperty("portTerm", portTerm);
            occurrence.addProperty("solverTerm", solverTerm);
            occurrences.add(occurrence);
        }
        result.add("portOccurrences", occurrences);
        return result;
    }

    private static JsonObject region() {
        JsonObject input = new JsonObject();
        input.addProperty("portId", "REGION.3.in.0");
        input.addProperty("javaType", "boolean");
        return regionWith(input);
    }

    private static JsonObject regionWith(JsonObject input) {
        JsonArray inputs = new JsonArray();
        inputs.add(input);
        JsonObject region = new JsonObject();
        region.addProperty("regionId", "REGION.3");
        region.add("symbolicInputs", inputs);
        return region;
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
