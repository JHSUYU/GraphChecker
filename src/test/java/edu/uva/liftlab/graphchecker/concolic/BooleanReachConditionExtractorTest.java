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
                .get("regionInstanceId").getAsString());
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
        manifest.remove("canonicalPortOccurrences");
        JsonObject report = BooleanReachConditionExtractor.extract(
                "(set-logic ALL)\n", manifest,
                Collections.singletonList(region()),
                null, 4, 16);

        assertEquals("CANDIDATE_WITH_GAPS",
                report.get("state").getAsString());
        assertTrue(report.getAsJsonArray("gaps").toString(),
                report.getAsJsonArray("gaps").toString().contains(
                        "CANONICAL_PORT_OCCURRENCE_CATALOG_MISSING"));
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
        manifest.getAsJsonArray("canonicalPortOccurrences").get(0)
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
            occurrence.addProperty("regionInstanceId", instance);
            occurrence.addProperty("sort", "BOOL");
            occurrence.addProperty("portTerm", portTerm);
            occurrence.addProperty("solverTerm", solverTerm);
            occurrences.add(occurrence);
        }
        result.add("canonicalPortOccurrences", occurrences);
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
