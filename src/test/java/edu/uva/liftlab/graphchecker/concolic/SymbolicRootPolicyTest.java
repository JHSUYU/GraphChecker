package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Which proposed roots an experiment's declaration file admits.
 *
 * <p>The automatic mechanisms propose far more roots than any chain needs --
 * on the HDFS block-key workloads every {@code Timer.now()} return -- so the
 * file is a restrictive allowlist over them.  Two authorities are exempt: a
 * source hook's own field, and a fault marker the workload wrote into its own
 * program text.</p>
 */
public class SymbolicRootPolicyTest {

    private static final String NN = "REGION.nn";
    private static final String DN = "REGION.dn";
    private static final String CLOCK_CELL =
            "<org.apache.hadoop.util.Timer: long now()>.return";
    private static final String KEY_ID =
            "<org.apache.hadoop.security.token.delegation.DelegationKey:"
                    + " int keyId>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void absentFileLeavesEveryProposedRootSymbolic() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(null, catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertEquals(Arrays.asList("SYMBOLIC", "SYMBOLIC", "SYMBOLIC"),
                modes(selected));
        assertEquals(0, selection.suppressedRootCandidates().size());
    }

    @Test
    public void declaredFileConcretizesTheUndeclaredAutomaticRoot()
            throws Exception {
        // The clock is declared for this region; the keyId field is not.
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertEquals("the declared clock stays a root",
                "SYMBOLIC", mode(selected, 0));
        assertEquals("the undeclared field is concrete at its recorded value",
                "CONCRETE", mode(selected, 1));
        assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                demand(selected, 1));
    }

    @Test
    public void aDeclaredFieldSignatureAdmitsItsAccessor() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"fieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertEquals("the undeclared clock is concretized",
                "CONCRETE", mode(selected, 0));
        assertEquals("SYMBOLIC", mode(selected, 1));
    }

    @Test
    public void aRegionTheFileDoesNotNameKeepsNoAutomaticRoot()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(DN, proposals());

        assertEquals("CONCRETE", mode(selected, 0));
        assertEquals("CONCRETE", mode(selected, 1));
    }

    /** The marker is the workload's own declaration, so it needs no row. */
    @Test
    public void anExplicitFaultMarkerSurvivesAnUnrelatedDeclaration()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(DN, proposals());

        assertEquals("SYMBOLIC", mode(selected, 2));
        assertEquals("WORKLOAD_DECLARED_SYMBOLIC_FAULT", demand(selected, 2));
        for (com.google.gson.JsonElement row
                : selection.suppressedRootCandidates()) {
            assertFalse("a workload-owned symbol is never a refusal",
                    "EXPLICIT_SYMBOLIC_FAULT".equals(row.getAsJsonObject()
                            .get("sourceKind").getAsString()));
        }
    }

    /** A wire-flow cut port hands over a producer expression; it mints no
     *  root, so refusing it would only cut propagation. */
    @Test
    public void aDeclaredCommunicationCutPortIsNotGovernedByTheAllowlist()
            throws Exception {
        JsonArray actions = proposals();
        JsonObject cut = action("COMMUNICATION_SITE_PORT",
                "<C: int getKeyId()>#u2");
        cut.addProperty("cell", "<C: int getKeyId()>.return");
        actions.add(cut);
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(DN, actions);

        assertEquals("SYMBOLIC", mode(selected, 3));
        assertEquals("DECLARED_COMMUNICATION_CUT_PORT", demand(selected, 3));
    }

    @Test
    public void telemetryNamesEveryRefusedCandidate() throws Exception {
        Path path = declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                + CLOCK_CELL + "\"]}");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(path, catalog());

        selection.select(NN, proposals());
        selection.select(DN, proposals());

        JsonObject telemetry = ConcolicScheduler.rootPolicyTelemetry(
                path, selection);
        assertEquals("SYMBOLIC_ROOT_POLICY",
                telemetry.get("kind").getAsString());
        // NN refuses the field; DN refuses the clock and the field.
        assertEquals(3,
                telemetry.get("suppressedRootCandidateCount").getAsInt());
        JsonArray rows = telemetry.getAsJsonArray("suppressedRootCandidates");
        boolean sawClock = false;
        for (com.google.gson.JsonElement element : rows) {
            JsonObject row = element.getAsJsonObject();
            assertEquals("SUPPRESSED_ROOT_CANDIDATE",
                    row.get("kind").getAsString());
            assertTrue("a refusal names its site",
                    !row.get("siteId").getAsString().isEmpty());
            if ("EXTERNAL_CALL_RETURN".equals(
                    row.get("sourceKind").getAsString())) {
                sawClock = true;
                assertEquals(DN, row.get("regionId").getAsString());
                assertEquals(CLOCK_CELL, row.get("cell").getAsString());
            }
        }
        assertTrue("the refused clock is named", sawClock);
    }

    private Path declarations(String... rows) throws IOException {
        Path path = folder.newFile("symbolic-inputs.jsonl").toPath();
        StringBuilder text = new StringBuilder();
        for (String row : rows) text.append(row).append('\n');
        Files.write(path, text.toString().getBytes(StandardCharsets.UTF_8));
        return path;
    }

    private static List<JsonObject> catalog() {
        return Arrays.asList(region(NN), region(DN));
    }

    private static JsonObject region(String regionId) {
        JsonObject region = new JsonObject();
        region.addProperty("regionId", regionId);
        return region;
    }

    /** One automatic clock return, one accessor field, one fault marker. */
    private static JsonArray proposals() {
        JsonArray actions = new JsonArray();
        JsonObject clock = action("EXTERNAL_CALL_RETURN",
                "<C: void removeExpiredKeys()>#u2");
        clock.addProperty("cell", CLOCK_CELL);
        clock.addProperty("declaredCallee",
                "<org.apache.hadoop.util.Timer: long now()>");
        actions.add(clock);
        JsonObject field = action("ACCESSOR_RETURN", "<C: boolean f()>#u9");
        field.addProperty("accessFieldSignature", KEY_ID);
        field.addProperty("cell", KEY_ID);
        actions.add(field);
        JsonObject fault = action("EXPLICIT_SYMBOLIC_FAULT",
                "<C: void sendRpcRequest(D)>#u17");
        fault.addProperty("cell", "<C: void sendRpcRequest(D)>::$z5");
        actions.add(fault);
        return actions;
    }

    private static JsonObject action(String sourceKind, String siteId) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("sourceKind", sourceKind);
        action.addProperty("siteId", siteId);
        action.addProperty("portId", "port." + siteId);
        action.addProperty("symbol", "port." + siteId);
        return action;
    }

    private static List<String> modes(JsonArray selected) {
        return Arrays.asList(mode(selected, 0), mode(selected, 1),
                mode(selected, 2));
    }

    private static String mode(JsonArray selected, int index) {
        return selected.get(index).getAsJsonObject()
                .get("mode").getAsString();
    }

    private static String demand(JsonArray selected, int index) {
        JsonObject action = selected.get(index).getAsJsonObject();
        return action.has("symbolicDemand")
                ? action.get("symbolicDemand").getAsString()
                : Collections.<String>emptyList().toString();
    }
}
