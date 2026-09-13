package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
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
 * What an experiment's {@code symbolic-inputs.jsonl} governs.
 *
 * <p>Two decisions are taken per proposed input, and the file governs one of
 * them.  TRACK -- symbolize the read so the VM publishes its {@code ReadFrom}
 * candidates and container versions -- is the default for every carrier:
 * field reads, bounded container states, declared cut ports, accessor
 * returns.  MINT -- permission to become a fresh root the solver may move --
 * belongs to three authorities only: a fault marker in the workload's own
 * source, a field a {@code CausynthSymbolicSource} hook owns, and a name this
 * file declares for the action's region.  The file narrows the second
 * decision and never the first.</p>
 *
 * <p>The exception is {@code EXTERNAL_CALL_RETURN}: nothing inside the
 * replayed process wrote that value, so there is no carrier to track and an
 * undeclared one is concrete.</p>
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
        assertEquals("an absent file decides nothing at all",
                0, selection.rootDecisions().size());
    }

    /** The replay needs to know the row was named by hand, not proposed. */
    @Test
    public void anAdmittedActionIsStampedAsDeclared() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertTrue("the declared clock carries the mint marker",
                selected.get(0).getAsJsonObject().get(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT)
                        .getAsBoolean());
        assertFalse("a tracked carrier never carries it",
                selected.get(1).getAsJsonObject().has(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
        assertFalse("nor does the exempt fault marker, whose mint the "
                        + "runtime finds by sourceKind",
                selected.get(2).getAsJsonObject().has(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
    }

    /** A wire-flow cut port hands over a producer expression; it mints no
     *  root, so refusing it would only cut propagation. */
    @Test
    public void aDeclaredCommunicationCutPortIsTrackedAndMintsNothing()
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
        assertFalse(selected.get(3).getAsJsonObject()
                .get("mintEligible").getAsBoolean());
    }

    private static final String ORDERED_FIELD =
            "<org.apache.hadoop.hdfs.server.namenode.snapshot.SnapshotManager:"
                    + " boolean snapshotDeletionOrdered>";

    /** A catalog whose NN region declares one CausynthSymbolicSource hook. */
    private static List<JsonObject> hookCatalog() {
        JsonObject nn = region(NN);
        JsonObject declaration = new JsonObject();
        declaration.addProperty("schemaVersion",
                StaticSymbolicSourceDeclaration.SCHEMA_VERSION);
        declaration.addProperty("kind", StaticSymbolicSourceDeclaration.KIND);
        declaration.addProperty("authority",
                StaticSymbolicSourceDeclaration.AUTHORITY);
        declaration.addProperty("sourceId",
                "HDFS.CONFIG.SNAPSHOT_DELETION_ORDERED");
        declaration.addProperty("fieldSignature", ORDERED_FIELD);
        declaration.addProperty("declarationMethod",
                "<org.apache.hadoop.hdfs.server.namenode.snapshot"
                        + ".SnapshotManager: void <init>(FSDirectory)>");
        declaration.addProperty("declarationUnitIndex", 42);
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        nn.add(StaticSymbolicSourceDeclaration.FIELD, declarations);
        return Arrays.asList(nn, region(DN));
    }

    /** The three standing proposals plus a read of the hook's own field. */
    private static JsonArray hookProposals() {
        JsonArray actions = proposals();
        JsonObject ordered = action("ACCESSOR_RETURN",
                "<C: boolean isSnapshotDeletionOrdered()>#u1");
        ordered.addProperty("accessFieldSignature", ORDERED_FIELD);
        ordered.addProperty("cell", ORDERED_FIELD);
        actions.add(ordered);
        return actions;
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
