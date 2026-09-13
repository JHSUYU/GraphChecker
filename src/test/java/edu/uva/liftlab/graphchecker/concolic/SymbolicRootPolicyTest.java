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

    /**
     * An undeclared external call return has no carrier to keep.
     *
     * <p>The clock is declared for this region; the {@code keyId} field is
     * not.  Both stay symbolic -- but only one may mint.</p>
     */
    @Test
    public void anUndeclaredExternalCallReturnIsConcrete() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"fieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertEquals("nothing propagated into the call return, so tracking "
                        + "it would be minting it",
                "CONCRETE", mode(selected, 0));
        assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                demand(selected, 0));
        assertEquals("SYMBOLIC", mode(selected, 1));
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

    /**
     * Every carrier the file does not name is tracked and mints nothing.
     *
     * <p>Concretizing a carrier is not the neutral option it looks like: the
     * plan then never symbolizes the read, the VM publishes no candidates
     * for it, and the guarded read family the composition needs has no
     * writer cases to admit.  This is the HDFS-17960 collapse and the
     * HDFS-11741 one, and the reason the allowlist narrows MINT alone.</p>
     */
    @Test
    public void anUndeclaredCarrierIsTrackedWithoutTheMint() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        JsonObject carrier = selected.get(1).getAsJsonObject();
        assertEquals("the surviving SYMBOLIC mode is the TRACK verdict",
                "SYMBOLIC", carrier.get("mode").getAsString());
        assertFalse(carrier.get("mintEligible").getAsBoolean());
        assertEquals("only the declared clock may mint",
                true, selected.get(0).getAsJsonObject()
                        .get("mintEligible").getAsBoolean());
    }

    @Test
    public void aDeclaredFieldSignatureAdmitsItsAccessor() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"fieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertTrue(selected.get(1).getAsJsonObject()
                .get("mintEligible").getAsBoolean());
        assertTrue(selected.get(1).getAsJsonObject().get(
                InputActionCatalog.DECLARED_SYMBOLIC_ROOT).getAsBoolean());
    }

    /** A declaration governs only the region that states it. */
    @Test
    public void aRegionTheFileDoesNotNameMintsNothing() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(DN, proposals());

        assertEquals("the clock is another region's root", "CONCRETE",
                mode(selected, 0));
        assertEquals("the field still carries here", "SYMBOLIC",
                mode(selected, 1));
        assertFalse(selected.get(1).getAsJsonObject()
                .get("mintEligible").getAsBoolean());
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
        assertTrue("a marker the workload wrote is always a root",
                selected.get(2).getAsJsonObject()
                        .get("mintEligible").getAsBoolean());
        for (JsonElement row : selection.suppressedRootCandidates()) {
            assertFalse("a workload-owned symbol is never a refusal",
                    "EXPLICIT_SYMBOLIC_FAULT".equals(row.getAsJsonObject()
                            .get("sourceKind").getAsString()));
        }
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

    /**
     * A tracked action keeps the demand the planner authored.
     *
     * <p>{@code symbolicDemand} is how the replay learns that a port models
     * a whole container rather than a scalar, so overwriting it with this
     * file's verdict silently downgrades the carrier the verdict just kept.
     * HDFS-11741 measured both halves of that: fourteen of its eighteen
     * container-state actions were concretized outright and the remaining
     * four, kept as cut ports, reached the replay with their container
     * demand replaced.</p>
     */
    @Test
    public void aTrackedActionKeepsItsAuthoredDemand() throws Exception {
        JsonArray actions = proposals();
        JsonObject state = action("ACTIVATION_FIELD_RECEIVER",
                "<C: void rollKeys()>#u4");
        state.addProperty("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        state.addProperty("accessFieldSignature",
                "<org.apache.hadoop.security.token.delegation"
                        + ".AbstractDelegationTokenSecretManager:"
                        + " java.util.Map allKeys>");
        actions.add(state);
        JsonObject cut = action("COMMUNICATION_SITE_PORT",
                "<C: void sendKeys()>#u7");
        cut.addProperty("symbolicDemand", "BOUNDED_CONTAINER_STATE");
        actions.add(cut);
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                                + CLOCK_CELL + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, actions);

        assertEquals("SYMBOLIC", mode(selected, 3));
        assertEquals("BOUNDED_CONTAINER_STATE", demand(selected, 3));
        assertEquals("SYMBOLIC", mode(selected, 4));
        assertEquals("BOUNDED_CONTAINER_STATE", demand(selected, 4));
    }

    /**
     * A root declaration governs the region that names it and no other.
     *
     * <p>HDFS-17899 declares {@code DelegationKey#expiryDate} in the
     * NameNode's key-update region, and the same field is where the
     * DataNodes' {@code PBHelper.convert(BlockKeyProto)} stores the value the
     * wire delivered.  Matching a declaration by field signature alone would
     * stamp the consumer's store as a mint site and give every DataNode its
     * own free clock.</p>
     */
    @Test
    public void aRootDeclarationDoesNotReachAnotherRegionsStore()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"fieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), catalog());

        JsonArray declaring = selection.select(NN, proposals());
        JsonArray consuming = selection.select(DN, proposals());

        assertTrue("the declaring region mints",
                declaring.get(1).getAsJsonObject().get(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT)
                        .getAsBoolean());
        assertFalse("another region's store of the same field does not",
                consuming.get(1).getAsJsonObject().get(
                        "mintEligible").getAsBoolean());
        assertFalse(consuming.get(1).getAsJsonObject().has(
                InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
    }

    /**
     * Naming a cut port in the selection file still mints nothing there.
     *
     * <p>A cut port is not mint-eligible because it is neither declared nor
     * workload-owned, which is an accident of the arithmetic rather than a
     * decision.  Declare the port by name and the arithmetic flips -- and
     * the consumer of a wire flow becomes a root, which is the whole defect.
     * The port's own verdict has to outrank the file.</p>
     */
    @Test
    public void aDeclaredPortIdDoesNotMakeACutPortMintEligible()
            throws Exception {
        JsonArray actions = proposals();
        JsonObject cut = action("COMMUNICATION_SITE_PORT",
                "<C: int getKeyId()>#u2");
        actions.add(cut);
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + DN
                                + "\",\"portIds\":[\"port.<C: int getKeyId()>#u2\"]}"),
                        catalog());

        JsonArray selected = selection.select(DN, actions);

        assertEquals("the wire value is still tracked",
                "SYMBOLIC", mode(selected, 3));
        assertFalse("but the declaration cannot make it a root",
                selected.get(3).getAsJsonObject()
                        .get("mintEligible").getAsBoolean());
        assertFalse(selected.get(3).getAsJsonObject().has(
                InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
    }

    /** One row shape: the cut port's exemption is a decision row like any
     *  other, not a list of its own. */
    @Test
    public void theDecisionRowNamesTheCutPortVerdict() throws Exception {
        Path path = declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                + CLOCK_CELL + "\"]}");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(path, catalog());
        JsonArray actions = proposals();
        actions.add(action("COMMUNICATION_SITE_PORT",
                "<C: int getKeyId()>#u2"));

        selection.select(DN, actions);

        JsonObject cutPortRow = null;
        for (com.google.gson.JsonElement element
                : selection.rootDecisions()) {
            JsonObject row = element.getAsJsonObject();
            if ("COMMUNICATION_SITE_PORT".equals(
                    row.get("sourceKind").getAsString())) {
                cutPortRow = row;
            }
        }
        assertTrue("the cut port has a decision row", cutPortRow != null);
        assertEquals(InputActionCatalog.DECLARED_COMMUNICATION_CUT_PORT,
                cutPortRow.get("verdict").getAsString());
        assertTrue(cutPortRow.get("tracked").getAsBoolean());
        assertFalse(cutPortRow.get("mintEligible").getAsBoolean());
        assertFalse(cutPortRow.get("declared").getAsBoolean());
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
        // Only DN's clock is refused: NN declares its own, and every other
        // proposal is a carrier the file no longer governs.
        assertEquals(1,
                telemetry.get("suppressedRootCandidateCount").getAsInt());
        JsonArray rows = telemetry.getAsJsonArray("suppressedRootCandidates");
        JsonObject refused = rows.get(0).getAsJsonObject();
        assertEquals("SUPPRESSED_ROOT_CANDIDATE",
                refused.get("kind").getAsString());
        assertEquals("EXTERNAL_CALL_RETURN",
                refused.get("sourceKind").getAsString());
        assertEquals(DN, refused.get("regionId").getAsString());
        assertEquals(CLOCK_CELL, refused.get("cell").getAsString());
        assertTrue("a refusal names its site",
                !refused.get("siteId").getAsString().isEmpty());
    }

    /** Both verdicts are published per action, not just the refusals. */
    @Test
    public void theDecisionRowsNameBothVerdicts() throws Exception {
        Path path = declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                + CLOCK_CELL + "\"]}");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(path, catalog());

        selection.select(NN, proposals());

        JsonObject telemetry = ConcolicScheduler.rootPolicyTelemetry(
                path, selection);
        assertEquals(3, telemetry.get("decidedActionCount").getAsInt());
        assertEquals("every proposal here is symbolized",
                3, telemetry.get("trackedActionCount").getAsInt());
        assertEquals("the clock and the fault marker may mint",
                2, telemetry.get("mintEligibleActionCount").getAsInt());
        assertEquals("only the clock is named by the file",
                1, telemetry.get("declaredActionCount").getAsInt());

        List<JsonObject> artifact = ConcolicScheduler.rootPolicyRows(
                path, selection);
        assertEquals("one summary row, then one row per action",
                4, artifact.size());
        assertEquals("SYMBOLIC_ROOT_DECISION",
                artifact.get(1).get("kind").getAsString());
        assertTrue(artifact.get(1).get("tracked").getAsBoolean());
        assertTrue(artifact.get(1).get("declared").getAsBoolean());
        assertEquals("DECLARED_SYMBOLIC_ROOT",
                artifact.get(1).get("verdict").getAsString());
        assertEquals("TRACKED_CARRIER",
                artifact.get(2).get("verdict").getAsString());
    }

    /**
     * A file that admits nothing keeps only the hook's own root.
     *
     * <p>An absent file and an empty one are different instructions.  Absent
     * means the experiment never narrowed anything, so every proposal stands;
     * empty means it narrowed to the exempt authorities, which is how a
     * workload says "the source hook's field is the only thing I am varying".
     * HDFS-17960 is that case: one configuration Boolean is the campaign's
     * only root, and every carrier under it keeps propagating.</p>
     */
    @Test
    public void anEmptyFileAdmitsNothingButTheExemptAuthorities()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations(), hookCatalog());

        JsonArray selected = selection.select(NN, hookProposals());

        assertEquals("the automatic clock return is concretized",
                "CONCRETE", mode(selected, 0));
        assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                demand(selected, 0));
        assertEquals("an unrelated accessor field keeps carrying",
                "SYMBOLIC", mode(selected, 1));
        assertFalse("but mints nothing", selected.get(1).getAsJsonObject()
                .get("mintEligible").getAsBoolean());
        assertEquals("the workload's own fault marker is exempt",
                "SYMBOLIC", mode(selected, 2));
        // The hook mints its field itself, so the input action stands down
        // rather than minting a second root for the same location.
        assertEquals("CONCRETE", mode(selected, 3));
        assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                demand(selected, 3));

        // Narrowing happened, and the telemetry names what it refused: an
        // empty file that silently behaved like an absent one would report
        // nothing here.
        assertEquals(1, selection.suppressedRootCandidates().size());
    }

    /** The same file, read as absent, still narrows to the hook. */
    @Test
    public void anAbsentFileWithAHookStillNarrowsToTheHook() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        null, hookCatalog());

        JsonArray selected = selection.select(NN, hookProposals());

        // A declaring hook is itself an allowlist authority, so its presence
        // is what turns narrowing on - not the file.
        assertEquals("CONCRETE", mode(selected, 0));
        assertEquals("CONCRETE", mode(selected, 3));
        assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                demand(selected, 3));
    }

    /**
     * The retired {@code carrier*} keys are refused, not ignored.
     *
     * <p>They existed to say "keep this read symbolic but mint nothing",
     * which is now what every name this file does not mention already gets.
     * A file still carrying one is stale, and reading it as a root would
     * invert the instruction, so say so.</p>
     */
    @Test
    public void aRetiredCarrierKeyIsRefused() throws Exception {
        try {
            ConcolicScheduler.SymbolicInputSelection.read(
                    declarations("{\"regionId\":\"" + NN
                            + "\",\"carrierFieldSignatures\":[\"" + KEY_ID
                            + "\"]}"), catalog());
            org.junit.Assert.fail("a retired key must be refused");
        } catch (IOException refused) {
            assertTrue(refused.getMessage().contains(
                    "carrierFieldSignatures was removed"));
        }
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
