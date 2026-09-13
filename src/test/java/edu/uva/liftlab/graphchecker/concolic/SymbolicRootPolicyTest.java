package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
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
 * Which proposed roots an experiment's declaration file admits.
 *
 * <p>The automatic mechanisms propose far more roots than any chain needs --
 * on the HDFS block-key workloads every {@code Timer.now()} return -- so the
 * file is a restrictive allowlist over them.  Two authorities are exempt: a
 * source hook's own field, and a fault marker the workload wrote into its own
 * program text.</p>
 *
 * <p>A row says one of two things about a name.  {@code fieldSignatures},
 * {@code portIds} and {@code cells} declare a root: the search starts there,
 * and the replay mints one even where a carrier already wraps the read.  The
 * {@code carrier*} keys declare the opposite: keep this read symbolic so its
 * candidates keep being published, but mint nothing.</p>
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
        assertFalse("a concretized row never carries it",
                selected.get(1).getAsJsonObject().has(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
        assertFalse("nor does the exempt fault marker",
                selected.get(2).getAsJsonObject().has(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
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
        assertFalse("an exempt port is not a declared root either",
                selected.get(3).getAsJsonObject().has(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
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
        assertEquals("another region's store of the same field does not",
                "CONCRETE", mode(consuming, 1));
        assertFalse(consuming.get(1).getAsJsonObject().has(
                InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
    }

    /** The plan must say which ports it exempted, or a later root count
     *  cannot be read against it. */
    @Test
    public void telemetryNamesEveryExemptedCutPort() throws Exception {
        Path path = declarations("{\"regionId\":\"" + NN + "\",\"cells\":[\""
                + CLOCK_CELL + "\"]}");
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(path, catalog());
        JsonArray actions = proposals();
        JsonObject cut = action("COMMUNICATION_SITE_PORT",
                "<C: int getKeyId()>#u2");
        actions.add(cut);

        selection.select(DN, actions);

        JsonObject telemetry = ConcolicScheduler.rootPolicyTelemetry(
                path, selection);
        assertEquals(1, telemetry.get("declaredCutPortCount").getAsInt());
        assertEquals("port.<C: int getKeyId()>#u2",
                telemetry.getAsJsonArray("declaredCutPorts").get(0)
                        .getAsString());
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

    /**
     * A file that admits nothing keeps only the hook's own root.
     *
     * <p>An absent file and an empty one are different instructions.  Absent
     * means the experiment never narrowed anything, so every proposal stands;
     * empty means it narrowed to the exempt authorities, which is how a
     * workload says "the source hook's field is the only thing I am varying".
     * HDFS-17960 is that case: one configuration Boolean, everything else at
     * its recorded value.</p>
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
        assertEquals("so is an unrelated accessor field",
                "CONCRETE", mode(selected, 1));
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
        assertEquals(2, selection.suppressedRootCandidates().size());
    }

    /**
     * A carrier row keeps the read symbolic without starting a search there.
     *
     * <p>Concretizing a read is not free: the plan then never symbolizes it,
     * the VM publishes no {@code ReadFrom} candidates for it, and the guarded
     * read family the composer needs has no writer cases to admit.  A carrier
     * row is the third answer -- keep propagating through this field, mint
     * nothing -- which is what HDFS-17960's counter needs while the
     * configuration Boolean stays the only root.</p>
     */
    @Test
    public void aCarrierRowStaysSymbolicWithoutTheMintMarker()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"carrierFieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), catalog());

        JsonArray selected = selection.select(NN, proposals());

        assertEquals("the automatic clock is still concretized",
                "CONCRETE", mode(selected, 0));
        assertEquals("the carrier field keeps propagating",
                "SYMBOLIC", mode(selected, 1));
        assertEquals("DECLARED_SYMBOLIC_CARRIER", demand(selected, 1));
        assertFalse("a carrier never carries the mint marker",
                selected.get(1).getAsJsonObject().has(
                        InputActionCatalog.DECLARED_SYMBOLIC_ROOT));
        assertEquals("only the clock was refused",
                1, selection.suppressedRootCandidates().size());
    }

    /** A carrier row governs only the region that declares it. */
    @Test
    public void aCarrierRowDoesNotReachAnotherRegion() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"carrierFieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), catalog());

        JsonArray selected = selection.select(DN, proposals());

        assertEquals("CONCRETE", mode(selected, 1));
        assertEquals("CONFIGURED_SYMBOLIC_INPUT_UNSELECTED",
                demand(selected, 1));
    }

    /**
     * The hook's own field is exempt from a carrier row too.
     *
     * <p>This is the HDFS-17960 shape exactly: one carrier row, and the
     * configured source still owns its field, so the campaign still has
     * exactly one root.</p>
     */
    @Test
    public void aCarrierRowLeavesTheConfiguredSourceExempt() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"carrierFieldSignatures\":[\"" + KEY_ID
                                + "\"]}"), hookCatalog());

        JsonArray selected = selection.select(NN, hookProposals());

        assertEquals("the carrier propagates", "SYMBOLIC", mode(selected, 1));
        assertEquals("the workload's own fault marker is exempt",
                "SYMBOLIC", mode(selected, 2));
        assertEquals("the hook still owns its field",
                "CONCRETE", mode(selected, 3));
        assertEquals("CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED",
                demand(selected, 3));
    }

    /** Root and carrier are opposite instructions about the same name. */
    @Test
    public void oneNameMayNotBeBothARootAndACarrier() throws Exception {
        try {
            ConcolicScheduler.SymbolicInputSelection.read(
                    declarations("{\"regionId\":\"" + NN
                            + "\",\"fieldSignatures\":[\"" + KEY_ID
                            + "\"],\"carrierFieldSignatures\":[\"" + KEY_ID
                            + "\"]}"), catalog());
            org.junit.Assert.fail("a name declared twice must be refused");
        } catch (IOException refused) {
            assertTrue(refused.getMessage().contains("both a root and a "
                    + "carrier"));
        }
    }

    /** The same file, read as absent, narrows nothing at all. */
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
