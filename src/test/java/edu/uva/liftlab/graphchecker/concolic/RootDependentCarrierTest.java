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
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Which locations a campaign tracks, and why it is not a declaration.
 *
 * <p>A carrier is a shared location this campaign's roots can still change.
 * The runtime-refined dataflow graph states that relation on both of its
 * halves -- a value edge carries a root-dependent value into a cell, and a
 * {@code GUARD} edge runs from a guard's operand to the definition the guard
 * controls -- so one forward closure from the root cells answers both and
 * reaches the fixed point the design asks for: a read of a carrier that
 * feeds another store lands on that store's cell on the next hop.</p>
 *
 * <p>What stays manual is the root set alone.  What stops being manual is
 * the carrier list: the HDFS-17960 experiment used to have to name
 * {@code AtomicInteger#value} by hand, and
 * {@code aCounterAGuardedCaseWritesIsSelectedWithoutBeingNamed} is that
 * shape with nothing declared.</p>
 */
public class RootDependentCarrierTest {

    private static final String NN = "REGION.nn";
    private static final String ORDERED =
            "<S: boolean snapshotDeletionOrdered>";
    private static final String GUARD_LOCAL = "<S: void deleteSnapshot()>::$z0";
    private static final String COUNTER = "<S: java.util.List snapshotsByNames>";
    private static final String COUNTER_READ =
            "<S: int getNumSnapshots()>::$i0";
    private static final String UNRELATED = "<T: long heartbeatTime>";
    private static final String DOWNSTREAM = "<U: int cachedSize>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * The root's own case decides the write, so the location is a carrier.
     *
     * <p>This is HDFS-17960 in miniature: the configured source guards the
     * ordered-deletion case, the case writes the snapshot list, and the
     * list is selected without anything naming it.</p>
     */
    @Test
    public void aCounterAGuardedCaseWritesIsSelectedWithoutBeingNamed()
            throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                graph(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, COUNTER, "GUARD")),
                fieldRead(COUNTER), fieldRead(UNRELATED));

        JsonArray selected = selection.select(NN,
                actions(fieldRead(COUNTER), fieldRead(UNRELATED)));

        assertEquals("the guarded write makes its location a carrier",
                "SYMBOLIC", mode(selected, 0));
        assertEquals("no root reaches the heartbeat clock",
                "CONCRETE", mode(selected, 1));
        assertEquals(ConcolicScheduler.SymbolicInputSelection
                        .NOT_ROOT_DEPENDENT, demand(selected, 1));
    }

    /** A read of a carrier that feeds another store carries it too. */
    @Test
    public void aCarrierThatFeedsAnotherStoreCarriesItToo() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                graph(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, COUNTER, "GUARD"),
                        edge(COUNTER, COUNTER_READ, "HEAP_READ"),
                        edge(COUNTER_READ, DOWNSTREAM, "HEAP_WRITE")),
                fieldRead(DOWNSTREAM));

        JsonArray selected = selection.select(NN,
                actions(fieldRead(DOWNSTREAM)));

        assertEquals("the closure is transitive, not one hop",
                "SYMBOLIC", mode(selected, 0));
    }

    /**
     * A library field read through an accessor is decided by its receiver.
     *
     * <p>{@code AtomicInteger#value} is a source cell of its own and meets
     * the field that holds it only at the local the accessor returns, so
     * the action's {@code dependencyCells} is the only cell it shares with
     * the graph.  Consulting it is what lets the counter's own location
     * select the port the experiment used to name by hand.</p>
     */
    @Test
    public void anAccessorReadIsDecidedByTheLocationItReads()
            throws Exception {
        JsonObject accessor = accessorRead(
                "<java.util.concurrent.atomic.AtomicInteger: int value>",
                COUNTER_READ);
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                graph(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, COUNTER, "GUARD"),
                        edge(COUNTER, COUNTER_READ, "HEAP_READ")),
                accessor);

        JsonArray selected = selection.select(NN, actions(accessor));

        assertEquals("SYMBOLIC", mode(selected, 0));
    }

    /**
     * A field nothing writes is never a carrier.
     *
     * <p>That is a property of the walk rather than a case in it: a static
     * final appears in the graph only as a {@code fromCell}, is the target
     * of no edge, and so cannot be reached from a root.  It holds even
     * though the local it is read into <em>is</em> root-dependent, which is
     * the shape that crashed HDFS-17960's INSTRUMENT stage
     * ({@code STATIC_FIELD_MATERIALIZATION_UNSUPPORTED} on
     * {@code FSDirectory.DOT_RESERVED}).</p>
     */
    @Test
    public void aFieldNothingWritesIsNeverACarrier() throws Exception {
        String constant = "<D: byte[] DOT_RESERVED>";
        String reader = "<D: boolean isReservedName(E)>::$r2";
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                graph(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, reader, "GUARD"),
                        edge(constant, reader, "HEAP_READ")),
                staticFieldRead(constant));

        JsonArray selected = selection.select(NN,
                actions(staticFieldRead(constant)));

        assertEquals("the constant has no writer for a root to reach",
                "CONCRETE", mode(selected, 0));
        assertEquals(ConcolicScheduler.SymbolicInputSelection
                        .NOT_ROOT_DEPENDENT, demand(selected, 0));
    }

    /** A campaign whose roots this graph does not name narrows nothing. */
    @Test
    public void aSliceWithoutAResolvedRootNarrowsNothing() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                graph(edge(UNRELATED, DOWNSTREAM, "HEAP_WRITE")),
                fieldRead(COUNTER));

        JsonArray selected = selection.select(NN,
                actions(fieldRead(COUNTER)));

        assertFalse("no root cell resolved, so the slice is withheld",
                selection.carrierSlice().usable());
        assertEquals("withholding keeps every carrier tracked",
                "SYMBOLIC", mode(selected, 0));
    }

    /** A declared root is tracked whether or not the graph agrees. */
    @Test
    public void aDeclaredRootIsNeverNarrowedAway() throws Exception {
        JsonObject declaredRead = fieldRead(UNRELATED);
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"fieldSignatures\":[\"" + ORDERED
                                + "\",\"" + UNRELATED + "\"]}"), catalog());
        selection.seedCarrierSlice(
                graph(edge(ORDERED, GUARD_LOCAL, "HEAP_READ")),
                proposals(declaredRead));

        JsonArray selected = selection.select(NN, actions(declaredRead));

        assertEquals("SYMBOLIC", mode(selected, 0));
        assertTrue("a declared root still mints",
                selected.get(0).getAsJsonObject().get(
                        ConcolicScheduler.SymbolicInputSelection
                                .MINT_ELIGIBLE).getAsBoolean());
    }

    /** The policy artifact names the locations it kept. */
    @Test
    public void thePolicyRowNamesTheCarriersItKept() throws Exception {
        ConcolicScheduler.SymbolicInputSelection selection = seeded(
                graph(edge(ORDERED, GUARD_LOCAL, "HEAP_READ"),
                        edge(GUARD_LOCAL, COUNTER, "GUARD")),
                fieldRead(COUNTER), fieldRead(UNRELATED));
        selection.select(NN, actions(fieldRead(COUNTER),
                fieldRead(UNRELATED)));

        JsonObject row = ConcolicScheduler.rootPolicyTelemetry(
                null, selection);

        assertTrue(row.get("carrierSliceApplied").getAsBoolean());
        assertEquals("ROOT_DEPENDENT_CARRIERS",
                row.get("carrierSliceReason").getAsString());
        assertEquals(1, row.get("carrierLocationCount").getAsInt());
        assertEquals(COUNTER, row.getAsJsonArray("carrierLocations")
                .get(0).getAsString());
    }

    // --- helpers ---------------------------------------------------------

    /** A selection with no declarations, seeded from one hook-owned root. */
    private ConcolicScheduler.SymbolicInputSelection seeded(
            List<JsonObject> graph, JsonObject... proposed)
            throws IOException {
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(
                        declarations("{\"regionId\":\"" + NN
                                + "\",\"fieldSignatures\":[\"" + ORDERED
                                + "\"]}"), catalog());
        selection.seedCarrierSlice(graph, proposals(proposed));
        return selection;
    }

    private static List<Map.Entry<String, JsonArray>> proposals(
            JsonObject... proposed) {
        List<Map.Entry<String, JsonArray>> rows = new ArrayList<>();
        rows.add(new AbstractMap.SimpleImmutableEntry<>(NN,
                actions(proposed)));
        return rows;
    }

    private static JsonArray actions(JsonObject... proposed) {
        JsonArray actions = new JsonArray();
        for (JsonObject action : proposed) actions.add(action.deepCopy());
        return actions;
    }

    private static List<JsonObject> graph(JsonObject... edges) {
        return Arrays.asList(edges);
    }

    private static JsonObject edge(
            String from, String to, String transferKind) {
        JsonObject row = new JsonObject();
        row.addProperty("fromCell", from);
        row.addProperty("toCell", to);
        row.addProperty("transferKind", transferKind);
        return row;
    }

    /** An instance field read: its own cell is the location. */
    private static JsonObject fieldRead(String field) {
        JsonObject action = base("ACTIVATION_FIELD_RECEIVER");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("cell", field);
        return action;
    }

    /** A library field reached through an accessor on a tracked receiver. */
    private static JsonObject accessorRead(String field, String returnLocal) {
        JsonObject action = base("ACCESSOR_RETURN");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("cell", field);
        JsonArray dependency = new JsonArray();
        dependency.add(returnLocal);
        action.add("dependencyCells", dependency);
        return action;
    }

    /** A static field read: the receiver cell is synthetic, the field is
     *  the only anchor, and nothing writes it. */
    private static JsonObject staticFieldRead(String field) {
        JsonObject action = base("ACTIVATION_FIELD_RECEIVER");
        action.addProperty("accessFieldSignature", field);
        action.addProperty("cell", "<D: boolean isReservedName(E)>"
                + "#u4.fieldReceiver");
        JsonArray dependency = new JsonArray();
        dependency.add(field);
        action.add("dependencyCells", dependency);
        return action;
    }

    private static JsonObject base(String sourceKind) {
        JsonObject action = new JsonObject();
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("sourceKind", sourceKind);
        action.addProperty("siteId", "<C: void m()>#u1");
        action.addProperty("symbol", "port." + sourceKind);
        return action;
    }

    private Path declarations(String... rows) throws IOException {
        Path path = folder.newFile("symbolic-inputs.jsonl").toPath();
        StringBuilder text = new StringBuilder();
        for (String row : rows) text.append(row).append('\n');
        Files.write(path, text.toString().getBytes(StandardCharsets.UTF_8));
        return path;
    }

    private static List<JsonObject> catalog() {
        JsonObject region = new JsonObject();
        region.addProperty("regionId", NN);
        return Collections.singletonList(region);
    }

    private static String mode(JsonArray selected, int index) {
        return selected.get(index).getAsJsonObject()
                .get("mode").getAsString();
    }

    private static String demand(JsonArray selected, int index) {
        JsonObject action = selected.get(index).getAsJsonObject();
        return action.has("symbolicDemand")
                ? action.get("symbolicDemand").getAsString() : "";
    }
}
