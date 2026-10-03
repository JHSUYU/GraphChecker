package edu.uva.liftlab.graphchecker.plan;


import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.Clock;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * What makes a read symbolic: its category, as the static scope map states it
 * ({@link StaticScopeMap#clocks}, {@link StaticScopeMap#readSites}), a
 * fault marker in the program's text, a field a hook owns, or a wire cut
 * port.  Every other proposed read is concrete.
 */
public class SymbolicRootPolicyTest {

    private static final String NN = "REGION.nn";
    private static final String DN = "REGION.dn";
    private static final Clock WALL_MS = Clock.of(1_000_000L, Clock.WALL);
    private static final String TIMER_NOW =
            "<org.apache.hadoop.util.Timer: long now()>";
    private static final String CLOCK_CELL = TIMER_NOW + ".return";
    private static final String EXPIRE =
            "<C: void removeExpiredKeys()>";
    private static final String KEY_ID = "<org.apache.hadoop.security.token"
            + ".delegation.DelegationKey: int keyId>";
    private static final String ROOT = InputActionCatalog
            .DECLARED_SYMBOLIC_ROOT;

    /** hdfs-17960's counter: read through a JDK accessor, stored elsewhere. */
    private static final String ATOMIC_VALUE =
            "<java.util.concurrent.atomic.AtomicInteger: int value>";
    private static final String ATOMIC_GET =
            "<java.util.concurrent.atomic.AtomicInteger: int get()>";
    private static final String NUM_SNAPSHOTS =
            "<S: java.util.concurrent.atomic.AtomicInteger numSnapshots>";
    private static final String DECREMENT = "<java.util.concurrent.atomic"
            + ".AtomicInteger: int getAndDecrement()>";
    private static final String DELETE = "<S: void deleteSnapshot()>";
    private static final String GET_NUM = "<S: int getNumSnapshots()>";
    private static final String GET_NUM_LOCAL = GET_NUM + "::$i0";
    private static final String COUNTER = "<S: int snapshotCounter>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    /**
     * A clock's read carries the mint marker and the clock flag, both off the
     * scope map; a read no category names is concrete by name; the fault
     * marker in the program's text is a root; and a declared wire-flow cut
     * port hands over a producer expression: tracked, and no root.
     */
    @Test
    public void onlyARootMakesAReadSymbolic() throws Exception {
        StaticScopeMap map = map(Arrays.asList(clockRead(EXPIRE)),
                Collections.singletonMap(NN, Collections.singletonList(
                        EXPIRE)), Collections.singletonMap(TIMER_NOW, WALL_MS),
                method -> true);
        assertEquals(Collections.singletonMap(TIMER_NOW, WALL_MS),
                map.clocks());
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(map,
                        catalog());
        JsonArray selected = selection.select(NN, proposals());

        assertTrue("the clock carries the mint marker",
                selected.get(0).getAsJsonObject().get(ROOT).getAsBoolean());
        assertEquals("and the clock's tick, read off its category",
                1_000_000L, selected.get(0).getAsJsonObject()
                        .get(InputActionCatalog.DECLARED_WALL_CLOCK)
                        .getAsLong());
        assertEquals("and the JVM clock it wraps: tick and source are one "
                        + "clock's identity", Clock.WALL,
                member(selected, 0, InputActionCatalog.DECLARED_CLOCK_SOURCE));
        assertEquals("a read no category names is concrete by name",
                "CONCRETE", member(selected, 1, "mode"));
        assertEquals(ConcolicScheduler.SymbolicInputSelection.UNDECLARED,
                member(selected, 1, "symbolicDemand"));
        assertEquals("the fault marker stays symbolic",
                "SYMBOLIC", member(selected, 2, "mode"));
        assertTrue("and is a root: the program's text states it",
                selected.get(2).getAsJsonObject().get(ROOT).getAsBoolean());
        JsonArray actions = proposals();
        actions.add(action("COMMUNICATION_SITE_PORT", "<C: int getKeyId()>#u2",
                "<C: int getKeyId()>.return"));
        JsonObject cut = selection.select(DN, actions).get(3).getAsJsonObject();
        assertEquals("SYMBOLIC", cut.get("mode").getAsString());
        assertFalse("a cut port is not a root", cut.has(ROOT));

        // A name is a VALUE, and the graph names one value once per local it
        // is copied into; Soot proves which edges are exact copies, so
        // following only those renames it onto the port.
        JsonObject port = action("EXTERNAL_CALL_RETURN", GET_NUM + "#u2",
                GET_NUM_LOCAL);
        ConcolicScheduler.SymbolicInputSelection renamed = clockOf(GET_NUM);
        renamed.resolveDeclaredNames(Collections.singletonList(
                copy("SOOT_EXACT_LOCAL_DIRECT_COPY_V1")));
        assertTrue("the proven rename selects the port",
                renamed.select(NN, actions(port)).get(0).getAsJsonObject()
                        .get(ROOT).getAsBoolean());
        ConcolicScheduler.SymbolicInputSelection unproven = clockOf(GET_NUM);
        unproven.resolveDeclaredNames(Collections.singletonList(copy("")));
        assertFalse("an edge Soot did not prove a copy is not a rename",
                unproven.select(NN, actions(port)).get(0).getAsJsonObject()
                        .has(ROOT));
    }

    /**
     * A READ placeholder: a read the weave cannot version -- its accessor runs
     * outside the woven program -- of a location another region stores.  A
     * woven accessor's read is versioned where it runs, and a location only
     * its own region stores has no writer to bind.
     */
    @Test
    public void aReadTheWeaveCannotVersionIsAPlaceholder() throws Exception {
        Map<String, List<String>> apart = new LinkedHashMap<>();
        apart.put(NN, Collections.singletonList(GET_NUM));
        apart.put(DN, Collections.singletonList(DELETE));
        List<Map<String, Object>> edges = Arrays.asList(atomicRead(),
                atomicStore());
        StaticScopeMap unwoven = map(edges, apart,
                Collections.<String, Clock>emptyMap(), ATOMIC_GET::equals);
        assertEquals(Collections.singleton(StaticScopeMap.readKey(
                GET_NUM + "#u2", ATOMIC_VALUE)), unwoven.readSites());
        JsonObject port = action("ACCESSOR_RETURN", GET_NUM + "#u2",
                ATOMIC_VALUE);
        port.addProperty("accessFieldSignature", ATOMIC_VALUE);
        JsonObject read = ConcolicScheduler.SymbolicInputSelection.read(
                unwoven, catalog()).select(NN, actions(port)).get(0)
                .getAsJsonObject();
        assertTrue("the placeholder is minted", read.get(ROOT).getAsBoolean());
        assertFalse("and is no clock",
                read.has(InputActionCatalog.DECLARED_WALL_CLOCK));

        assertTrue("a woven accessor's read is no placeholder",
                map(edges, apart, Collections.<String, Clock>emptyMap(),
                        method -> false).readSites().isEmpty());
        assertTrue("nor is a read its own region alone stores",
                map(edges, Collections.singletonMap(NN,
                        Arrays.asList(GET_NUM, DELETE)),
                        Collections.<String, Clock>emptyMap(), ATOMIC_GET::equals)
                        .readSites().isEmpty());

    }

    /**
     * SYMBOL-SCOPE F2: a primitive instance cell the slice both reads and
     * stores, and a branch decides on, is tracked -- every access of it is
     * observed, a read, a {@code putfield} and an atomic's RMW, and a region
     * reading it observes its branches from entry.  A cell no read of the
     * slice reaches, or whose reads only feed data or the wire, is not.
     */
    @Test
    public void aCellTheSliceReadsAndStoresIsTracked() throws Exception {
        Map<String, List<String>> apart = new LinkedHashMap<>();
        apart.put(NN, Collections.singletonList(GET_NUM));
        apart.put(DN, Collections.singletonList(DELETE));
        StaticScopeMap tracked = map(Arrays.asList(atomicRead(),
                atomicStore(), counterRead(), counterStore(),
                guard(GET_NUM_LOCAL), guard(GET_NUM + "::$i1")), apart,
                Collections.<String, Clock>emptyMap(), method -> false);
        JsonArray sites = tracked.observedSites();
        assertEquals("both reads, the atomic's RMW and the putfield", 4,
                sites.size());
        assertEquals(GET_NUM + "#u2", member(sites, 0, "siteId"));
        assertEquals("true", member(sites, 0, "read"));
        assertEquals(DELETE + "#u35", member(sites, 1, "siteId"));
        assertEquals(DECREMENT, member(sites, 1, "declaredCallee"));
        assertEquals("false", member(sites, 1, "read"));
        assertEquals(GET_NUM + "#u4", member(sites, 2, "siteId"));
        assertEquals("true", member(sites, 2, "read"));
        assertEquals(DELETE + "#u40", member(sites, 3, "siteId"));
        assertEquals("a putfield names no callee", "",
                member(sites, 3, "declaredCallee"));
        ConcolicScheduler.SymbolicInputSelection selection =
                ConcolicScheduler.SymbolicInputSelection.read(tracked,
                        catalog());
        assertTrue("the reading region observes from entry",
                selection.readsTrackedState(Collections.singleton(NN)));
        assertTrue("so does one it is folded into", selection
                .readsTrackedState(Arrays.asList("REGION.enclosing", NN)));
        assertFalse("the writing region does not", selection
                .readsTrackedState(Collections.singleton(DN)));
        assertEquals("a store no read of the slice reaches is not observed",
                0, map(Arrays.asList(atomicStore(), counterStore()), apart,
                        Collections.<String, Clock>emptyMap(), method -> false)
                        .observedSites().size());
        assertEquals("nor one whose reads no branch decides on", 0,
                map(Arrays.asList(atomicRead(), atomicStore(), counterRead(),
                        counterStore()), apart,
                        Collections.<String, Clock>emptyMap(), method -> false)
                        .observedSites().size());
        assertEquals("nor one whose reads a receiver decides on (F3)", 0,
                map(Arrays.asList(counterRead(), counterStore(),
                        edge("{\"kind\":\"wire_handoff\",\"fromCell\":\""
                                + GET_NUM + "::$i1\",\"toCell\":\"" + DELETE
                                + "::$i3\"}"), guard(DELETE + "::$i3")),
                        apart, Collections.<String, Clock>emptyMap(),
                        method -> false).observedSites().size());
    }

    /** The published scope map of these edges, through the artifact the way
     *  SEED publishes it and PLAN reads it. */
    private StaticScopeMap map(List<Map<String, Object>> edges,
                               Map<String, List<String>> regionMethods,
                               Map<String, Clock> clocks,
                               Predicate<String> unwoven)
            throws IOException {
        List<Map<String, Object>> regions = new java.util.ArrayList<>();
        for (Map.Entry<String, List<String>> region
                : regionMethods.entrySet()) {
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("regionId", region.getKey());
            row.put("methods", region.getValue());
            regions.add(row);
        }
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(StaticScopeMap.sites(edges,
                regions, clocks, (m, u, c) -> null, unwoven,
                cell -> SharedFieldFlow.TrackedKind.VALUE, cell -> false),
                null)) {
            text.append(row.toString()).append('\n');
        }
        Path file = folder.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    /** A selection whose one clock is {@code callee}. */
    private ConcolicScheduler.SymbolicInputSelection clockOf(String callee)
            throws IOException {
        return ConcolicScheduler.SymbolicInputSelection.read(map(
                Arrays.asList(clockRead(callee, EXPIRE)),
                Collections.singletonMap(NN, Collections.singletonList(
                        EXPIRE)), Collections.singletonMap(callee, WALL_MS),
                method -> true), catalog());
    }

    private static Map<String, Object> clockRead(String method) {
        return clockRead(TIMER_NOW, method);
    }

    private static Map<String, Object> clockRead(String callee,
                                                 String method) {
        return edge("{\"kind\":\"call_return\",\"method\":\"" + method
                + "\",\"unitIndex\":2,\"invoke\":\"" + callee
                + "\",\"fromCell\":\"" + callee + ".return\",\"toCell\":\""
                + method + "::$l0\"}");
    }

    private static Map<String, Object> atomicRead() {
        return edge("{\"kind\":\"accessor_field_return\",\"method\":\""
                + GET_NUM + "\",\"unitIndex\":2,\"invoke\":\"" + ATOMIC_GET
                + "\",\"declaredFieldSignature\":\"" + ATOMIC_VALUE
                + "\",\"accessorImplementationMethod\":\"" + ATOMIC_GET
                + "\",\"fromCell\":\"" + ATOMIC_VALUE + "\",\"toCell\":\""
                + GET_NUM_LOCAL + "\"}");
    }

    private static Map<String, Object> atomicStore() {
        return edge("{\"kind\":\"field_mutation\",\"transferKind\":"
                + "\"HEAP_WRITE\",\"fromCell\":\"" + DELETE + "#u35\","
                + "\"toCell\":\"" + NUM_SNAPSHOTS + "\",\"method\":\""
                + DELETE + "\",\"unitIndex\":35,\"invoke\":\"" + DECREMENT
                + "\"}");
    }

    /** A branch of the slice on {@code cell}. */
    private static Map<String, Object> guard(String cell) {
        return edge("{\"kind\":\"guard_dependency\",\"method\":\""
                + GET_NUM + "\",\"unitIndex\":6,\"fromCell\":\"" + cell
                + "\",\"toCell\":\"" + GET_NUM + "#u6\"}");
    }

    private static Map<String, Object> counterRead() {
        return edge("{\"kind\":\"field_read\",\"method\":\"" + GET_NUM
                + "\",\"unitIndex\":4,\"fromCell\":\"" + COUNTER
                + "\",\"toCell\":\"" + GET_NUM + "::$i1\"}");
    }

    private static Map<String, Object> counterStore() {
        return edge("{\"kind\":\"field_write\",\"transferKind\":"
                + "\"HEAP_WRITE\",\"fromCell\":\"" + DELETE + "::$i2\","
                + "\"toCell\":\"" + COUNTER + "\",\"method\":\""
                + DELETE + "\",\"unitIndex\":40}");
    }

    private static JsonObject copy(String authority) {
        JsonObject edge = json("{\"kind\":\"local_def_use\",\"transferKind\":"
                + "\"VALUE_PASS\",\"fromCell\":\"" + GET_NUM_LOCAL
                + "\",\"toCell\":\"" + GET_NUM + ".return\"}");
        if (!authority.isEmpty()) {
            edge.addProperty("valueFlowAuthority", authority);
        }
        return edge;
    }

    /** One candidate-graph row as the static stage holds it. */
    private static Map<String, Object> edge(String row) {
        Map<String, Object> edge = new LinkedHashMap<>();
        for (Map.Entry<String, com.google.gson.JsonElement> member
                : json(row).entrySet()) {
            edge.put(member.getKey(), member.getValue().getAsJsonPrimitive()
                    .isNumber() ? (Object) member.getValue().getAsInt()
                    : member.getValue().getAsString());
        }
        return edge;
    }

    private static List<JsonObject> catalog() {
        return Arrays.asList(json("{\"regionId\":\"" + NN + "\"}"),
                json("{\"regionId\":\"" + DN + "\"}"));
    }

    /** One clock return, one accessor field, one fault marker. */
    private static JsonArray proposals() {
        JsonArray actions = new JsonArray();
        JsonObject clock = action("EXTERNAL_CALL_RETURN", EXPIRE + "#u2",
                CLOCK_CELL);
        clock.addProperty("declaredCallee", TIMER_NOW);
        actions.add(clock);
        JsonObject field = action("ACCESSOR_RETURN", "<C: boolean f()>#u9",
                KEY_ID);
        field.addProperty("accessFieldSignature", KEY_ID);
        actions.add(field);
        actions.add(action("EXPLICIT_SYMBOLIC_FAULT",
                "<C: void sendRpcRequest(D)>#u17",
                "<C: void sendRpcRequest(D)>::$z5"));
        return actions;
    }

    private static JsonArray actions(JsonObject action) {
        JsonArray actions = new JsonArray();
        actions.add(action.deepCopy());
        return actions;
    }

    private static JsonObject action(String sourceKind, String siteId,
            String cell) {
        return json("{\"mode\":\"SYMBOLIC\",\"sourceKind\":\""
                + sourceKind + "\",\"siteId\":\"" + siteId
                + "\",\"portId\":\"port." + siteId + "\",\"symbol\":\"port."
                + siteId + "\",\"cell\":\"" + cell + "\"}");
    }

    private static String member(JsonArray rows, int index, String name) {
        JsonObject row = rows.get(index).getAsJsonObject();
        return row.has(name) ? row.get(name).getAsString() : "";
    }

    private static JsonObject json(String row) {
        return JsonParser.parseString(row).getAsJsonObject();
    }
}
