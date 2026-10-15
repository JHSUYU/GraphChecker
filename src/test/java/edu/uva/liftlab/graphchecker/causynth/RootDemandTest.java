package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.After;
import org.junit.Test;
import soot.G;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §4.6: where the target's path guards' values enter, nearest
 * boundary first, and which boundaries are chosen.
 */
public class RootDemandTest {
    private static final String T = "t.T";
    private static final String CHECK = "<t.T: void check()>";
    private static final String RUN = "<t.T: void run()>";
    private static final String HANDLE = "<t.T: void handle(int)>";
    /** A door's chain: chosen at RUN's store, standing in RUN. */
    private static final List<String> VIA = Collections.singletonList(RUN);
    private static final String M = "<a.C: void m()>";
    private static final String OTHER = "<a.D: void n()>";
    private static final String STORED = "<a.C: long expiry>";
    private static final String ROOT = M + "::$l0";

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void everyPathStopsAtItsNearestBoundary() {
        Map<String, List<String>> writers = new LinkedHashMap<>();
        scene(writers);
        List<Map<String, Object>> edges = edges();
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("regionId", "REGION.r");
        region.put("rootMethod", HANDLE);
        region.put("methods", Arrays.asList(HANDLE, RUN, CHECK));
        RootDemand demand = RootDemand.of(edges,
                Collections.singletonList(region),
                Collections.singletonMap(
                        "<java.lang.System: long currentTimeMillis()>",
                        Clock.of(1_000_000L, Clock.WALL)),
                ConfigRoots.of(edges, writers),
                Collections.singleton(CHECK + "#u9"),
                field -> field.contains(": int ")
                        ? SharedFieldFlow.TrackedKind.VALUE
                        : SharedFieldFlow.TrackedKind.NONE,
                field -> false, owner -> owner.startsWith("t."), new Faults(),
                Collections.<DemandedDoors.Site>emptyList());
        List<String> found = new ArrayList<>();
        String cut = "";
        for (RootDemand.Boundary boundary : demand.boundaries()) {
            found.add(boundary.kind + " " + boundary.distance + " "
                    + boundary.chosen + " " + boundary.cell);
            if (!boundary.chosen) {
                cut += boundary.kind + ":" + boundary.cut + " ";
            }
        }
        StaticScopeMap.Demanded track = demand.marks().at(CHECK + "#u4",
                field("int count"));
        Object[][] rows = {
            {"the boundaries, nearest first; the clock past the bound is "
                    + "none, the path to it named where it was cut, the "
                    + "configuration behind the tracked count found on the "
                    + "cone", Arrays.asList(
                    "IO 1 false <java.io.FileInputStream: int read()>.return",
                    "PRE_WINDOW 1 true " + field("int old"),
                    "READ 1 true <java.util.concurrent.atomic.AtomicInteger:"
                            + " int value>",
                    "SCOPE 1 true <t.Other: int app()>.return",
                    "TRACK 1 true " + field("int count"),
                    "TRACK_CONTAINER 1 true <java.util.Map: java.lang.Object"
                            + " get(java.lang.Object)>.return",
                    "TRACK_IDENTITY 1 true " + field("java.lang.String name"),
                    "WIRE 1 true " + HANDLE + ".param0:int",
                    "CLOCK 2 true <java.lang.System: long currentTimeMillis()>"
                            + ".return",
                    "CONFIG_FIELD 4 true " + field("boolean flag"),
                    "CONFIG_FIELD 16 true " + field("int limit"),
                    "CUT 16 false " + CHECK + "::$c16",
                    "CONFIG_FIELD 17 true " + field("int limit")), found},
            {"what is not chosen says why: a stream read's value is no "
                    + "door", "IO:NO_DOOR CUT:DISTANCE", cut.trim()},
            {"the configuration minted: the key near the path, and the"
                    + " one near the guard of the tracked count's writer,"
                    + " past the bound on the path's cone",
                    "[CONFIG:k.flag, CONFIG:k.limit]",
                    demand.configSources().toString()},
            {"each measured where it was", "PATH WRITERS",
                    measured(demand, field("int limit"))},
            {"the scope growth demands", "{" + field("int old")
                    + "=PRE_WINDOW, <t.Other: int app()>=SCOPE}",
                    kinds(demand.frontier())},
            {"the scope map's mark of the tracked read", "TRACK 1 true",
                    track.kind + " " + track.distance + " " + track.chosen}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * SYMBOL-SCOPE §4.6: a construction-only field is a PROVENANCE boundary
     * (a read of a decoded object's field reads the store version it was
     * parsed from), and the walk goes on through what its constructor stored
     * -- a processor's copy of its collection's read-only flag leads to the
     * flag read, a boundary of its own, and a container field the flag's
     * construction read holds what that copy's version holds: PROVENANCE,
     * no tracked container (solr-18413 Z3: ZkNodeProps.propMap).  A
     * construction-only field a region stores and a replay versions stays
     * tracked (solr-18413: RoutingRule.expireAt).
     */
    @Test
    public void aConstructionOnlyFieldIsWalkedThroughToWhatItsConstructorStored() {
        scene(new LinkedHashMap<>());
        String z0 = CHECK + "::$z0";
        String init = "<t.T: void <init>(t.D)>";
        String copy = field("boolean copy");
        String flag = "<t.D: java.lang.Boolean flag>";
        String built = "<t.D: void <init>(java.util.Map)>";
        String props = "<t.D: java.util.Map props>";
        // Per row: whether a region stores the flag and a replay versions
        // it, and the boundaries.
        Object[][] rows = {
            {false, Arrays.asList("PROVENANCE 1 true " + copy,
                    "PROVENANCE 3 true " + flag,
                    "PROVENANCE 5 true " + props)},
            {true, Arrays.asList("PROVENANCE 1 true " + copy,
                    "TRACK 3 true " + flag)},
        };
        for (Object[] row : rows) {
            boolean stored = (Boolean) row[0];
            List<Map<String, Object>> edges = new ArrayList<>(Arrays.asList(
                    edge("exception_guard", z0, CHECK + "#u9#exception:E",
                            CHECK, 9, null),
                    edge("field_read", copy, z0, CHECK, 4, null),
                    edge("field_write", init + "::$z1", copy, init, 3, null),
                    edge("accessor_field_return", flag, init + "::$z1", init,
                            2, "<t.D: java.lang.Boolean isFlag()>"),
                    edge("field_write", built + "::$r2", flag, built, 2,
                            null),
                    edge("field_read", props, built + "::$r2", built, 1,
                            null),
                    edge("field_write", RUN + "::$r3", props, RUN, 5,
                            null)));
            if (stored) {
                edges.add(edge("field_write", RUN + "::$z4", flag, RUN, 6,
                        null));
            }
            RootDemand demand = RootDemand.of(edges,
                    Collections.singletonList(region()),
                    Collections.<String, Clock>emptyMap(),
                    ConfigRoots.of(edges, new LinkedHashMap<>()),
                    Collections.singleton(CHECK + "#u9"),
                    field -> stored && field.equals(flag)
                            ? SharedFieldFlow.TrackedKind.VALUE
                            : SharedFieldFlow.TrackedKind.NONE,
                    field -> field.equals(copy) || field.equals(flag),
                    owner -> owner.startsWith("t."), new Faults(),
                    Collections.<DemandedDoors.Site>emptyList());
            List<String> found = new ArrayList<>();
            for (RootDemand.Boundary boundary : demand.boundaries()) {
                found.add(boundary.kind + " " + boundary.distance + " "
                        + boundary.chosen + " " + boundary.cell);
            }
            assertEquals("stored=" + stored, row[1], found);
            assertEquals("the read the scope map marks", (stored ? "TRACK"
                    : "PROVENANCE") + " 3 true",
                    mark(demand.marks().at(init + "#u2", flag)));
            // A PROVENANCE field feeds scope growth as a PRE_WINDOW one
            // does: its writer is a decode's constructor, maybe out of scope.
            assertEquals("stored=" + stored + ": scope growth takes the copy",
                    "PROVENANCE", demand.frontier().get(copy).kind);
        }
    }

    /**
     * SYMBOL-SCOPE §4.4: where a root an occurrence read goes inside it (its
     * influence), and its way into what is demanded.
     */
    @Test
    public void aRootReachesTheStoresItDecidesAndTheWiresItFeeds() {
        List<Map<String, Object>> graph = Arrays.asList(
                edge("local_def_use", ROOT, M + "::$l1", M),
                // the arm the root decides stores the location
                edge("guard_dependency", M + "::$l1", STORED, M),
                edge("local_def_use", M + "::$l1", M + "::$l2", M),
                edge("wire_handoff", M + "::$l2", OTHER + "::$i0", OTHER),
                // an edge of a method this occurrence did not perform
                edge("local_def_use", ROOT, OTHER + "::$x", OTHER),
                // past the store: whoever reads the location next
                edge("field_read", STORED, M + "::$l9", M));
        Map<String, List<String>> methods = new LinkedHashMap<>();
        methods.put("REGION.r", Collections.singletonList(M));
        RootRelevance relevance = new RootRelevance(graph,
                Collections.singleton(STORED), methods);
        RootRelevance.Influence influence = relevance.influence(
                Collections.singletonList("REGION.r"), ROOT);
        Object[][] rows = {
            {"the stored locations it reaches", set(STORED),
                influence.carriers},
            {"the wire consumers its value is handed to",
                set(OTHER + "::$i0"), influence.consumers},
            {"its way into a demanded location",
                set(ROOT, M + "::$l1", STORED),
                influence.through(Collections.singleton(STORED))},
            {"its way into a demanded wire",
                set(ROOT, M + "::$l1", M + "::$l2", OTHER + "::$i0"),
                influence.through(Collections.singleton(OTHER + "::$i0"))},
            {"no way in when nothing is demanded", set(),
                influence.through(Collections.<String>emptySet())},
            {"a region that does not hold the method holds none of it",
                set(), relevance.influence(
                        Collections.singletonList("REGION.q"), ROOT).carriers},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1],
                    new HashSet<>((Set<?>) row[2]));
        }
    }

    private static String mark(StaticScopeMap.Demanded demanded) {
        return demanded.kind + " " + demanded.distance + " "
                + demanded.chosen;
    }

    private static String measured(RootDemand demand, String cell) {
        List<String> found = new ArrayList<>();
        for (RootDemand.Boundary boundary : demand.boundaries()) {
            if (cell.equals(boundary.cell)) found.add(boundary.measured);
        }
        Collections.sort(found);
        return String.join(" ", found);
    }

    /**
     * SYMBOL-SCOPE §4.6: a local file operation is a door only where its
     * outcome reaches what the walk demanded -- a failing result into the
     * path (VALUE), a latent fault skipping a demanded store (ESCAPE) --
     * the doors this pass wove first, the {@value RootDemand#WIDTH}
     * nearest in all, none whose demanded site no region holds (its marker
     * is read where that site runs); a call into the system where one
     * could stand is an IO frontier row of scope growth.
     */
    @Test
    public void aFileFaultIsADoorOnlyWhereItsOutcomeReachesTheSlice() {
        scene(new LinkedHashMap<>());
        String rename = "<java.io.File: boolean renameTo(java.io.File)>";
        String open = "<java.io.FileOutputStream: void <init>(java.io.File)>";
        String z0 = CHECK + "::$z0";
        List<Map<String, Object>> edges = Arrays.asList(
                edge("exception_guard", z0, CHECK + "#u9#exception:E",
                        CHECK, 9, null),
                edge("exception_throw", CHECK + "::$r9",
                        CHECK + "#u10#exception:E", CHECK, 10, null),
                edge("call_return", rename + ".return", z0, CHECK, 3,
                        rename),
                edge("field_read", field("int count"), z0, CHECK, 4, null),
                edge("field_write", RUN + "::$i0", field("int count"), RUN,
                        3, null));
        Faults faults = new Faults();
        faults.latent.add(new RootDemand.Candidate(RUN + "#u1", open, RUN,
                0, 2, RootDemand.ESCAPE, false, VIA, true));
        faults.latent.add(new RootDemand.Candidate(RUN + "#u2",
                "<t.Other: void save()>", RUN, 0, 3, RootDemand.HANDLER,
                true, VIA, true));
        faults.latent.add(new RootDemand.Candidate("<t.T: void close()>#u4",
                open, "<t.T: void close()>", 0, 2, RootDemand.ESCAPE,
                false, Arrays.asList("<t.T: void unheld()>",
                        "<t.T: void close()>"), false));
        faults.latent.add(new RootDemand.Candidate(RUN + "#u30", open, RUN,
                99, 17, RootDemand.ESCAPE, false, VIA, true));
        for (int site = 0; site < 11; site++) {
            faults.latent.add(new RootDemand.Candidate(RUN + "#u" + (10
                    + site), open, RUN, site + 1, 5, RootDemand.HANDLER,
                    false, VIA, true));
        }
        DemandedDoors.Site woven = new DemandedDoors.Site(HANDLE,
                "<java.io.FileOutputStream: void write(byte[])>", 0, 4,
                RootDemand.ESCAPE, Collections.singletonList(HANDLE));
        RootDemand demand = RootDemand.of(edges, Collections.singletonList(
                region()), Collections.<String, Clock>emptyMap(),
                ConfigRoots.of(edges, new LinkedHashMap<>()),
                Collections.singleton(CHECK + "#u9"),
                field -> SharedFieldFlow.TrackedKind.VALUE,
                field -> false, owner -> owner.startsWith("t."), faults,
                Collections.singletonList(woven));
        List<String> doors = new ArrayList<>();
        for (DemandedDoors.Site door : demand.doors()) {
            doors.add(door.caller.equals(CHECK) ? "check " + door.reach
                    : door.key() + " " + door.reach);
        }
        Map<String, Integer> cuts = new LinkedHashMap<>();
        for (RootDemand.Boundary boundary : demand.boundaries()) {
            if (boundary.kind != RootDemand.Kind.IO) continue;
            cuts.merge(boundary.chosen ? boundary.edgeKind : boundary.cut,
                    1, Integer::sum);
        }
        Object[][] rows = {
            {"the walk hands over the demanded store and the target's path",
                "{" + RUN + "#u3=1} [" + CHECK + "#u9, " + CHECK + "#u10]",
                faults.stores + " " + faults.path},
            {"the woven door first, then nearest first, 12 in all",
                Arrays.asList(woven.key() + " ESCAPE", "check VALUE",
                        RUN + "|" + open + "|0 ESCAPE", RUN + "|" + open
                                + "|1 HANDLER"), doors.subList(0, 4)},
            {"twelve doors", 12, doors.size()},
            {"every IO row says why it is or is not a door",
                "{call_return=1, door=1, fault_escape=1, fault_frontier=1, "
                        + "fault_handler=9, DISTANCE=1, NO_REGION=1, "
                        + "WIDTH=2}",
                ordered(cuts)},
            {"the IO frontier joins scope growth's demanded rows",
                "IO 3", demand.frontier().get("<t.Other: void save()>").kind
                        + " " + demand.frontier().get(
                                "<t.Other: void save()>").distance}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * A demanded door's result is an IO boundary even where the analyzer's
     * operand edges carry the call (a timed wait's timeout local reaches its
     * return through a {@code local_def_use} naming the call, as a rename's
     * target does): {@code if (!lock.tryLock(t, u))} on the path is a VALUE
     * door, never walked through.
     */
    @Test
    public void aDoorsResultIsABoundaryWhateverItsOperandsCarry() {
        scene(new LinkedHashMap<>());
        String z0 = CHECK + "::$z0";
        Object[][] rows = {
            {"<java.util.concurrent.locks.Lock: boolean tryLock(long,"
                    + "java.util.concurrent.TimeUnit)>"},
            {"<java.io.File: boolean renameTo(java.io.File)>"},
        };
        for (Object[] row : rows) {
            String callee = (String) row[0];
            List<Map<String, Object>> edges = Arrays.asList(
                    edge("exception_guard", z0, CHECK + "#u9#exception:E",
                            CHECK, 9, null),
                    edge("call_return", callee + ".return", z0, CHECK, 3,
                            callee),
                    edge("local_def_use", CHECK + "::$l1", z0, CHECK, 3,
                            callee));
            Faults faults = new Faults();
            RootDemand demand = RootDemand.of(edges, Collections
                    .singletonList(region()), Collections.<String,
                    Clock>emptyMap(), ConfigRoots.of(edges,
                    new LinkedHashMap<>()), Collections.singleton(CHECK
                    + "#u9"), field -> SharedFieldFlow.TrackedKind.NONE,
                    field -> false, owner -> owner.startsWith("t."), faults,
                    Collections.<DemandedDoors.Site>emptyList());
            List<String> doors = new ArrayList<>();
            for (DemandedDoors.Site door : demand.doors()) {
                doors.add(door.callee + " " + door.reach);
            }
            assertEquals(callee, Collections.singletonList(callee
                    + " VALUE"), doors);
        }
    }

    private static String kinds(
            Map<String, StaticScopeMap.Demanded> frontier) {
        Map<String, String> kinds = new LinkedHashMap<>();
        for (Map.Entry<String, StaticScopeMap.Demanded> row
                : frontier.entrySet()) {
            kinds.put(row.getKey(), row.getValue().kind);
        }
        return kinds.toString();
    }

    /** Chosen edge kinds first, then cuts, each in name order. */
    private static String ordered(Map<String, Integer> counts) {
        Map<String, Integer> sorted = new java.util.TreeMap<>(
                (a, b) -> Character.isUpperCase(a.charAt(0))
                        == Character.isUpperCase(b.charAt(0))
                        ? a.compareTo(b)
                        : Character.isUpperCase(a.charAt(0)) ? 1 : -1);
        sorted.putAll(counts);
        return sorted.toString();
    }

    private static Set<String> set(String... cells) {
        return new HashSet<>(Arrays.asList(cells));
    }

    private static Map<String, Object> region() {
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("regionId", "REGION.r");
        region.put("rootMethod", HANDLE);
        region.put("methods", Arrays.asList(HANDLE, RUN, CHECK));
        return region;
    }

    /** A stub of the Soot side: a failing result at each File call, the
     *  latent faults it is given, the woven door at HANDLE#u7. */
    private static final class Faults implements RootDemand.Faults {
        final List<RootDemand.Candidate> latent = new ArrayList<>();
        Map<String, Integer> stores;
        java.util.Set<String> path;

        @Override
        public RootDemand.Candidate valued(String siteId, String callee) {
            return callee.startsWith("<java.io.File: ")
                    || callee.startsWith("<java.util.concurrent.locks.Lock: ")
                    ? new RootDemand.Candidate(siteId, callee, CHECK, 0, 0,
                    RootDemand.VALUE, false, Collections.singletonList(
                    CHECK), true) : null;
        }

        @Override
        public List<RootDemand.Candidate> latent(
                Map<String, Integer> demanded, Map<String, Integer> stores,
                java.util.Set<String> path) {
            this.stores = stores;
            this.path = path;
            return latent;
        }

        @Override
        public String site(DemandedDoors.Site door) {
            return HANDLE + "#u7";
        }
    }

    private static String field(String declared) {
        return "<" + T + ": " + declared + ">";
    }

    /**
     * {@code check}'s guard at u9 reads a clock, the fields {@code count}
     * (stored by {@code run}, under {@code flag}, and only where a call
     * decided on {@code limit} 14 copies away let it), {@code name} ({@code
     * run}), {@code old} (stored outside every region), an atomic, a
     * stream, a map, another class of the system and {@code handle}'s
     * formal; and, 17 copies away, another clock.
     */
    private static List<Map<String, Object>> edges() {
        String z0 = CHECK + "::$z0";
        List<Map<String, Object>> edges = new ArrayList<>(Arrays.asList(
                edge("exception_guard", z0, CHECK + "#u9#exception:E",
                        CHECK, 9, null),
                edge("local_def_use", CHECK + "::$i0", z0, CHECK, 2, null),
                edge("call_return",
                        "<java.lang.System: long currentTimeMillis()>.return",
                        CHECK + "::$i0", CHECK, 3,
                        "<java.lang.System: long currentTimeMillis()>"),
                edge("field_read", field("int count"), z0, CHECK, 4, null),
                edge("field_write", RUN + "::$i0", field("int count"), RUN,
                        3, null),
                edge("guard_dependency", RUN + "::$z1", RUN + "::$i0", RUN,
                        2, null),
                edge("field_read", field("boolean flag"), RUN + "::$z1", RUN,
                        1, null),
                edge("field_read", field("java.lang.String name"), z0, CHECK,
                        5, null),
                edge("field_write", RUN + "::$r0",
                        field("java.lang.String name"), RUN, 4, null),
                edge("field_read", field("int old"), z0, CHECK, 6, null),
                edge("field_write", "<t.T: void legacy()>::$i0",
                        field("int old"), "<t.T: void legacy()>", 1, null),
                edge("accessor_field_return",
                        "<java.util.concurrent.atomic.AtomicInteger: int "
                                + "value>", z0, CHECK, 7,
                        "<java.util.concurrent.atomic.AtomicInteger: int "
                                + "get()>"),
                edge("call_return", "<java.io.FileInputStream: int read()>"
                        + ".return", z0, CHECK, 8,
                        "<java.io.FileInputStream: int read()>"),
                edge("call_return", "<java.util.Map: java.lang.Object get("
                        + "java.lang.Object)>.return", z0, CHECK, 10,
                        "<java.util.Map: java.lang.Object get("
                                + "java.lang.Object)>"),
                edge("call_return", "<t.Other: int app()>.return", z0, CHECK,
                        11, "<t.Other: int app()>"),
                edge("local_def_use", HANDLE + ".param0:int", z0, CHECK, 12,
                        null)));
        edges.add(edge("guard_dependency", RUN + "::$z2", field("int count"),
                RUN, 0, null));
        String guard = RUN + "::$z2";
        for (int copy = 1; copy <= 14; copy++) {
            String from = RUN + "::$d" + copy;
            edges.add(edge("local_def_use", from, guard, RUN, 10 + copy,
                    null));
            guard = from;
        }
        edges.add(edge("field_read", field("int limit"), guard, RUN, 30,
                null));
        String to = z0;
        for (int copy = 1; copy <= 17; copy++) {
            String from = CHECK + "::$c" + copy;
            edges.add(edge("local_def_use", from, to, CHECK, 20 + copy,
                    null));
            to = from;
        }
        edges.add(edge("call_return",
                "<java.lang.System: long nanoTime()>.return", to, CHECK, 40,
                "<java.lang.System: long nanoTime()>"));
        return edges;
    }

    /** {@code t.T}'s constructor stores {@code flag} and {@code limit}
     *  from a Configuration. */
    private static void scene(Map<String, List<String>> writers) {
        String conf = "org.apache.hadoop.conf.Configuration";
        JimpleScene.load(JimpleScene.OBJECT,
                "public class java.lang.String extends java.lang.Object { }",
                "public class " + conf + " extends java.lang.Object {"
                        + " public native boolean getBoolean(java.lang.String,"
                        + " boolean); public native int getInt("
                        + "java.lang.String, int); }",
                "application public class " + T + " extends java.lang.Object"
                        + " { boolean flag; int count; int limit;"
                        + " public void <init>(" + conf + ") { " + T + " r0; "
                        + conf + " r1; boolean $z0; int $i1; r0 := @this: " + T
                        + "; r1 := @parameter0: " + conf + "; $z0 ="
                        + " virtualinvoke r1.<" + conf + ": boolean getBoolean("
                        + "java.lang.String,boolean)>(\"k.flag\", 0); r0."
                        + field("boolean flag") + " = $z0; $i1 = virtualinvoke"
                        + " r1.<" + conf + ": int getInt(java.lang.String,"
                        + "int)>(\"k.limit\", 0); r0." + field("int limit")
                        + " = $i1; return; } }");
        String init = "<" + T + ": void <init>(" + conf + ")>";
        writers.put(field("boolean flag"),
                Collections.singletonList(init + "#u3"));
        writers.put(field("int limit"),
                Collections.singletonList(init + "#u5"));
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String method) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", kind);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        edge.put("method", method);
        return edge;
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String method,
                                            int unitIndex, String invoke) {
        Map<String, Object> edge = edge(kind, from, to, method);
        edge.put("unitIndex", unitIndex);
        edge.put("siteId", method + "#u" + unitIndex);
        if (invoke != null) edge.put("invoke", invoke);
        return edge;
    }
}
