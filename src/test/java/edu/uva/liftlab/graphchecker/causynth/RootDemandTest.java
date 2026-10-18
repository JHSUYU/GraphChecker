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

    private static String measured(RootDemand demand, String cell) {
        List<String> found = new ArrayList<>();
        for (RootDemand.Boundary boundary : demand.boundaries()) {
            if (cell.equals(boundary.cell)) found.add(boundary.measured);
        }
        Collections.sort(found);
        return String.join(" ", found);
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
