package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.After;
import org.junit.Test;
import soot.BooleanType;
import soot.G;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.StringConstant;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

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
    private static final Jimple J = Jimple.v();
    /** A door's chain: chosen at RUN's store, standing in RUN. */
    private static final List<String> VIA = Collections.singletonList(RUN);

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
                owner -> owner.startsWith("t."), new Faults(),
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
                    "CUT 16 false " + CHECK + "::$c16"), found},
            {"what is not chosen says why: a stream read's value is no "
                    + "door", "IO:NO_DOOR CUT:DISTANCE", cut.trim()},
            {"the configuration minted", "[CONFIG:k.flag]",
                    demand.configSources().toString()},
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
                owner -> owner.startsWith("t."), faults,
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
     * (stored by {@code run}, under {@code flag}), {@code name} ({@code
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

    /** {@code t.T}'s constructor stores {@code flag} from a Configuration. */
    private static void scene(Map<String, List<String>> writers) {
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null);
        RefType text = library("java.lang.String", object).getType();
        SootClass conf = library("org.apache.hadoop.conf.Configuration",
                object);
        SootMethod getBoolean = new SootMethod("getBoolean",
                Arrays.<Type>asList(text, BooleanType.v()), BooleanType.v(),
                Modifier.PUBLIC | Modifier.NATIVE);
        conf.addMethod(getBoolean);
        SootClass type = library(T, object);
        type.setApplicationClass();
        SootField flag = new SootField("flag", BooleanType.v(), 0);
        type.addField(flag);
        type.addField(new SootField("count", IntType.v(), 0));
        SootMethod init = new SootMethod("<init>",
                Collections.<Type>singletonList(conf.getType()),
                VoidType.v(), Modifier.PUBLIC);
        type.addMethod(init);
        init.setActiveBody(J.newBody(init));
        Local self = J.newLocal("r0", type.getType());
        Local source = J.newLocal("r1", conf.getType());
        Local read = J.newLocal("$z0", BooleanType.v());
        init.getActiveBody().getLocals().addAll(Arrays.asList(self, source,
                read));
        init.getActiveBody().getUnits().addAll(Arrays.asList(
                J.newIdentityStmt(self, J.newThisRef(type.getType())),
                J.newIdentityStmt(source, J.newParameterRef(conf.getType(),
                        0)),
                J.newAssignStmt(read, J.newVirtualInvokeExpr(source,
                        getBoolean.makeRef(), StringConstant.v("k.flag"),
                        IntConstant.v(0))),
                J.newAssignStmt(J.newInstanceFieldRef(self, flag.makeRef()),
                        read),
                J.newReturnVoidStmt()));
        writers.put(field("boolean flag"),
                Collections.singletonList(init.getSignature() + "#u3"));
    }

    private static SootClass library(String name, SootClass parent) {
        SootClass type = new SootClass(name, Modifier.PUBLIC);
        if (parent != null) type.setSuperclass(parent);
        Scene.v().addClass(type);
        return type;
    }

    private static Map<String, Object> edge(String kind, String from,
                                            String to, String method,
                                            int unitIndex, String invoke) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("kind", kind);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        edge.put("method", method);
        edge.put("unitIndex", unitIndex);
        edge.put("siteId", method + "#u" + unitIndex);
        if (invoke != null) edge.put("invoke", invoke);
        return edge;
    }
}
