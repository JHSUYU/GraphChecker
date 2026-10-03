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
                owner -> owner.startsWith("t."));
        List<String> found = new ArrayList<>();
        String cut = "";
        for (RootDemand.Boundary boundary : demand.boundaries()) {
            found.add(boundary.kind + " " + boundary.distance + " "
                    + boundary.chosen + " " + boundary.cell);
            if (!boundary.chosen) cut += boundary.kind + ":" + boundary.cut;
        }
        StaticScopeMap.Demanded track = demand.marks().at(CHECK + "#u4",
                field("int count"));
        Object[][] rows = {
            {"the boundaries, nearest first; the clock past the bound is "
                    + "none, the path to it named where it was cut, the "
                    + "configuration behind the tracked count found on the "
                    + "cone", Arrays.asList(
                    "IO 1 true <java.io.FileInputStream: int read()>.return",
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
            {"what is not chosen says why", "CUT:DISTANCE", cut},
            {"the configuration minted", "[CONFIG:k.flag]",
                    demand.configSources().toString()},
            {"the scope growth demands", "{" + field("int old")
                    + "=PRE_WINDOW, <t.Other: int app()>=SCOPE}",
                    demand.frontier().toString()},
            {"the scope map's mark of the tracked read", "TRACK 1 true",
                    track.kind + " " + track.distance + " " + track.chosen}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
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
