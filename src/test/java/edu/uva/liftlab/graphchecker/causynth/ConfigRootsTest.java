package edu.uva.liftlab.graphchecker.causynth;

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
import soot.Unit;
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
 * SYMBOL-SCOPE §4.3: which reads are configuration, under which key, minted
 * in which shape, with which domain.
 */
public class ConfigRootsTest {
    private static final String CONF = "org.apache.hadoop.conf.Configuration";
    private static final String MANAGER = "t.Manager";
    private static final Jimple J = Jimple.v();

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aConfigurationIsReadAtOneFieldOrAtItsGetterReturns() {
        Map<String, List<String>> writers = new LinkedHashMap<>();
        List<Map<String, Object>> edges = new ArrayList<>();
        scene(writers, edges);
        ConfigRoots roots = ConfigRoots.of(edges, writers);
        Object[][] rows = {
            {"a field its constructor stores from a getter, a boolean",
                "CONFIG:k.ordered boolean [,]", source(roots.field(
                        field("boolean ordered")))},
            {"a clamp keeps the key; the default and a compared literal "
                    + "+-1 are its domain", "CONFIG:k.limit int [5,11]",
                source(roots.field(field("int limit")))},
            {"a second writer storing anything else is no configuration",
                "null", source(roots.field(field("int counter")))},
            {"a wrapper's literal key, past the initializer's constant",
                "CONFIG:k.legacy boolean [,]", source(roots.field(
                        field("boolean legacy")))},
            {"a key a field holds is minted at the field, not its getter",
                "null", source(roots.call(run(), 3,
                        "<t.Manager: boolean legacy(" + CONF + ")>"))},
            {"a key no field holds is minted at each getter return",
                "CONFIG:k.only int [3,3]", source(roots.call(run(), 4,
                        "<" + CONF + ": int getInt(java.lang.String,int)>"))},
            {"a getter called on a subclass is the catalog's",
                "CONFIG:k.sub int [2,2]", source(roots.call(run(), 5,
                        "<org.apache.hadoop.hdfs.HdfsConfiguration: int "
                                + "getInt(java.lang.String,int)>"))},
            {"every configuration field of the slice, declared or not",
                "[true, false]", Arrays.asList(roots.configField(field(
                        "boolean ordered")), roots.configField(field(
                        "int counter"))).toString()}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static String source(ConfigRoots.Source source) {
        return source == null ? "null" : source.sourceId + " "
                + source.javaType + " [" + source.domainMin + ","
                + source.domainMax + "]";
    }

    private static String field(String declared) {
        return "<" + MANAGER + ": " + declared + ">";
    }

    private static String run() {
        return "<" + MANAGER + ": void run(" + CONF + ")>";
    }

    /**
     * {@code t.Manager}'s constructor stores {@code ordered}, {@code limit}
     * (clamped), {@code counter} (which {@code bump} also counts) and {@code
     * legacy} (initialized false, then a wrapper's answer) from a {@code
     * Configuration}; {@code check} compares {@code limit} with 10; {@code
     * run} calls the wrapper and two getters, one through {@code
     * HdfsConfiguration}.
     */
    private static void scene(Map<String, List<String>> writers,
                              List<Map<String, Object>> edges) {
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null);
        SootClass string = library("java.lang.String", object);
        RefType text = string.getType();
        SootMethod equals = method(string, "equals",
                Collections.<Type>singletonList(object.getType()),
                BooleanType.v(), Modifier.NATIVE);
        SootClass math = library("java.lang.Math", object);
        SootMethod max = method(math, "max", Arrays.<Type>asList(
                IntType.v(), IntType.v()), IntType.v(),
                Modifier.STATIC | Modifier.NATIVE);
        SootClass conf = library(CONF, object);
        SootMethod getBoolean = method(conf, "getBoolean", Arrays.<Type>asList(
                text, BooleanType.v()), BooleanType.v(), Modifier.NATIVE);
        SootMethod getInt = method(conf, "getInt", Arrays.<Type>asList(text,
                IntType.v()), IntType.v(), Modifier.NATIVE);
        SootMethod get = method(conf, "get", Collections.<Type>singletonList(
                text), text, Modifier.NATIVE);
        SootClass hdfs = library("org.apache.hadoop.hdfs.HdfsConfiguration",
                conf);

        SootClass manager = library(MANAGER, object);
        manager.setApplicationClass();
        RefType self = manager.getType();
        SootField ordered = field(manager, "ordered", BooleanType.v());
        SootField limit = field(manager, "limit", IntType.v());
        SootField counter = field(manager, "counter", IntType.v());
        SootField legacy = field(manager, "legacy", BooleanType.v());

        SootMethod wrapper = method(manager, "legacy",
                Collections.<Type>singletonList(conf.getType()),
                BooleanType.v(), Modifier.STATIC);
        Local w0 = local(wrapper, "r0", conf.getType());
        Local w1 = local(wrapper, "$r1", text);
        Local w2 = local(wrapper, "$z0", BooleanType.v());
        Local w3 = local(wrapper, "$r2", text);
        body(wrapper, J.newIdentityStmt(w0, J.newParameterRef(conf.getType(),
                        0)),
                J.newAssignStmt(w1, J.newVirtualInvokeExpr(w0, get.makeRef(),
                        StringConstant.v("k.legacy"))),
                J.newAssignStmt(w3, StringConstant.v("true")),
                J.newAssignStmt(w2, J.newVirtualInvokeExpr(w3,
                        equals.makeRef(), w1)),
                J.newReturnStmt(w2));

        SootMethod init = method(manager, "<init>",
                Collections.<Type>singletonList(conf.getType()),
                VoidType.v(), 0);
        Local i0 = local(init, "r0", self);
        Local i1 = local(init, "r1", conf.getType());
        Local z0 = local(init, "$z0", BooleanType.v());
        Local n0 = local(init, "$i0", IntType.v());
        Local n1 = local(init, "$i1", IntType.v());
        Local n2 = local(init, "$i2", IntType.v());
        Local z1 = local(init, "$z1", BooleanType.v());
        body(init, J.newIdentityStmt(i0, J.newThisRef(self)),
                J.newIdentityStmt(i1, J.newParameterRef(conf.getType(), 0)),
                store(i0, legacy, IntConstant.v(0)),
                J.newAssignStmt(z0, J.newVirtualInvokeExpr(i1,
                        getBoolean.makeRef(), StringConstant.v("k.ordered"),
                        IntConstant.v(0))),
                store(i0, ordered, z0),
                J.newAssignStmt(n0, J.newVirtualInvokeExpr(i1,
                        getInt.makeRef(), StringConstant.v("k.limit"),
                        IntConstant.v(5))),
                J.newAssignStmt(n1, J.newStaticInvokeExpr(max.makeRef(), n0,
                        IntConstant.v(1))),
                store(i0, limit, n1),
                J.newAssignStmt(n2, J.newVirtualInvokeExpr(i1,
                        getInt.makeRef(), StringConstant.v("k.counter"),
                        IntConstant.v(0))),
                store(i0, counter, n2),
                J.newAssignStmt(z1, J.newStaticInvokeExpr(wrapper.makeRef(),
                        i1)),
                store(i0, legacy, z1),
                J.newReturnVoidStmt());
        String initSig = init.getSignature();
        writers.put(field("boolean ordered"),
                Collections.singletonList(initSig + "#u4"));
        writers.put(field("int limit"),
                Collections.singletonList(initSig + "#u7"));
        writers.put(field("boolean legacy"),
                Arrays.asList(initSig + "#u2", initSig + "#u11"));

        SootMethod bump = method(manager, "bump",
                Collections.<Type>emptyList(), VoidType.v(), 0);
        Local b0 = local(bump, "r0", self);
        Local b1 = local(bump, "$i0", IntType.v());
        Local b2 = local(bump, "$i1", IntType.v());
        body(bump, J.newIdentityStmt(b0, J.newThisRef(self)),
                J.newAssignStmt(b1, J.newInstanceFieldRef(b0,
                        counter.makeRef())),
                J.newAssignStmt(b2, J.newAddExpr(b1, IntConstant.v(1))),
                store(b0, counter, b2), J.newReturnVoidStmt());
        writers.put(field("int counter"), Arrays.asList(initSig + "#u9",
                bump.getSignature() + "#u3"));

        SootMethod check = method(manager, "check",
                Collections.<Type>emptyList(), VoidType.v(), 0);
        Local c0 = local(check, "r0", self);
        Local c1 = local(check, "$i0", IntType.v());
        Unit done = J.newReturnVoidStmt();
        body(check, J.newIdentityStmt(c0, J.newThisRef(self)),
                J.newAssignStmt(c1, J.newInstanceFieldRef(c0,
                        limit.makeRef())),
                J.newIfStmt(J.newLeExpr(c1, IntConstant.v(10)), done),
                J.newInvokeStmt(J.newVirtualInvokeExpr(c0, bump.makeRef())),
                done);
        String checkSig = check.getSignature();
        String limitLocal = checkSig + "::$i0";
        edges.add(edge("field_read", field("int limit"), limitLocal,
                checkSig, 1, null));
        edges.add(edge("guard_dependency", limitLocal, checkSig + "#u2",
                checkSig, 2, null));
        for (String read : new String[]{"boolean ordered", "int counter",
                "boolean legacy"}) {
            edges.add(edge("field_read", field(read), checkSig + "::x",
                    checkSig, 1, null));
        }

        SootMethod runs = method(manager, "run",
                Collections.<Type>singletonList(conf.getType()),
                VoidType.v(), 0);
        Local r0 = local(runs, "r0", self);
        Local r1 = local(runs, "r1", conf.getType());
        Local r2 = local(runs, "$z0", BooleanType.v());
        Local r3 = local(runs, "$i0", IntType.v());
        Local r4 = local(runs, "$r2", hdfs.getType());
        Local r5 = local(runs, "$i1", IntType.v());
        body(runs, J.newIdentityStmt(r0, J.newThisRef(self)),
                J.newIdentityStmt(r1, J.newParameterRef(conf.getType(), 0)),
                J.newAssignStmt(r4, J.newCastExpr(r1, hdfs.getType())),
                J.newAssignStmt(r2, J.newStaticInvokeExpr(wrapper.makeRef(),
                        r1)),
                J.newAssignStmt(r3, J.newVirtualInvokeExpr(r1,
                        getInt.makeRef(), StringConstant.v("k.only"),
                        IntConstant.v(3))),
                J.newAssignStmt(r5, J.newVirtualInvokeExpr(r4,
                        Scene.v().makeMethodRef(hdfs, "getInt",
                                Arrays.<Type>asList(text, IntType.v()),
                                IntType.v(), false),
                        StringConstant.v("k.sub"), IntConstant.v(2))),
                J.newReturnVoidStmt());
        String runSig = runs.getSignature();
        edges.add(edge("call_return", wrapper.getSignature() + ".return",
                runSig + "::$z0", runSig, 3, wrapper.getSignature()));
        edges.add(edge("call_return", getInt.getSignature() + ".return",
                runSig + "::$i0", runSig, 4, getInt.getSignature()));
        String sub = "<org.apache.hadoop.hdfs.HdfsConfiguration: int "
                + "getInt(java.lang.String,int)>";
        edges.add(edge("call_return", sub + ".return", runSig + "::$i1",
                runSig, 5, sub));
    }

    private static Unit store(Local owner, SootField field,
                              soot.Value value) {
        return J.newAssignStmt(J.newInstanceFieldRef(owner, field.makeRef()),
                value);
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
        if (invoke != null) edge.put("invoke", invoke);
        return edge;
    }

    private static SootClass library(String name, SootClass parent) {
        SootClass type = new SootClass(name, Modifier.PUBLIC);
        if (parent != null) type.setSuperclass(parent);
        Scene.v().addClass(type);
        return type;
    }

    private static SootField field(SootClass owner, String name, Type type) {
        SootField field = new SootField(name, type, 0);
        owner.addField(field);
        return field;
    }

    private static SootMethod method(SootClass owner, String name,
                                     List<Type> parameters, Type returned,
                                     int modifiers) {
        SootMethod method = new SootMethod(name, parameters, returned,
                Modifier.PUBLIC | modifiers);
        owner.addMethod(method);
        if ((modifiers & Modifier.NATIVE) == 0) {
            method.setActiveBody(J.newBody(method));
        }
        return method;
    }

    private static Local local(SootMethod method, String name, Type type) {
        Local local = J.newLocal(name, type);
        method.getActiveBody().getLocals().add(local);
        return local;
    }

    private static void body(SootMethod method, Unit... units) {
        method.getActiveBody().getUnits().addAll(Arrays.asList(units));
    }
}
