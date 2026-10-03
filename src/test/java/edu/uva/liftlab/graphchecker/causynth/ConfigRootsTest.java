package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.BooleanType;
import soot.G;
import soot.IntType;
import soot.LongType;
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
import soot.jimple.LongConstant;
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
        String getInt = "<" + CONF + ": int getInt(java.lang.String,int)>";
        Object[][] rows = {
            {"a field its constructor stores from a getter, a boolean",
                "CONFIG:k.ordered boolean [,]", source(roots.field(
                        field("boolean ordered")))},
            {"a clamp keeps the key; the default and a compared literal "
                    + "+-1 are its domain", "CONFIG:k.limit int [5,11]",
                source(roots.field(field("int limit")))},
            {"a clamp bounds the domain: Math.max(v, 1) is never 0",
                "CONFIG:k.low int [1,4]", source(roots.field(
                        field("int low")))},
            {"a constant stored after the configuration (if (f <= 0) f = 1)"
                    + " leaves the field no root", "null false true",
                source(roots.field(field("int san"))) + " "
                        + roots.fields().containsKey(field("int san")) + " "
                        + roots.configField(field("int san"))},
            {"a second writer storing anything else is no configuration",
                "null", source(roots.field(field("int counter")))},
            {"a view's literal is part of the root, past the initializer's"
                    + " constant", "CONFIG:k.legacy==true boolean [,]",
                source(roots.field(field("boolean legacy")))},
            {"a key a field holds is minted at the field, not its getter",
                "null", source(roots.call(run(), 3,
                        "<t.Manager: boolean legacy(" + CONF + ")>"))},
            {"the getter call a field's writer stores is the field's read: "
                    + "no root, no gap", "null", source(roots.call(
                        "<t.Manager: void <init>(" + CONF + ")>", 3, "<"
                        + CONF + ": boolean getBoolean(java.lang.String,"
                        + "boolean)>"))},
            {"a key no field holds is minted at each getter return of its"
                    + " shape, whatever its default",
                "CONFIG:k.only int [3,7] CONFIG:k.only int [3,7]",
                source(roots.call(run(), 4, getInt)) + " "
                        + source(roots.call(run(), 8, getInt))},
            {"a read of the key under another type is read concretely",
                "null", source(roots.call(run(), 9, "<" + CONF
                        + ": long getLong(java.lang.String,long)>"))},
            {"a key no literal names is no root", "null",
                source(roots.call(run(), 7, getInt))},
            {"two views of one key: the first by site is the root",
                "CONFIG:k.mode==a boolean [,] null",
                source(roots.call(run(), 10, "<t.Manager: boolean isA("
                        + CONF + ")>")) + " " + source(roots.call(run(), 11,
                        "<t.Manager: boolean isB(" + CONF + ")>"))},
            {"a wrapper's clamp bounds its domain; the getter in its body is"
                    + " its own read", "CONFIG:k.w int [2,2] null",
                source(roots.call(run(), 12, "<t.Manager: int limitOf("
                        + CONF + ")>")) + " " + source(roots.call(
                        "<t.Manager: int limitOf(" + CONF + ")>", 1,
                        getInt))},
            {"a getter called on a subclass is the catalog's",
                "CONFIG:k.sub int [2,2]", source(roots.call(run(), 5,
                        "<org.apache.hadoop.hdfs.HdfsConfiguration: int "
                                + "getInt(java.lang.String,int)>"))},
            {"every configuration field of the slice, declared or not",
                "[true, false]", Arrays.asList(roots.configField(field(
                        "boolean ordered")), roots.configField(field(
                        "int counter"))).toString()},
            {"what no root mints is named, by reason and site",
                "[CONFIG_FIELD_OVERWRITTEN@<t.Manager: void <init>("
                        + CONF + ")>#u19, CONFIG_READ_CONCRETE@" + run()
                        + "#u3, CONFIG_KEY_UNRESOLVED@" + run() + "#u7,"
                        + " CONFIG_READ_CONCRETE@" + run() + "#u9,"
                        + " CONFIG_READ_CONCRETE@" + run() + "#u11]",
                gaps(roots)},
            {"beside a root the demand left unchosen, a concrete read is no"
                    + " gap", "[CONFIG_FIELD_OVERWRITTEN@<t.Manager: void"
                    + " <init>(" + CONF + ")>#u19, CONFIG_KEY_UNRESOLVED@"
                    + run() + "#u7, CONFIG_READ_CONCRETE@" + run() + "#u9]",
                gaps(roots.limitedTo(Collections.singleton(
                        "CONFIG:k.only")))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static String gaps(ConfigRoots roots) {
        List<String> found = new ArrayList<>();
        for (Map<String, Object> gap : roots.gaps()) {
            found.add(gap.get("reason") + "@" + gap.get("siteId"));
        }
        return found.toString();
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
     * and {@code low} (clamped), {@code counter} (which {@code bump} also
     * counts), {@code legacy} (initialized false, then a wrapper's answer)
     * and {@code san} (then set to 1 where it is not positive) from a {@code
     * Configuration}; {@code check} compares {@code limit} with 10, {@code
     * checkLow} {@code low} with 3; {@code run} calls the wrappers ({@code
     * legacy}, the views {@code isA} and {@code isB}, the clamp {@code
     * limitOf}) and the getters: {@code k.only} with two defaults and as a
     * {@code long}, a key no literal names, one through {@code
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
        RefType confType = conf.getType();
        SootMethod getBoolean = method(conf, "getBoolean", Arrays.<Type>asList(
                text, BooleanType.v()), BooleanType.v(), Modifier.NATIVE);
        SootMethod getInt = method(conf, "getInt", Arrays.<Type>asList(text,
                IntType.v()), IntType.v(), Modifier.NATIVE);
        SootMethod getLong = method(conf, "getLong", Arrays.<Type>asList(text,
                LongType.v()), LongType.v(), Modifier.NATIVE);
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
        SootField low = field(manager, "low", IntType.v());
        SootField san = field(manager, "san", IntType.v());

        SootMethod wrapper = view(manager, "legacy", "k.legacy", "true",
                confType, text, get, equals);
        SootMethod isA = view(manager, "isA", "k.mode", "a", confType, text,
                get, equals);
        SootMethod isB = view(manager, "isB", "k.mode", "b", confType, text,
                get, equals);
        SootMethod limitOf = method(manager, "limitOf",
                Collections.<Type>singletonList(confType), IntType.v(),
                Modifier.STATIC);
        Local l0 = local(limitOf, "r0", confType);
        Local l1 = local(limitOf, "$i0", IntType.v());
        Local l2 = local(limitOf, "$i1", IntType.v());
        body(limitOf, J.newIdentityStmt(l0, J.newParameterRef(confType, 0)),
                J.newAssignStmt(l1, J.newVirtualInvokeExpr(l0,
                        getInt.makeRef(), StringConstant.v("k.w"),
                        IntConstant.v(0))),
                J.newAssignStmt(l2, J.newStaticInvokeExpr(max.makeRef(), l1,
                        IntConstant.v(2))),
                J.newReturnStmt(l2));

        SootMethod init = method(manager, "<init>",
                Collections.<Type>singletonList(confType), VoidType.v(), 0);
        Local i0 = local(init, "r0", self);
        Local i1 = local(init, "r1", confType);
        Local z0 = local(init, "$z0", BooleanType.v());
        Local n0 = local(init, "$i0", IntType.v());
        Local n1 = local(init, "$i1", IntType.v());
        Local n2 = local(init, "$i2", IntType.v());
        Local z1 = local(init, "$z1", BooleanType.v());
        Local n3 = local(init, "$i3", IntType.v());
        Local n4 = local(init, "$i4", IntType.v());
        Local n5 = local(init, "$i5", IntType.v());
        Local n6 = local(init, "$i6", IntType.v());
        Unit initDone = J.newReturnVoidStmt();
        body(init, J.newIdentityStmt(i0, J.newThisRef(self)),
                J.newIdentityStmt(i1, J.newParameterRef(confType, 0)),
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
                J.newAssignStmt(n3, J.newVirtualInvokeExpr(i1,
                        getInt.makeRef(), StringConstant.v("k.low"),
                        IntConstant.v(0))),
                J.newAssignStmt(n4, J.newStaticInvokeExpr(max.makeRef(), n3,
                        IntConstant.v(1))),
                store(i0, low, n4),
                J.newAssignStmt(n5, J.newVirtualInvokeExpr(i1,
                        getInt.makeRef(), StringConstant.v("k.san"),
                        IntConstant.v(5))),
                store(i0, san, n5),
                J.newAssignStmt(n6, J.newInstanceFieldRef(i0, san.makeRef())),
                J.newIfStmt(J.newGtExpr(n6, IntConstant.v(0)), initDone),
                store(i0, san, IntConstant.v(1)),
                initDone);
        String initSig = init.getSignature();
        writers.put(field("boolean ordered"),
                Collections.singletonList(initSig + "#u4"));
        writers.put(field("int limit"),
                Collections.singletonList(initSig + "#u7"));
        writers.put(field("boolean legacy"),
                Arrays.asList(initSig + "#u2", initSig + "#u11"));
        writers.put(field("int low"),
                Collections.singletonList(initSig + "#u14"));
        writers.put(field("int san"),
                Arrays.asList(initSig + "#u16", initSig + "#u19"));

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

        compare(manager, self, "check", limit, 10, bump, edges);
        compare(manager, self, "checkLow", low, 3, bump, edges);
        String checkSig = "<" + MANAGER + ": void check()>";
        for (String read : new String[]{"boolean ordered", "int counter",
                "boolean legacy", "int san"}) {
            edges.add(edge("field_read", field(read), checkSig + "::x",
                    checkSig, 1, null));
        }

        SootMethod runs = method(manager, "run",
                Collections.<Type>singletonList(confType), VoidType.v(), 0);
        Local r0 = local(runs, "r0", self);
        Local r1 = local(runs, "r1", confType);
        Local r2 = local(runs, "$z0", BooleanType.v());
        Local r3 = local(runs, "$i0", IntType.v());
        Local r4 = local(runs, "$r2", hdfs.getType());
        Local r5 = local(runs, "$i1", IntType.v());
        Local name = local(runs, "$r3", text);
        Local r6 = local(runs, "$i2", IntType.v());
        Local r7 = local(runs, "$i3", IntType.v());
        Local r8 = local(runs, "$l0", LongType.v());
        Local r9 = local(runs, "$z1", BooleanType.v());
        Local r10 = local(runs, "$z2", BooleanType.v());
        Local r11 = local(runs, "$i4", IntType.v());
        body(runs, J.newIdentityStmt(r0, J.newThisRef(self)),
                J.newIdentityStmt(r1, J.newParameterRef(confType, 0)),
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
                J.newAssignStmt(name, J.newVirtualInvokeExpr(r1,
                        get.makeRef(), StringConstant.v("k.name"))),
                J.newAssignStmt(r6, J.newVirtualInvokeExpr(r1,
                        getInt.makeRef(), name, IntConstant.v(0))),
                J.newAssignStmt(r7, J.newVirtualInvokeExpr(r1,
                        getInt.makeRef(), StringConstant.v("k.only"),
                        IntConstant.v(7))),
                J.newAssignStmt(r8, J.newVirtualInvokeExpr(r1,
                        getLong.makeRef(), StringConstant.v("k.only"),
                        LongConstant.v(3L))),
                J.newAssignStmt(r9, J.newStaticInvokeExpr(isA.makeRef(), r1)),
                J.newAssignStmt(r10, J.newStaticInvokeExpr(isB.makeRef(), r1)),
                J.newAssignStmt(r11, J.newStaticInvokeExpr(limitOf.makeRef(),
                        r1)),
                J.newReturnVoidStmt());
        String runSig = runs.getSignature();
        String sub = "<org.apache.hadoop.hdfs.HdfsConfiguration: int "
                + "getInt(java.lang.String,int)>";
        Object[][] calls = {{3, wrapper, "$z0"}, {4, getInt, "$i0"},
            {5, sub, "$i1"}, {7, getInt, "$i2"}, {8, getInt, "$i3"},
            {9, getLong, "$l0"}, {10, isA, "$z1"}, {11, isB, "$z2"},
            {12, limitOf, "$i4"}};
        for (Object[] call : calls) {
            String callee = call[1] instanceof SootMethod
                    ? ((SootMethod) call[1]).getSignature() : (String) call[1];
            edges.add(edge("call_return", callee + ".return",
                    runSig + "::" + call[2], runSig, (Integer) call[0],
                    callee));
        }
        edges.add(edge("call_return", getInt.getSignature() + ".return",
                limitOf.getSignature() + "::$i0", limitOf.getSignature(), 1,
                getInt.getSignature()));
        edges.add(edge("call_return", getBoolean.getSignature() + ".return",
                initSig + "::$z0", initSig, 3, getBoolean.getSignature()));
    }

    /** {@code static boolean <name>(Configuration c)}: {@code
     *  "<literal>".equals(c.get("<key>"))}. */
    private static SootMethod view(SootClass owner, String name, String key,
                                   String literal, RefType confType,
                                   RefType text, SootMethod get,
                                   SootMethod equals) {
        SootMethod view = method(owner, name,
                Collections.<Type>singletonList(confType), BooleanType.v(),
                Modifier.STATIC);
        Local c = local(view, "r0", confType);
        Local value = local(view, "$r1", text);
        Local answer = local(view, "$z0", BooleanType.v());
        Local constant = local(view, "$r2", text);
        body(view, J.newIdentityStmt(c, J.newParameterRef(confType, 0)),
                J.newAssignStmt(value, J.newVirtualInvokeExpr(c,
                        get.makeRef(), StringConstant.v(key))),
                J.newAssignStmt(constant, StringConstant.v(literal)),
                J.newAssignStmt(answer, J.newVirtualInvokeExpr(constant,
                        equals.makeRef(), value)),
                J.newReturnStmt(answer));
        return view;
    }

    /** {@code void <name>()}: {@code if (this.<field> > bound) bump()}, its
     *  read and its guard in the slice. */
    private static void compare(SootClass owner, RefType self, String name,
                                SootField read, int bound, SootMethod bump,
                                List<Map<String, Object>> edges) {
        SootMethod check = method(owner, name,
                Collections.<Type>emptyList(), VoidType.v(), 0);
        Local c0 = local(check, "r0", self);
        Local c1 = local(check, "$i0", IntType.v());
        Unit done = J.newReturnVoidStmt();
        body(check, J.newIdentityStmt(c0, J.newThisRef(self)),
                J.newAssignStmt(c1, J.newInstanceFieldRef(c0,
                        read.makeRef())),
                J.newIfStmt(J.newLeExpr(c1, IntConstant.v(bound)), done),
                J.newInvokeStmt(J.newVirtualInvokeExpr(c0, bump.makeRef())),
                done);
        String signature = check.getSignature();
        String local = signature + "::$i0";
        edges.add(edge("field_read", field("int " + read.getName()), local,
                signature, 1, null));
        edges.add(edge("guard_dependency", local, signature + "#u2",
                signature, 2, null));
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
