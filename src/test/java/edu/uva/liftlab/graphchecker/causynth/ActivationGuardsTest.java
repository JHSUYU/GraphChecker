package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.ArrayType;
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
import soot.options.Options;

import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §2.2: a branch that decides whether code carrying the slice's
 * data runs is demanded like data -- at a mutation of a demanded container,
 * at the calls into the declared target's method from its region's entry,
 * and at the calls into a method holding a demanded store, constant or not;
 * and a concrete method an abstract class declares is a body the slice
 * follows, an enum's inherited identity a value.  The target's chain in
 * the scope map takes the calls into its method, up to its execution
 * context's entry.
 */
public class ActivationGuardsTest {
    private static final String T = "a.T";
    private static final String CHECK = "<a.T: void check(a.Base,a.Mode,"
            + "a.Mode,int)>";
    private static final String RUN = "<a.T: void run(a.Base,a.Mode,"
            + "a.Mode,int)>";
    private static final Jimple J = Jimple.v();

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
        System.clearProperty(LibraryReceivers.ROOTS);
    }

    @Test
    public void aBranchDecidingWhetherSliceCodeRunsIsDemanded()
            throws Exception {
        System.setProperty(LibraryReceivers.ROOTS,
                tree.newFolder("roots").getPath());
        StaticProgram program = new SeedBackwardStaticAnalyzer(target())
                .analyze();
        String thrown = CHECK + "#u13";
        StaticScopeMap.Guards guards = SiteControlDependence.over(
                Collections.singleton(thrown));
        Object[][] rows = {
                {"an abstract class's concrete method, called through it, is"
                        + " the plain call: its return and its body",
                        names("call_return"), kinds(program,
                        "<a.Base: int state()>.return", CHECK + "::i1")},
                {"so the field its body returns is read", names("field_read"),
                        kinds(program, field("a.Base", "int mark"),
                                "<a.Base: int state()>::i0")},
                {"an enum's inherited equals is its receiver's and its"
                        + " argument's value", names(local("r1"), local("r2")),
                        sources(program, "local_def_use", local("z0"))},
                {"the call into the target's method demands its caller's"
                        + " guard", names(RUN + "::i1"), sources(program,
                        "guard_dependency", CHECK + ".activation")},
                {"a data store's method: the guard of the call into it",
                        names("<a.T: void caller(int)>::i1"),
                        sources(program, "guard_dependency",
                                field(T, "int saved"))},
                {"a store into a demanded array: its own guard",
                        names("<a.T: int fill(int)>::i1"), sources(program,
                        "guard_dependency",
                        "<a.T: int fill(int)>::r0#array-element")},
                {"the target's chain: the guard of the call into its method",
                        names(RUN + "#u5"), sites(StaticScopeMap.targetChain(
                        guards, thrown, method -> false))},
                {"none where its method is an execution context's entry,"
                        + " which its starter runs", names(),
                        sites(StaticScopeMap.targetChain(guards, thrown,
                                CHECK::equals))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * A switch guard of the throw is forced to the one case the throw is
     * reachable from ({@code plan.ForcingTable}): {@code pick(k)} throws on
     * {@code case 2} and returns on the others; {@code fallback(k)} throws on
     * its default.  A switch whose every arm reaches the throw names none.
     */
    @Test
    public void aSwitchGuardNamesTheOneCaseTheThrowIsReachableFrom() {
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        library("java.lang.IllegalStateException", object, 0);
        SootClass type = application(T, object, 0);
        Object[][] rows = {
                {"case 2 throws", switching(type, "pick", false), "2"},
                {"the default throws", switching(type, "fallback", true),
                        StaticScopeMap.Guards.DEFAULT_CASE}};
        for (Object[] row : rows) {
            String method = (String) row[1];
            StaticScopeMap.Guards guards = SiteControlDependence.over(
                    Collections.singleton(method + "#u4"));
            assertEquals((String) row[0], row[2],
                    guards.switchCase(method + "#u1", method + "#u4"));
            assertEquals("no switch at a plain unit", null,
                    guards.switchCase(method + "#u0", method + "#u4"));
        }
    }

    /** {@code name(int k)}: {@code switch (k) {case 1: case 2:} ...}, the
     *  throw at unit 4 reached from case 2, or from the default. */
    private static String switching(SootClass type, String name,
                                    boolean throwsOnDefault) {
        IntType i = IntType.v();
        SootMethod method = method(type, name,
                Collections.<Type>singletonList(i), VoidType.v(),
                Modifier.STATIC);
        Local k = local(method, "i0", i);
        RefType failure = RefType.v("java.lang.IllegalStateException");
        Local thrown = local(method, "r0", failure);
        Unit leave = J.newReturnVoidStmt();
        Unit raise = J.newAssignStmt(thrown, J.newNewExpr(failure));
        Unit doThrow = J.newThrowStmt(thrown);
        Unit dispatch = J.newTableSwitchStmt(k, 1, 2,
                throwsOnDefault ? Arrays.asList(leave, leave)
                        : Arrays.asList(leave, raise),
                throwsOnDefault ? raise : leave);
        body(method, J.newIdentityStmt(k, J.newParameterRef(i, 0)),
                dispatch, leave, raise, doThrow);
        return method.getSignature();
    }

    private static Set<String> sites(List<StaticScopeMap.Guard> chain) {
        Set<String> found = new TreeSet<>();
        for (StaticScopeMap.Guard guard : chain) found.add(guard.siteId());
        return found;
    }

    private static String field(String owner, String declared) {
        return "<" + owner + ": " + declared + ">";
    }

    private static String local(String name) {
        return CHECK + "::" + name;
    }

    /** The kinds of the rows from {@code from} into {@code to}. */
    private static Set<String> kinds(StaticProgram program, String from,
                                     String to) {
        Set<String> found = new TreeSet<>();
        for (Map<String, Object> edge : program.edges) {
            if (from.equals(edge.get("fromCell"))
                    && to.equals(edge.get("toCell"))) {
                found.add((String) edge.get("kind"));
            }
        }
        return found;
    }

    /** The sources of the rows of {@code kind} into {@code to}. */
    private static Set<String> sources(StaticProgram program, String kind,
                                       String to) {
        Set<String> found = new TreeSet<>();
        for (Map<String, Object> edge : program.edges) {
            if (kind.equals(edge.get("kind")) && to.equals(edge.get("toCell"))) {
                found.add((String) edge.get("fromCell"));
            }
        }
        return found;
    }

    private static Set<String> names(String... names) {
        return new TreeSet<>(Arrays.asList(names));
    }

    /**
     * {@code check(Base b, Mode m, Mode n, int k)} throws unless {@code
     * b.state() + m.equals(n) + saved + fill(k)} is non-zero; {@code run}
     * calls it only when {@code gate} is set; {@code caller} calls {@code
     * save}, which stores {@code saved}, only when {@code enabled} is.
     */
    private static CausynthTargetContext target() {
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        library("java.lang.IllegalStateException", object, 0);
        IntType i = IntType.v();
        SootClass enumType = library("java.lang.Enum", object,
                Modifier.ABSTRACT);
        method(enumType, "equals", Collections.<Type>singletonList(
                object.getType()), BooleanType.v(), Modifier.FINAL);
        SootClass mode = application("a.Mode", enumType, Modifier.FINAL);
        SootClass type = application(T, object, 0);
        SootField saved = staticField(type, "saved");
        SootField gate = staticField(type, "gate");
        SootField enabled = staticField(type, "enabled");
        SootField on = staticField(type, "on");

        // Base: abstract, its state() concrete; Leaf inherits it.
        SootClass base = application("a.Base", object, Modifier.ABSTRACT);
        SootField mark = new SootField("mark", i, Modifier.PUBLIC);
        base.addField(mark);
        SootMethod state = method(base, "state",
                Collections.<Type>emptyList(), i, 0);
        Local self = local(state, "r0", base.getType());
        Local value = local(state, "i0", i);
        body(state, J.newIdentityStmt(self, J.newThisRef(base.getType())),
                J.newAssignStmt(value, J.newInstanceFieldRef(self,
                        mark.makeRef())),
                J.newAssignStmt(value, J.newAddExpr(value, IntConstant.v(1))),
                J.newReturnStmt(value));
        application("a.Leaf", base, 0);

        // save(v): saved = v; caller(v): if (enabled != 0) save(v).
        SootMethod save = method(type, "save",
                Collections.<Type>singletonList(i), VoidType.v(),
                Modifier.STATIC);
        Local v = local(save, "i0", i);
        body(save, J.newIdentityStmt(v, J.newParameterRef(i, 0)),
                J.newAssignStmt(J.newStaticFieldRef(saved.makeRef()), v),
                J.newReturnVoidStmt());
        SootMethod caller = method(type, "caller",
                Collections.<Type>singletonList(i), VoidType.v(),
                Modifier.STATIC);
        Local cv = local(caller, "i0", i);
        Local flag = local(caller, "i1", i);
        Unit skip = J.newReturnVoidStmt();
        body(caller, J.newIdentityStmt(cv, J.newParameterRef(i, 0)),
                J.newAssignStmt(flag, J.newStaticFieldRef(enabled.makeRef())),
                J.newIfStmt(J.newEqExpr(flag, IntConstant.v(0)), skip),
                J.newInvokeStmt(J.newStaticInvokeExpr(save.makeRef(), cv)),
                skip);

        // fill(k): int[] a = new int[1]; if (on != 0) a[0] = k; return a[0].
        ArrayType ints = ArrayType.v(i, 1);
        SootMethod fill = method(type, "fill",
                Collections.<Type>singletonList(i), i, Modifier.STATIC);
        Local k = local(fill, "i0", i);
        Local set = local(fill, "i1", i);
        Local array = local(fill, "r0", ints);
        Local read = local(fill, "i2", i);
        Unit load = J.newAssignStmt(read, J.newArrayRef(array,
                IntConstant.v(0)));
        body(fill, J.newIdentityStmt(k, J.newParameterRef(i, 0)),
                J.newAssignStmt(array, J.newNewArrayExpr(i, IntConstant.v(1))),
                J.newAssignStmt(set, J.newStaticFieldRef(on.makeRef())),
                J.newIfStmt(J.newEqExpr(set, IntConstant.v(0)), load),
                J.newAssignStmt(J.newArrayRef(array, IntConstant.v(0)), k),
                load, J.newReturnStmt(read));

        List<Type> parameters = Arrays.<Type>asList(base.getType(),
                mode.getType(), mode.getType(), i);
        SootMethod check = method(type, "check", parameters, VoidType.v(),
                Modifier.STATIC);
        Local b = local(check, "r0", base.getType());
        Local m = local(check, "r1", mode.getType());
        Local n = local(check, "r2", mode.getType());
        Local key = local(check, "i0", i);
        Local got = local(check, "i1", i);
        Local same = local(check, "z0", BooleanType.v());
        Local stored = local(check, "i2", i);
        Local filled = local(check, "i3", i);
        Local sum = local(check, "i4", i);
        RefType failure = RefType.v("java.lang.IllegalStateException");
        Local thrown = local(check, "r3", failure);
        Unit done = J.newReturnVoidStmt();
        body(check, J.newIdentityStmt(b, J.newParameterRef(base.getType(), 0)),
                J.newIdentityStmt(m, J.newParameterRef(mode.getType(), 1)),
                J.newIdentityStmt(n, J.newParameterRef(mode.getType(), 2)),
                J.newIdentityStmt(key, J.newParameterRef(i, 3)),
                J.newAssignStmt(got, J.newVirtualInvokeExpr(b,
                        state.makeRef())),
                J.newAssignStmt(same, J.newVirtualInvokeExpr(m,
                        Scene.v().makeMethodRef(mode, "equals",
                                Collections.<Type>singletonList(
                                        object.getType()), BooleanType.v(),
                                false), n)),
                J.newAssignStmt(stored, J.newStaticFieldRef(saved.makeRef())),
                J.newAssignStmt(filled, J.newStaticInvokeExpr(fill.makeRef(),
                        key)),
                J.newAssignStmt(sum, J.newAddExpr(got, same)),
                J.newAssignStmt(sum, J.newAddExpr(sum, stored)),
                J.newAssignStmt(sum, J.newAddExpr(sum, filled)),
                J.newIfStmt(J.newNeExpr(sum, IntConstant.v(0)), done),
                J.newAssignStmt(thrown, J.newNewExpr(failure)),
                J.newThrowStmt(thrown), done);

        // run(b, m, n, k): if (gate != 0) check(b, m, n, k).
        SootMethod run = method(type, "run", parameters, VoidType.v(),
                Modifier.STATIC);
        Local[] actuals = {local(run, "r0", base.getType()),
                local(run, "r1", mode.getType()),
                local(run, "r2", mode.getType()), local(run, "i0", i)};
        Local open = local(run, "i1", i);
        Unit leave = J.newReturnVoidStmt();
        body(run, J.newIdentityStmt(actuals[0],
                        J.newParameterRef(base.getType(), 0)),
                J.newIdentityStmt(actuals[1],
                        J.newParameterRef(mode.getType(), 1)),
                J.newIdentityStmt(actuals[2],
                        J.newParameterRef(mode.getType(), 2)),
                J.newIdentityStmt(actuals[3], J.newParameterRef(i, 3)),
                J.newAssignStmt(open, J.newStaticFieldRef(gate.makeRef())),
                J.newIfStmt(J.newEqExpr(open, IntConstant.v(0)), leave),
                J.newInvokeStmt(J.newStaticInvokeExpr(check.makeRef(),
                        Arrays.asList(actuals))), leave);
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", T, "check",
                        "(La/Base;La/Mode;La/Mode;I)V", CHECK,
                        "java.lang.IllegalStateException", 0));
    }

    private static SootField staticField(SootClass owner, String name) {
        SootField field = new SootField(name, IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(field);
        return field;
    }

    private static SootClass application(String name, SootClass parent,
                                         int modifiers) {
        SootClass type = library(name, parent, modifiers);
        type.setApplicationClass();
        return type;
    }

    private static SootClass library(String name, SootClass parent,
                                     int modifiers) {
        SootClass type = new SootClass(name, Modifier.PUBLIC | modifiers);
        if (parent != null) type.setSuperclass(parent);
        Scene.v().addClass(type);
        return type;
    }

    private static SootMethod method(SootClass owner, String name,
                                     List<Type> parameters, Type returned,
                                     int modifiers) {
        SootMethod method = new SootMethod(name, parameters, returned,
                Modifier.PUBLIC | modifiers);
        owner.addMethod(method);
        method.setActiveBody(J.newBody(method));
        return method;
    }

    private static Local local(SootMethod method, String name, Type type) {
        Local local = J.newLocal(name, type);
        method.getActiveBody().getLocals().add(local);
        return local;
    }

    private static void body(SootMethod method, Unit... units) {
        for (Unit unit : units) {
            method.getActiveBody().getUnits().add(unit);
        }
    }
}
