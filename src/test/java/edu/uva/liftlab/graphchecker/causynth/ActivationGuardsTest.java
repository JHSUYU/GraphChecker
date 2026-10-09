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
     * What a call's result is: its receiver when the call may return it or
     * a view of it -- a fluent call, a java.util iterator -- never another
     * argument (solr-adhoc-10 SG1: {@code toStringHelper(this).add(..,
     * autoDeleteAgeMath)} made the next {@code add} a mutation of the String
     * field); and no call on an immutable JDK value mutates it.  {@code
     * touch()} chains a helper over {@code name}, removes through {@code
     * items}' iterator, and replaces in {@code name}.  And a constructor's
     * store into the object it builds is no store the guard of the call
     * into it decides (solr-bugs-reindex-cleanup SG1: {@code wrapWatcher}'s
     * {@code instanceof} before {@code new ProcessWatchWithExecutor}), where
     * its store into another object's field is: {@code make} builds a
     * {@code Box} under {@code gate}, whose constructor stores its own
     * {@code v} and its owner's {@code w}.
     */
    @Test
    public void aCallsResultIsItsReceiverOnlyAndAValueIsNeverMutated()
            throws Exception {
        System.setProperty(LibraryReceivers.ROOTS,
                tree.newFolder("roots").getPath());
        StaticProgram program = new SeedBackwardStaticAnalyzer(storeScene())
                .analyze();
        String own = field("a.Box", "int v");
        String other = field(STORE, "int w");
        Map<String, Object> region = new java.util.LinkedHashMap<>();
        region.put("regionId", "REGION.store");
        List<String> methods = new java.util.ArrayList<>();
        for (String type : Arrays.asList(STORE, "a.Box")) {
            for (SootMethod method
                    : Scene.v().getSootClass(type).getMethods()) {
                methods.add(method.getSignature());
            }
        }
        region.put("methods", methods);
        List<StaticScopeMap.Site> sites = StaticScopeMap.sites(program.edges,
                Collections.<Map<String, Object>>singletonList(region),
                Collections.<String,
                        edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(),
                (m, u, c) -> null, (site, cell) -> null,
                method -> !method.startsWith("<a."),
                CausynthStaticFacts::trackedKind,
                CausynthStaticFacts::staticField,
                CausynthStaticFacts::constructionOnly);
        Map<String, Set<String>> storeGuards = new java.util.TreeMap<>();
        for (com.google.gson.JsonObject row : StaticScopeMap.rows(sites,
                SiteControlDependence.over(StaticScopeMap.siteIds(sites)),
                method -> false)) {
            if (!StaticScopeMap.WRITE_SITE.equals(row.get("role")
                    .getAsString())) {
                continue;
            }
            Set<String> guarded = new TreeSet<>();
            for (com.google.gson.JsonElement guard
                    : row.getAsJsonArray("guards")) {
                guarded.add(guard.getAsString());
            }
            storeGuards.put(row.get("cell").getAsString()
                    + (row.has("ownObject") ? " ownObject" : ""), guarded);
        }
        Object[][] rows = {
                {"the constructor's store of its owner's field: the guard of"
                        + " the call into it", names(MAKE + "#u3"),
                        storeGuards.get(other)},
                {"its store of its own field: none", names(),
                        storeGuards.get(own + " ownObject")},
                {"the helper's add is no mutation of name", names(),
                        mutations(program, TOUCH, 4)},
                {"the iterator's remove mutates items",
                        names(field(STORE, "java.util.List items")),
                        mutations(program, TOUCH, 7)},
                {"a String's replace mutates nothing", names(),
                        mutations(program, TOUCH, 9)}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static final String STORE = "a.S";
    private static final String MAKE = "<a.S: void make(a.S,int)>";
    private static final String TOUCH = "<a.S: void touch()>";
    private static final String STORE_CHECK = "<a.S: void check()>";

    /** The fields the mutation rows of {@code method}'s unit write. */
    private static Set<String> mutations(StaticProgram program, String method,
                                         int unit) {
        Set<String> found = new TreeSet<>();
        for (Map<String, Object> edge : program.edges) {
            if ("field_mutation".equals(edge.get("kind"))
                    && method.equals(edge.get("method"))
                    && Integer.valueOf(unit).equals(edge.get("unitIndex"))) {
                found.add((String) edge.get("toCell"));
            }
        }
        return found;
    }

    /**
     * {@code check()} throws unless {@code inst.name.length() +
     * inst.items.size() + box.v + inst.w} is zero; {@code touch()} is
     * {@code Helper.of(this).add("n", name).add("m", name);
     * items.iterator().remove(); name.replace("a", "b");}; {@code make(t,
     * k)} is {@code if (gate != 0) keep(new Box(t, k));}, {@code Box(owner,
     * p)} is {@code this.v = p; owner.w = p;}, {@code keep(b)} is {@code box
     * = b}.
     */
    private static CausynthTargetContext storeScene() {
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        IntType i = IntType.v();
        SootClass object = library("java.lang.Object", null, 0);
        library("java.lang.IllegalStateException", object, 0);
        SootClass string = library("java.lang.String", object,
                Modifier.FINAL);
        SootMethod length = method(string, "length",
                Collections.<Type>emptyList(), i, 0);
        SootMethod replace = method(string, "replace", Arrays.<Type>asList(
                string.getType(), string.getType()), string.getType(), 0);
        SootClass iterator = library("java.util.Iterator", null,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        SootMethod remove = declared(iterator, "remove",
                Collections.<Type>emptyList(), VoidType.v());
        SootClass list = library("java.util.List", null,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        SootMethod size = declared(list, "size",
                Collections.<Type>emptyList(), i);
        SootMethod iterate = declared(list, "iterator",
                Collections.<Type>emptyList(), iterator.getType());

        SootClass helper = application("a.Helper", object, 0);
        SootMethod add = method(helper, "add", Arrays.<Type>asList(
                string.getType(), object.getType()), helper.getType(), 0);
        Local self = local(add, "r0", helper.getType());
        body(add, J.newIdentityStmt(self, J.newThisRef(helper.getType())),
                J.newReturnStmt(self));
        SootMethod of = method(helper, "of", Collections.<Type>singletonList(
                object.getType()), helper.getType(), Modifier.STATIC);
        Local made = local(of, "$r0", helper.getType());
        Local given = local(of, "r1", object.getType());
        body(of, J.newIdentityStmt(given,
                        J.newParameterRef(object.getType(), 0)),
                J.newAssignStmt(made, J.newNewExpr(helper.getType())),
                J.newReturnStmt(made));

        SootClass type = application(STORE, object, 0);
        SootField name = new SootField("name", string.getType(),
                Modifier.PUBLIC);
        SootField items = new SootField("items", list.getType(),
                Modifier.PUBLIC);
        SootField inst = new SootField("inst", type.getType(),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField w = new SootField("w", i, Modifier.PUBLIC);
        type.addField(name);
        type.addField(items);
        type.addField(inst);
        type.addField(w);
        SootField gate = staticField(type, "gate");

        SootClass box = application("a.Box", object, 0);
        SootField v = new SootField("v", i, Modifier.PUBLIC);
        box.addField(v);
        SootField held = new SootField("box", box.getType(),
                Modifier.PUBLIC | Modifier.STATIC);
        type.addField(held);
        SootMethod build = method(box, "<init>", Arrays.<Type>asList(
                type.getType(), i), VoidType.v(), 0);
        Local b0 = local(build, "r0", box.getType());
        Local owner = local(build, "r1", type.getType());
        Local p = local(build, "i0", i);
        body(build, J.newIdentityStmt(b0, J.newThisRef(box.getType())),
                J.newIdentityStmt(owner, J.newParameterRef(type.getType(), 0)),
                J.newIdentityStmt(p, J.newParameterRef(i, 1)),
                J.newAssignStmt(J.newInstanceFieldRef(b0, v.makeRef()), p),
                J.newAssignStmt(J.newInstanceFieldRef(owner, w.makeRef()), p),
                J.newReturnVoidStmt());
        SootMethod keep = method(type, "keep", Collections.<Type>singletonList(
                box.getType()), VoidType.v(), Modifier.STATIC);
        Local kept = local(keep, "r0", box.getType());
        body(keep, J.newIdentityStmt(kept, J.newParameterRef(box.getType(), 0)),
                J.newAssignStmt(J.newStaticFieldRef(held.makeRef()), kept),
                J.newReturnVoidStmt());
        SootMethod make = method(type, "make", Arrays.<Type>asList(
                type.getType(), i), VoidType.v(), Modifier.STATIC);
        Local mt = local(make, "r0", type.getType());
        Local mk = local(make, "i1", i);
        Local open = local(make, "$i0", i);
        Local fresh = local(make, "$r1", box.getType());
        Unit leave = J.newReturnVoidStmt();
        body(make, J.newIdentityStmt(mt, J.newParameterRef(type.getType(), 0)),
                J.newIdentityStmt(mk, J.newParameterRef(i, 1)),
                J.newAssignStmt(open, J.newStaticFieldRef(gate.makeRef())),
                J.newIfStmt(J.newEqExpr(open, IntConstant.v(0)), leave),
                J.newAssignStmt(fresh, J.newNewExpr(box.getType())),
                J.newInvokeStmt(J.newSpecialInvokeExpr(fresh, build.makeRef(),
                        mt, mk)),
                J.newInvokeStmt(J.newStaticInvokeExpr(keep.makeRef(), fresh)),
                leave);

        SootMethod touch = method(type, "touch", Collections.<Type>emptyList(),
                VoidType.v(), 0);
        Local t0 = local(touch, "r0", type.getType());
        Local n = local(touch, "$r1", string.getType());
        Local h = local(touch, "$r2", helper.getType());
        Local h2 = local(touch, "$r3", helper.getType());
        Local l = local(touch, "$r4", list.getType());
        Local it = local(touch, "$r5", iterator.getType());
        Local s2 = local(touch, "$r6", string.getType());
        Local s3 = local(touch, "$r7", string.getType());
        body(touch, J.newIdentityStmt(t0, J.newThisRef(type.getType())),
                J.newAssignStmt(n, J.newInstanceFieldRef(t0, name.makeRef())),
                J.newAssignStmt(h, J.newStaticInvokeExpr(of.makeRef(), t0)),
                J.newAssignStmt(h2, J.newVirtualInvokeExpr(h, add.makeRef(),
                        soot.jimple.StringConstant.v("n"), n)),
                J.newInvokeStmt(J.newVirtualInvokeExpr(h2, add.makeRef(),
                        soot.jimple.StringConstant.v("m"), n)),
                J.newAssignStmt(l, J.newInstanceFieldRef(t0, items.makeRef())),
                J.newAssignStmt(it, J.newInterfaceInvokeExpr(l,
                        iterate.makeRef())),
                J.newInvokeStmt(J.newInterfaceInvokeExpr(it, remove.makeRef())),
                J.newAssignStmt(s2, J.newInstanceFieldRef(t0, name.makeRef())),
                J.newAssignStmt(s3, J.newVirtualInvokeExpr(s2,
                        replace.makeRef(), soot.jimple.StringConstant.v("a"),
                        soot.jimple.StringConstant.v("b"))),
                J.newReturnVoidStmt());

        SootMethod check = method(type, "check", Collections.<Type>emptyList(),
                VoidType.v(), Modifier.STATIC);
        Local c = local(check, "$r0", type.getType());
        Local cn = local(check, "$r1", string.getType());
        Local cl = local(check, "$r2", list.getType());
        Local len = local(check, "$i0", i);
        Local count = local(check, "$i1", i);
        Local sum = local(check, "$i2", i);
        Local cb = local(check, "$r4", box.getType());
        Local cv = local(check, "$i3", i);
        Local cw = local(check, "$i4", i);
        RefType failure = RefType.v("java.lang.IllegalStateException");
        Local thrown = local(check, "$r3", failure);
        Unit done = J.newReturnVoidStmt();
        body(check, J.newAssignStmt(c, J.newStaticFieldRef(inst.makeRef())),
                J.newAssignStmt(cn, J.newInstanceFieldRef(c, name.makeRef())),
                J.newAssignStmt(len, J.newVirtualInvokeExpr(cn,
                        length.makeRef())),
                J.newAssignStmt(cl, J.newInstanceFieldRef(c, items.makeRef())),
                J.newAssignStmt(count, J.newInterfaceInvokeExpr(cl,
                        size.makeRef())),
                J.newAssignStmt(sum, J.newAddExpr(len, count)),
                J.newAssignStmt(cb, J.newStaticFieldRef(held.makeRef())),
                J.newAssignStmt(cv, J.newInstanceFieldRef(cb, v.makeRef())),
                J.newAssignStmt(cw, J.newInstanceFieldRef(c, w.makeRef())),
                J.newAssignStmt(sum, J.newAddExpr(sum, cv)),
                J.newAssignStmt(sum, J.newAddExpr(sum, cw)),
                J.newIfStmt(J.newEqExpr(sum, IntConstant.v(0)), done),
                J.newAssignStmt(thrown, J.newNewExpr(failure)),
                J.newThrowStmt(thrown), done);
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", STORE, "check", "()V",
                        STORE_CHECK, "java.lang.IllegalStateException", 0));
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

    /** An abstract method: a library interface's, with no body. */
    private static SootMethod declared(SootClass owner, String name,
                                       List<Type> parameters, Type returned) {
        SootMethod method = new SootMethod(name, parameters, returned,
                Modifier.PUBLIC | Modifier.ABSTRACT);
        owner.addMethod(method);
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
