package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.G;
import soot.Scene;
import soot.SootMethod;

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
     * a view of it -- a fluent call, a java.util iterator --, an argument a
     * library check returns ({@code Objects.requireNonNull}) or a helper's
     * body does ({@code same}), never another argument (solr-adhoc-10 SG1:
     * {@code toStringHelper(this).add(..,
     * autoDeleteAgeMath)} made the next {@code add} a mutation of the String
     * field); and no call on an immutable JDK value mutates it.  {@code
     * touch()} chains a helper over {@code name}, removes through {@code
     * items}' iterator, and replaces in {@code name}.  And a constructor's
     * store into the object it builds is no store a guard of the call into
     * it decides when only one arm builds one (solr-bugs-reindex-cleanup
     * SG1: {@code wrapWatcher}'s {@code instanceof} before {@code new
     * ProcessWatchWithExecutor}), but one is when both arms do, choosing
     * the arguments it stores; its store into another object's field is
     * decided by every such guard: {@code make} builds a {@code Box} under
     * {@code gate}, {@code pick} one on each arm of it, whose constructor
     * stores its own {@code v} and its owner's {@code w}.
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
                {"the constructor's store of its owner's field: the guards of"
                        + " the calls into it", names(MAKE + "#u3",
                        PICK + "#u3"), storeGuards.get(other)},
                {"its store of its own field: only the guard both of whose"
                        + " arms build one, choosing the arguments it stores",
                        names(PICK + "#u3"),
                        storeGuards.get(own + " ownObject")},
                {"the helper's add is no mutation of name", names(),
                        mutations(program, TOUCH, 4)},
                {"the iterator's remove mutates items",
                        names(field(STORE, "java.util.List items")),
                        mutations(program, TOUCH, 7)},
                {"a String's replace mutates nothing", names(),
                        mutations(program, TOUCH, 9)},
                {"a remove through requireNonNull's result mutates items",
                        names(field(STORE, "java.util.List items")),
                        mutations(program, THROUGH, 5)},
                {"and through a helper's that returns its argument",
                        names(field(STORE, "java.util.List items")),
                        mutations(program, THROUGH, 10)}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** A field reference on the method's own receiver ({@code := @this}'s
     *  local), read or written, and none on another object or a static. */
    @Test
    public void aFieldReferenceOnTheMethodsOwnReceiver() {
        Object[][] rows = {
                {"$r2 = r0.<a.W: a.Watcher watcher>", true},
                {"r0.<a.Box: int v> = i0", true},
                {"$r1 = $r0.<a.S: java.lang.String name>", false},
                {"r1.<a.S: int w> = i0", false},
                {"$r0 = <a.S: a.S inst>", false}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1],
                    SeedBackwardStaticAnalyzer.onReceiver("r0",
                            (String) row[0]));
        }
    }

    private static final String STORE = "a.S";
    private static final String MAKE = "<a.S: void make(a.S,int)>";
    private static final String PICK = "<a.S: void pick(a.S,int)>";
    private static final String TOUCH = "<a.S: void touch()>";
    private static final String THROUGH = "<a.S: void through()>";
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
     * = b}; {@code pick(t, k)} is {@code if (gate != 0) keep(new Box(t, 1));
     * else keep(new Box(t, 2));}; {@code through()} is {@code
     * ((List) Objects.requireNonNull(items)).iterator().remove(); ((List)
     * same(items)).iterator().remove();}, {@code same(o)} returning {@code
     * o}.
     */
    private static CausynthTargetContext storeScene() {
        String helper = "<a.Helper: a.Helper add(java.lang.String,"
                + "java.lang.Object)>";
        String iterator = "<java.util.List: java.util.Iterator iterator()>";
        String remove = "<java.util.Iterator: void remove()>";
        String box = "<a.Box: void <init>(a.S,int)>";
        String keep = "<a.S: void keep(a.Box)>";
        JimpleScene.load(JimpleScene.OBJECT, JimpleScene.FAILURE,
                "public final class java.lang.String extends"
                        + " java.lang.Object { public int length() { }"
                        + " public java.lang.String replace(java.lang.String,"
                        + " java.lang.String) { } }",
                "public abstract interface java.util.Iterator {"
                        + " public abstract void remove(); }",
                "public abstract interface java.util.List {"
                        + " public abstract int size();"
                        + " public abstract java.util.Iterator iterator(); }",
                "application public class a.Helper extends java.lang.Object {"
                        + " public a.Helper add(java.lang.String,"
                        + " java.lang.Object) { a.Helper r0;"
                        + " r0 := @this: a.Helper; return r0; }"
                        + " public static a.Helper of(java.lang.Object) {"
                        + " a.Helper $r0; java.lang.Object r1;"
                        + " r1 := @parameter0: java.lang.Object;"
                        + " $r0 = new a.Helper; return $r0; } }",
                "application public class a.S extends java.lang.Object {"
                        + " public java.lang.String name;"
                        + " public java.util.List items;"
                        + " public static a.S inst; public int w;"
                        + " public static int gate; public static a.Box box;"
                        + " public static void keep(a.Box) { a.Box r0;"
                        + " r0 := @parameter0: a.Box; <a.S: a.Box box> = r0;"
                        + " return; }"
                        + " public static void make(a.S, int) { a.S r0;"
                        + " int i1, $i0; a.Box $r1; r0 := @parameter0: a.S;"
                        + " i1 := @parameter1: int; $i0 = <a.S: int gate>;"
                        + " if $i0 == 0 goto label1; $r1 = new a.Box;"
                        + " specialinvoke $r1." + box + "(r0, i1);"
                        + " staticinvoke " + keep + "($r1); label1: return; }"
                        + " public static void pick(a.S, int) { a.S r0;"
                        + " int i1, $i0; a.Box $r1, $r2;"
                        + " r0 := @parameter0: a.S; i1 := @parameter1: int;"
                        + " $i0 = <a.S: int gate>; if $i0 == 0 goto label1;"
                        + " $r1 = new a.Box; specialinvoke $r1." + box
                        + "(r0, 1); staticinvoke " + keep + "($r1);"
                        + " goto label2; label1: $r2 = new a.Box;"
                        + " specialinvoke $r2." + box + "(r0, 2);"
                        + " staticinvoke " + keep + "($r2); label2: return; }"
                        + " public void touch() { a.S r0;"
                        + " java.lang.String $r1; a.Helper $r2, $r3;"
                        + " java.util.List $r4; java.util.Iterator $r5;"
                        + " java.lang.String $r6, $r7; r0 := @this: a.S;"
                        + " $r1 = r0.<a.S: java.lang.String name>;"
                        + " $r2 = staticinvoke <a.Helper: a.Helper of("
                        + "java.lang.Object)>(r0); $r3 = virtualinvoke $r2."
                        + helper + "(\"n\", $r1); virtualinvoke $r3." + helper
                        + "(\"m\", $r1); $r4 = r0.<a.S: java.util.List items>;"
                        + " $r5 = interfaceinvoke $r4." + iterator + "();"
                        + " interfaceinvoke $r5." + remove + "();"
                        + " $r6 = r0.<a.S: java.lang.String name>;"
                        + " $r7 = virtualinvoke $r6.<java.lang.String:"
                        + " java.lang.String replace(java.lang.String,"
                        + "java.lang.String)>(\"a\", \"b\"); return; }"
                        + " public static java.lang.Object same("
                        + "java.lang.Object) { java.lang.Object r0, $r1;"
                        + " r0 := @parameter0: java.lang.Object; $r1 = r0;"
                        + " return $r1; }"
                        + " public void through() { a.S r0; java.util.List $r1;"
                        + " java.lang.Object $r2; java.util.List $r3;"
                        + " java.util.Iterator $r4; java.util.List $r5;"
                        + " java.lang.Object $r6; java.util.List $r7;"
                        + " java.util.Iterator $r8; r0 := @this: a.S;"
                        + " $r1 = r0.<a.S: java.util.List items>;"
                        + " $r2 = staticinvoke <java.util.Objects:"
                        + " java.lang.Object requireNonNull(java.lang.Object)>"
                        + "($r1); $r3 = (java.util.List) $r2;"
                        + " $r4 = interfaceinvoke $r3." + iterator + "();"
                        + " interfaceinvoke $r4." + remove + "();"
                        + " $r5 = r0.<a.S: java.util.List items>;"
                        + " $r6 = staticinvoke <a.S: java.lang.Object same("
                        + "java.lang.Object)>($r5); $r7 = (java.util.List) $r6;"
                        + " $r8 = interfaceinvoke $r7." + iterator + "();"
                        + " interfaceinvoke $r8." + remove + "(); return; }"
                        + " public static void check() { a.S $r0;"
                        + " java.lang.String $r1; java.util.List $r2;"
                        + " int $i0, $i1, $i2; a.Box $r4; int $i3, $i4;"
                        + " java.lang.IllegalStateException $r3;"
                        + " $r0 = <a.S: a.S inst>;"
                        + " $r1 = $r0.<a.S: java.lang.String name>;"
                        + " $i0 = virtualinvoke $r1.<java.lang.String: int"
                        + " length()>(); $r2 = $r0.<a.S: java.util.List items>;"
                        + " $i1 = interfaceinvoke $r2.<java.util.List: int"
                        + " size()>(); $i2 = $i0 + $i1;"
                        + " $r4 = <a.S: a.Box box>; $i3 = $r4.<a.Box: int v>;"
                        + " $i4 = $r0.<a.S: int w>; $i2 = $i2 + $i3;"
                        + " $i2 = $i2 + $i4; if $i2 == 0 goto label1;"
                        + " $r3 = new java.lang.IllegalStateException;"
                        + " throw $r3; label1: return; } }",
                "application public class a.Box extends java.lang.Object {"
                        + " public int v; public void <init>(a.S, int) {"
                        + " a.Box r0; a.S r1; int i0; r0 := @this: a.Box;"
                        + " r1 := @parameter0: a.S; i0 := @parameter1: int;"
                        + " r0.<a.Box: int v> = i0; r1.<a.S: int w> = i0;"
                        + " return; } }",
                "public class java.util.Objects extends java.lang.Object {"
                        + " public static java.lang.Object requireNonNull("
                        + "java.lang.Object) { } }");
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
        String params = "a.Base, a.Mode, a.Mode, int";
        String identities = " r0 := @parameter0: a.Base;"
                + " r1 := @parameter1: a.Mode; r2 := @parameter2: a.Mode;"
                + " i0 := @parameter3: int;";
        JimpleScene.load(JimpleScene.OBJECT, JimpleScene.FAILURE,
                "public abstract class java.lang.Enum extends java.lang.Object"
                        + " { public final boolean equals(java.lang.Object)"
                        + " { } }",
                "application public final class a.Mode extends java.lang.Enum"
                        + " { }",
                "application public class a.T extends java.lang.Object {"
                        + " public static int saved; public static int gate;"
                        + " public static int enabled; public static int on;"
                        // save(v): saved = v; caller(v): if (enabled != 0)
                        // save(v).
                        + " public static void save(int) { int i0;"
                        + " i0 := @parameter0: int; <a.T: int saved> = i0;"
                        + " return; }"
                        + " public static void caller(int) { int i0, i1;"
                        + " i0 := @parameter0: int; i1 = <a.T: int enabled>;"
                        + " if i1 == 0 goto label1; staticinvoke <a.T: void"
                        + " save(int)>(i0); label1: return; }"
                        // fill(k): int[] a = new int[1]; if (on != 0) a[0] =
                        // k; return a[0].
                        + " public static int fill(int) { int i0, i1;"
                        + " int[] r0; int i2; i0 := @parameter0: int;"
                        + " r0 = newarray (int)[1]; i1 = <a.T: int on>;"
                        + " if i1 == 0 goto label1; r0[0] = i0;"
                        + " label1: i2 = r0[0]; return i2; }"
                        + " public static void check(" + params + ") {"
                        + " a.Base r0; a.Mode r1, r2; int i0, i1; boolean z0;"
                        + " int i2, i3, i4; java.lang.IllegalStateException r3;"
                        + identities
                        + " i1 = virtualinvoke r0.<a.Base: int state()>();"
                        + " z0 = virtualinvoke r1.<a.Mode: boolean equals("
                        + "java.lang.Object)>(r2); i2 = <a.T: int saved>;"
                        + " i3 = staticinvoke <a.T: int fill(int)>(i0);"
                        + " i4 = i1 + z0; i4 = i4 + i2; i4 = i4 + i3;"
                        + " if i4 != 0 goto label1;"
                        + " r3 = new java.lang.IllegalStateException;"
                        + " throw r3; label1: return; }"
                        // run(b, m, n, k): if (gate != 0) check(b, m, n, k).
                        + " public static void run(" + params + ") {"
                        + " a.Base r0; a.Mode r1, r2; int i0, i1;" + identities
                        + " i1 = <a.T: int gate>; if i1 == 0 goto label1;"
                        + " staticinvoke " + CHECK
                        + "(r0, r1, r2, i0); label1: return; } }",
                // Base: abstract, its state() concrete; Leaf inherits it.
                "application public abstract class a.Base extends"
                        + " java.lang.Object { public int mark;"
                        + " public int state() { a.Base r0; int i0;"
                        + " r0 := @this: a.Base; i0 = r0.<a.Base: int mark>;"
                        + " i0 = i0 + 1; return i0; } }",
                "application public class a.Leaf extends a.Base { }");
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", T, "check",
                        "(La/Base;La/Mode;La/Mode;I)V", CHECK,
                        "java.lang.IllegalStateException", 0));
    }
}
