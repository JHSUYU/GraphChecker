package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import soot.G;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;

/**
 * Matched calls ({@link ReturnOnlyFormals}): a formal only its method's
 * return needs is demanded only at the calls whose result is.  The scene's
 * declared throw in {@code check} decides on the results of its keyed
 * callers and on three fields; beside each keyed caller an idle one makes
 * the same call and drops or stores the result where nothing reads it.
 */
public class MatchedCallTest {
    private static final String PB = "m.Pb";
    private static final String CHECK = "<m.Pb: void check(int,m.Codec,"
            + "m.Scale,m.Bag,java.lang.Object,m.Spi)>";
    private static final Set<String> ARGUMENTS = names("call_argument",
            "caller_argument", "dispatch_argument",
            "dispatch_caller_argument");

    @Rule
    public TemporaryFolder tree = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
        System.clearProperty(LibraryReceivers.ROOTS);
    }

    @Test
    public void aFormalOnlyTheReturnNeedsReachesOnlyTheDemandedCalls()
            throws Exception {
        // The system's own roots hold none of the scene's library classes.
        System.setProperty(LibraryReceivers.ROOTS,
                tree.newFolder("roots").getPath());
        StaticProgram program = new SeedBackwardStaticAnalyzer(target())
                .analyze();
        Object[][] rows = {
                {"a helper only its return needs (PBHelperClient"
                        + ".getByteString's shape) reaches the caller whose"
                        + " result is demanded, not the one that stores it"
                        + " where nothing reads it",
                        names("encodeKey"), callers(program, "int wrap(int)")},
                {"so that caller is no slice method", false,
                        program.traceMethods.contains(
                                "<m.Pb: void encodeCipher(int)>")},
                {"a formal flowing into the return and a store reaches"
                        + " every caller", names("recordIdle", "recordKey"),
                        callers(program, "int record(int)")},
                {"a virtual call: the implementation that stores its"
                        + " formal is demanded at every site",
                        names("codeIdle", "codeKey"), callers(program,
                        "<m.LoggingCodec: int code(int)>")},
                {"the one only its return needs where the result is",
                        names("codeKey"), callers(program,
                        "<m.PureCodec: int code(int)>")},
                {"a call of the method itself is a flow inside it",
                        names("down", "downKey"),
                        callers(program, "int down(int)")},
                {"a cycle through another method is conservative",
                        names("odd", "parityIdle", "parityKey"),
                        callers(program, "int even(int)")},
                {"a literal actual is a row only where the result is"
                        + " demanded", names("lit"), into(program,
                        "<m.Pb: int wrap(int)>.param0:int",
                        "method_caller_literal_argument")},
                {"a this only the return needs: only the receiver whose"
                        + " call's result is demanded", names("applyKey"),
                        into(program, "<m.Scale: int apply(int)>::r0",
                        "method_receiver")},
                {"a store into an array a formal holds is an effect:"
                        + " every caller", names("putIdle", "putKey"),
                        into(program, "<m.Pb: int put(int[],int)>"
                                + ".param1:int", ARGUMENTS)},
                {"a callee mutating its own container mutates its"
                        + " receiver", names("hold"), into(program,
                        "<m.Pb: int hold(m.Bag,java.lang.Object)>::r0",
                        "container_call_mutation_effect")},
                {"a call through a sub-interface that inherits the method"
                        + " is the implementation's call: the formal that"
                        + " turned into an effect reaches the caller that"
                        + " met it while return-only", names("spiIdle",
                        "spiKey"), callers(program,
                        "<m.Late: int tick(int)>")},
                {"and through one inheriting a library's declaration",
                        names("spi2Idle"), callers(program,
                        "<m.Late2: int probe(int)>")}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    @Test
    public void aCallerThatMetAReturnOnlyFormalIsRequeuedWhenItTurns() {
        String g = "<m.G: int g(int)>";
        String formal = g + ".param0:int";
        String local = g + "::i0";
        Set<String> relevant = new LinkedHashSet<>(Arrays.asList(
                g + ".return", local, formal));
        Set<String> requeued = new TreeSet<>();
        ReturnOnlyFormals summaries = new ReturnOnlyFormals(
                new ReturnOnlyFormals.Slice() {
                    @Override
                    public Set<String> relevant(String method) {
                        return g.equals(method) ? relevant
                                : Collections.<String>emptySet();
                    }

                    @Override
                    public String thisCell(String method) {
                        return null;
                    }

                    @Override
                    public void requeue(String method) {
                        requeued.add(method);
                    }
                });
        summaries.row(row("local_def_use", formal, local, g));
        summaries.row(row("local_def_use", local, g + ".return", g));
        boolean unused = summaries.demanded(g, formal, false, "<m.C: void c()>");
        boolean used = summaries.demanded(g, formal, true, "<m.D: int d()>");
        requeued.clear();
        summaries.row(row("field_write", local, "<m.G: int seen>", g));
        Object[][] rows = {
                {"a call whose result is unused does not demand it", false,
                        unused},
                {"one whose result is does", true, used},
                {"a store makes it an effect", false,
                        summaries.returnOnly(g, formal)},
                {"its method and every caller that met it are re-queued",
                        names("<m.C: void c()>", "<m.D: int d()>", g),
                        requeued}};
        for (Object[] each : rows) {
            assertEquals((String) each[0], each[1], each[2]);
        }
    }

    private static Map<String, Object> row(String kind, String from,
                                           String to, String method) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("kind", kind);
        row.put("fromCell", from);
        row.put("toCell", to);
        row.put("method", method);
        return row;
    }

    /** The names of the methods whose actuals reach the method's first
     *  formal. */
    private static Set<String> callers(StaticProgram program, String method) {
        return into(program, (method.startsWith("<") ? method
                : "<" + PB + ": " + method + ">") + ".param0:int", ARGUMENTS);
    }

    private static Set<String> into(StaticProgram program, String cell,
                                    String kind) {
        return into(program, cell, Collections.singleton(kind));
    }

    /** The names of the methods of the rows of {@code kinds} into {@code
     *  cell}. */
    private static Set<String> into(StaticProgram program, String cell,
                                    Set<String> kinds) {
        Set<String> found = new TreeSet<>();
        for (Map<String, Object> edge : program.edges) {
            if (cell.equals(edge.get("toCell"))
                    && kinds.contains(edge.get("kind"))) {
                String caller = (String) edge.get("method");
                found.add(caller.substring(caller.indexOf(' ',
                        caller.indexOf(": ") + 2) + 1, caller.indexOf('(')));
            }
        }
        return found;
    }

    private static Set<String> names(String... names) {
        return new TreeSet<>(Arrays.asList(names));
    }

    /** The scene, and the declared throw in {@code check}. */
    private static CausynthTargetContext target() {
        // check sums what each keyed caller, field and chain returns.
        String[] reads = {"staticinvoke " + pb("int encodeKey(int)") + "(i0)",
                "staticinvoke " + pb("int recordKey(int)") + "(i0)",
                pb("int last"), "staticinvoke "
                + pb("int codeKey(m.Codec,int)") + "(r0, i0)",
                pb("int logged"), "staticinvoke " + pb("int downKey(int)")
                + "(i0)", "staticinvoke " + pb("int parityKey(int)") + "(i0)",
                "staticinvoke " + pb("int lit()") + "()", "staticinvoke "
                + pb("int applyKey(m.Scale,int)") + "(r2, i0)",
                "staticinvoke " + pb("int putKey(int[],int)") + "(r6, i0)",
                "staticinvoke " + pb("int hold(m.Bag,java.lang.Object)")
                        + "(r3, r4)",
                "staticinvoke " + pb("int spiKey(m.Spi,int)") + "(r5, i0)",
                "staticinvoke " + pb("int idle1(m.Spi,int)") + "(r5, i0)",
                "staticinvoke " + pb("int seen1()") + "()",
                pb("int logged2")};
        StringBuilder locals = new StringBuilder("int i0; m.Codec r0;"
                + " m.Scale r2; m.Bag r3; java.lang.Object r4; m.Spi r5;"
                + " int[] r6;");
        StringBuilder sums = new StringBuilder();
        for (int n = 0; n < reads.length; n++) {
            locals.append(" int v").append(n).append(';');
            sums.append(" v").append(n).append(" = ").append(reads[n])
                    .append(';');
            if (n == 0) continue;
            locals.append(" int s").append(n).append(';');
            sums.append(" s").append(n).append(" = ").append(n == 1 ? "v0"
                    : "s" + (n - 1)).append(" + v").append(n).append(';');
        }
        JimpleScene.load(JimpleScene.OBJECT, JimpleScene.FAILURE,
                "application public class m.Pb extends java.lang.Object {"
                        + " public static int last; public static int logged;"
                        + " public static int cipher;"
                        + " public static int seen; public static int logged2;"
                        // wrap: a pure helper, called by a keyed and an idle
                        // encoder.
                        + " public static int wrap(int) { int i0, i1;"
                        + " i0 := @parameter0: int; i1 = i0 + 1; return i1; }"
                        + keyed("encodeKey", "wrap")
                        + " public static void encodeCipher(int) { int i0, i1;"
                        + " i0 := @parameter0: int; i1 = staticinvoke "
                        + pb("int wrap(int)") + "(i0); " + pb("int cipher")
                        + " = i1; return; }"
                        // record: returns its formal and stores it where
                        // check reads it.
                        + " public static int record(int) { int i0;"
                        + " i0 := @parameter0: int; " + pb("int last")
                        + " = i0; return i0; }"
                        + keyed("recordKey", "record")
                        + idle("recordIdle", "record")
                        // code: an interface call, one implementation pure,
                        // one storing.
                        + via("codeKey", "m.Codec", "interfaceinvoke",
                                "<m.Codec: int code(int)>", "return")
                        + via("codeIdle", "m.Codec", "interfaceinvoke",
                                "<m.Codec: int code(int)>", "void")
                        // down: calls itself; even and odd: call each other.
                        + recurse("down", "down", 0)
                        + recurse("even", "odd", 1)
                        + recurse("odd", "even", 0)
                        + keyed("downKey", "down") + idle("downIdle", "down")
                        + keyed("parityKey", "even")
                        + idle("parityIdle", "even")
                        // lit: wrap's literal actual, its result demanded;
                        // litIdle's not.
                        + " public static int lit() { int i0; i0 ="
                        + " staticinvoke " + pb("int wrap(int)")
                        + "(7); return i0; }"
                        + " public static void litIdle() { int i0;"
                        + " staticinvoke " + pb("int wrap(int)")
                        + "(7); return; }"
                        + via("applyKey", "m.Scale", "virtualinvoke",
                                "<m.Scale: int apply(int)>", "return")
                        + via("applyIdle", "m.Scale", "virtualinvoke",
                                "<m.Scale: int apply(int)>", "void")
                        // put: stores its value into the array it is passed,
                        // returns it.
                        + " public static int put(int[], int) { int[] r0;"
                        + " int i0, i1; r0 := @parameter0: int[];"
                        + " i0 := @parameter1: int; r0[0] = i0; i1 = r0[0];"
                        + " return i1; }"
                        + via("putKey", "int[]", "staticinvoke", pb(
                                "int put(int[],int)"), "return")
                        + via("putIdle", "int[]", "staticinvoke", pb(
                                "int put(int[],int)"), "void")
                        // hold asks the bag's size after keep.
                        + " public static int hold(m.Bag, java.lang.Object) {"
                        + " m.Bag r0; java.lang.Object r1; int i0;"
                        + " r0 := @parameter0: m.Bag;"
                        + " r1 := @parameter1: java.lang.Object;"
                        + " virtualinvoke r0.<m.Bag: void keep("
                        + "java.lang.Object)>(r1); i0 = virtualinvoke"
                        + " r0.<java.util.ArrayList: int size()>();"
                        + " return i0; }"
                        // Late.tick through Spi, which inherits it from
                        // Base: it returns its formal and stores it into
                        // seen, which check reaches four calls down, after
                        // the return made the formal return-only; spiIdle,
                        // three calls down, drops the call's result.
                        + via("spiKey", "m.Spi", "interfaceinvoke",
                                "<m.Spi: int tick(int)>", "return")
                        + via("spiIdle", "m.Spi", "interfaceinvoke",
                                "<m.Spi: int tick(int)>", "next")
                        + via("idle2", "m.Spi", "staticinvoke",
                                pb("int spiIdle(m.Spi,int)"), "return")
                        + via("idle1", "m.Spi", "staticinvoke",
                                pb("int idle2(m.Spi,int)"), "return")
                        + seen(4, pb("int seen")) + seen(3, "seen4")
                        + seen(2, "seen3") + seen(1, "seen2")
                        // Late2.probe through Spi2, inheriting a library's
                        // Probe.probe.
                        + via("spi2Idle", "m.Spi2", "interfaceinvoke",
                                "<m.Spi2: int probe(int)>", "next")
                        + " public static void check(int, m.Codec, m.Scale,"
                        + " m.Bag, java.lang.Object, m.Spi) { " + locals
                        + " java.lang.IllegalStateException r1;"
                        + " i0 := @parameter0: int; r0 := @parameter1: m.Codec;"
                        + " r2 := @parameter2: m.Scale;"
                        + " r3 := @parameter3: m.Bag;"
                        + " r4 := @parameter4: java.lang.Object;"
                        + " r5 := @parameter5: m.Spi;"
                        + " r6 = newarray (int)[1];" + sums
                        + " if s14 != 0 goto label1;"
                        + " r1 = new java.lang.IllegalStateException;"
                        + " throw r1; label1: return; } }",
                "application public abstract interface m.Codec extends"
                        + " java.lang.Object { public abstract int code(int);"
                        + " }",
                code("m.PureCodec", "i1 = i0 + 1; return i1;"),
                code("m.LoggingCodec", pb("int logged")
                        + " = i0; return i0;"),
                // Scale.apply: reads its receiver's field into its return
                // only.
                "application public class m.Scale extends java.lang.Object"
                        + " { public int base; public int apply(int) {"
                        + " m.Scale r0; int i0, i1, i2; r0 := @this: m.Scale;"
                        + " i0 := @parameter0: int;"
                        + " i1 = r0.<m.Scale: int base>; i2 = i0 + i1;"
                        + " return i2; } }",
                // Bag.keep: a JDK list's subclass adding to itself.
                "public class java.util.ArrayList extends java.lang.Object {"
                        + " public boolean add(java.lang.Object) { }"
                        + " public int size() { } }",
                "application public class m.Bag extends java.util.ArrayList {"
                        + " public void keep(java.lang.Object) { m.Bag r0;"
                        + " java.lang.Object r1; r0 := @this: m.Bag;"
                        + " r1 := @parameter0: java.lang.Object;"
                        + " virtualinvoke r0.<java.util.ArrayList: boolean"
                        + " add(java.lang.Object)>(r1); return; } }",
                "application public abstract interface m.Base extends"
                        + " java.lang.Object { public abstract int tick(int);"
                        + " }",
                "application public abstract interface m.Spi extends"
                        + " java.lang.Object implements m.Base { }",
                storing("m.Late", "m.Spi", "tick", "seen"),
                "public abstract interface javax.probe.Probe extends"
                        + " java.lang.Object { public abstract int probe(int);"
                        + " }",
                "application public abstract interface m.Spi2 extends"
                        + " java.lang.Object implements javax.probe.Probe { }",
                storing("m.Late2", "m.Spi2", "probe", "logged2"));
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", PB, "check", "(ILm/Codec;"
                        + "Lm/Scale;Lm/Bag;Ljava/lang/Object;Lm/Spi;)V",
                        CHECK, "java.lang.IllegalStateException", 0));
    }

    /** {@code <m.Pb: member>}. */
    private static String pb(String member) {
        return "<" + PB + ": " + member + ">";
    }

    /** {@code int name(int k) { return callee(k); }} */
    private static String keyed(String name, String callee) {
        return " public static int " + name + "(int) { int i0, i1;"
                + " i0 := @parameter0: int; i1 = staticinvoke "
                + pb("int " + callee + "(int)") + "(i0); return i1; }";
    }

    /** {@code void name(int k) { callee(k); }} */
    private static String idle(String name, String callee) {
        return " public static void " + name + "(int) { int i0;"
                + " i0 := @parameter0: int; staticinvoke "
                + pb("int " + callee + "(int)") + "(i0); return; }";
    }

    /**
     * {@code name(T r, int k)} calling {@code callee} on {@code (r, k)}
     * (a receiver's call takes {@code r} as its receiver): {@code return}
     * returns its result, {@code void} drops it, {@code next} drops it and
     * returns {@code k + 1} (its own result demanded, the call's not).
     */
    private static String via(String name, String type, String invoke,
                              String callee, String ending) {
        String call = invoke + (invoke.equals("staticinvoke") ? " " + callee
                + "(r0, i0)" : " r0." + callee + "(i0)");
        return " public static " + (ending.equals("void") ? "void" : "int")
                + " " + name + "(" + type + ", int) { " + type + " r0;"
                + " int i0, i1; r0 := @parameter0: " + type + ";"
                + " i0 := @parameter1: int; " + (ending.equals("return")
                ? "i1 = " + call + "; return i1; }" : call + "; "
                + (ending.equals("void") ? "return; }"
                : "i1 = i0 + 1; return i1; }"));
    }

    /** {@code int m(int k) { if (k == 0) return base; return callee(k - 1);
     *  }} */
    private static String recurse(String name, String callee, int base) {
        return " public static int " + name + "(int) { int i0, i1, i2;"
                + " i0 := @parameter0: int; if i0 == 0 goto label1;"
                + " i1 = i0 - 1; i2 = staticinvoke " + pb("int " + callee
                + "(int)") + "(i1); return i2; label1: return " + base
                + "; }";
    }

    /** {@code int seen<n>() { return read; }}: {@code read} a field, or
     *  the next method of the chain. */
    private static String seen(int n, String read) {
        return " public static int seen" + n + "() { int i0; i0 = "
                + (read.startsWith("<") ? read : "staticinvoke "
                + pb("int " + read + "()") + "()") + "; return i0; }";
    }

    /** A codec whose {@code code} runs {@code tail} over {@code i0}. */
    private static String code(String name, String tail) {
        return "application public class " + name + " extends"
                + " java.lang.Object implements m.Codec { public int"
                + " code(int) { " + name + " r0; int i0, i1; r0 := @this: "
                + name + "; i0 := @parameter0: int; " + tail + " } }";
    }

    /** {@code int m(int k) { field = k; return k; }} in {@code type}, an
     *  implementation of {@code contract}. */
    private static String storing(String type, String contract, String name,
                                  String field) {
        return "application public class " + type + " extends"
                + " java.lang.Object implements " + contract + " { public int "
                + name + "(int) { " + type + " r0; int i0; r0 := @this: "
                + type + "; i0 := @parameter0: int; " + pb("int " + field)
                + " = i0; return i0; } }";
    }
}
