package edu.uva.liftlab.graphchecker.causynth;

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
import soot.Value;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.options.Options;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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
        G.reset();
        Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        library("java.lang.IllegalStateException", object, 0);
        SootClass pb = application(PB, object, 0);
        SootField last = field(pb, "last");
        SootField logged = field(pb, "logged");
        SootField cipher = field(pb, "cipher");
        IntType i = IntType.v();

        // wrap: a pure helper, called by a keyed and an idle encoder.
        SootMethod wrap = staticMethod(pb, "wrap", i);
        Local[] w = locals(wrap, 2);
        body(wrap, param(w[0], 0), Jimple.v().newAssignStmt(w[1],
                Jimple.v().newAddExpr(w[0], IntConstant.v(1))),
                Jimple.v().newReturnStmt(w[1]));
        SootMethod encodeKey = keyed(pb, "encodeKey", wrap);
        SootMethod encodeCipher = staticMethod(pb, "encodeCipher",
                VoidType.v());
        Local[] c = locals(encodeCipher, 2);
        body(encodeCipher, param(c[0], 0), Jimple.v().newAssignStmt(c[1],
                Jimple.v().newStaticInvokeExpr(wrap.makeRef(), c[0])),
                Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(
                        cipher.makeRef()), c[1]),
                Jimple.v().newReturnVoidStmt());

        // record: returns its formal and stores it where check reads it.
        SootMethod record = staticMethod(pb, "record", i);
        Local[] r = locals(record, 1);
        body(record, param(r[0], 0), Jimple.v().newAssignStmt(Jimple.v()
                        .newStaticFieldRef(last.makeRef()), r[0]),
                Jimple.v().newReturnStmt(r[0]));
        SootMethod recordKey = keyed(pb, "recordKey", record);
        idle(pb, "recordIdle", record);

        // code: an interface call, one implementation pure, one storing.
        SootClass codec = application("m.Codec", object,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        SootMethod code = new SootMethod("code",
                Collections.<Type>singletonList(i), i,
                Modifier.PUBLIC | Modifier.ABSTRACT);
        codec.addMethod(code);
        for (String name : new String[]{"m.PureCodec", "m.LoggingCodec"}) {
            SootClass implementation = application(name, object, 0);
            implementation.addInterface(codec);
            SootMethod body = method(implementation, "code",
                    Collections.<Type>singletonList(i), i, 0);
            Local self = local(body, "r0", implementation.getType());
            Local[] k = locals(body, 2);
            List<Unit> units = new ArrayList<>(Arrays.asList(
                    Jimple.v().newIdentityStmt(self,
                            Jimple.v().newThisRef(implementation.getType())),
                    param(k[0], 0)));
            if (name.endsWith("PureCodec")) {
                units.add(Jimple.v().newAssignStmt(k[1],
                        Jimple.v().newAddExpr(k[0], IntConstant.v(1))));
                units.add(Jimple.v().newReturnStmt(k[1]));
            } else {
                units.add(Jimple.v().newAssignStmt(Jimple.v()
                        .newStaticFieldRef(logged.makeRef()), k[0]));
                units.add(Jimple.v().newReturnStmt(k[0]));
            }
            body(body, units.toArray(new Unit[0]));
        }
        SootMethod codeKey = null;
        for (String name : new String[]{"codeKey", "codeIdle"}) {
            boolean keyed = "codeKey".equals(name);
            SootMethod caller = method(pb, name, Arrays.<Type>asList(
                    codec.getType(), i), keyed ? i : VoidType.v(),
                    Modifier.STATIC);
            Local held = local(caller, "r0", codec.getType());
            Local[] k = locals(caller, 2);
            Value call = Jimple.v().newInterfaceInvokeExpr(held,
                    code.makeRef(), k[0]);
            body(caller, Jimple.v().newIdentityStmt(held,
                            Jimple.v().newParameterRef(codec.getType(), 0)),
                    Jimple.v().newIdentityStmt(k[0],
                            Jimple.v().newParameterRef(i, 1)),
                    keyed ? Jimple.v().newAssignStmt(k[1], call)
                            : Jimple.v().newInvokeStmt(call),
                    keyed ? Jimple.v().newReturnStmt(k[1])
                            : Jimple.v().newReturnVoidStmt());
            if (keyed) codeKey = caller;
        }

        // down: calls itself; even and odd: call each other.
        SootMethod down = staticMethod(pb, "down", i);
        SootMethod even = staticMethod(pb, "even", i);
        SootMethod odd = staticMethod(pb, "odd", i);
        recurse(down, down, 0);
        recurse(even, odd, 1);
        recurse(odd, even, 0);
        SootMethod downKey = keyed(pb, "downKey", down);
        idle(pb, "downIdle", down);
        SootMethod parityKey = keyed(pb, "parityKey", even);
        idle(pb, "parityIdle", even);

        // lit: wrap's literal actual, its result demanded; litIdle's not.
        SootMethod lit = null;
        for (String name : new String[]{"lit", "litIdle"}) {
            boolean keyed = "lit".equals(name);
            SootMethod caller = method(pb, name, Collections.<Type>emptyList(),
                    keyed ? i : VoidType.v(), Modifier.STATIC);
            Local[] k = locals(caller, 1);
            Value call = Jimple.v().newStaticInvokeExpr(wrap.makeRef(),
                    IntConstant.v(7));
            body(caller, keyed ? Jimple.v().newAssignStmt(k[0], call)
                            : Jimple.v().newInvokeStmt(call),
                    keyed ? Jimple.v().newReturnStmt(k[0])
                            : Jimple.v().newReturnVoidStmt());
            if (keyed) lit = caller;
        }

        // Scale.apply: reads its receiver's field into its return only.
        SootClass scale = application("m.Scale", object, 0);
        SootField base = new SootField("base", i, Modifier.PUBLIC);
        scale.addField(base);
        SootMethod apply = method(scale, "apply",
                Collections.<Type>singletonList(i), i, 0);
        Local self = local(apply, "r0", scale.getType());
        Local[] a = locals(apply, 3);
        body(apply, Jimple.v().newIdentityStmt(self,
                        Jimple.v().newThisRef(scale.getType())),
                param(a[0], 0), Jimple.v().newAssignStmt(a[1], Jimple.v()
                        .newInstanceFieldRef(self, base.makeRef())),
                Jimple.v().newAssignStmt(a[2], Jimple.v().newAddExpr(a[0],
                        a[1])), Jimple.v().newReturnStmt(a[2]));
        SootMethod applyKey = viaReceiver(pb, "applyKey", scale, apply,
                true);
        viaReceiver(pb, "applyIdle", scale, apply, false);

        // put: stores its value into the array it is passed, returns it.
        ArrayType ints = ArrayType.v(i, 1);
        SootMethod put = method(pb, "put", Arrays.<Type>asList(ints, i), i,
                Modifier.STATIC);
        Local buf = local(put, "r0", ints);
        Local[] v = locals(put, 2);
        body(put, Jimple.v().newIdentityStmt(buf,
                        Jimple.v().newParameterRef(ints, 0)),
                Jimple.v().newIdentityStmt(v[0],
                        Jimple.v().newParameterRef(i, 1)),
                Jimple.v().newAssignStmt(Jimple.v().newArrayRef(buf,
                        IntConstant.v(0)), v[0]),
                Jimple.v().newAssignStmt(v[1], Jimple.v().newArrayRef(buf,
                        IntConstant.v(0))), Jimple.v().newReturnStmt(v[1]));
        SootMethod putKey = null;
        for (String name : new String[]{"putKey", "putIdle"}) {
            boolean keyed = "putKey".equals(name);
            SootMethod caller = method(pb, name, Arrays.<Type>asList(ints,
                    i), keyed ? i : VoidType.v(), Modifier.STATIC);
            Local array = local(caller, "r0", ints);
            Local[] k = locals(caller, 2);
            Value call = Jimple.v().newStaticInvokeExpr(put.makeRef(), array,
                    k[0]);
            body(caller, Jimple.v().newIdentityStmt(array,
                            Jimple.v().newParameterRef(ints, 0)),
                    Jimple.v().newIdentityStmt(k[0],
                            Jimple.v().newParameterRef(i, 1)),
                    keyed ? Jimple.v().newAssignStmt(k[1], call)
                            : Jimple.v().newInvokeStmt(call),
                    keyed ? Jimple.v().newReturnStmt(k[1])
                            : Jimple.v().newReturnVoidStmt());
            if (keyed) putKey = caller;
        }

        // Bag.keep: a JDK list's subclass adding to itself; hold asks the
        // bag's size after keep.
        RefType objectType = object.getType();
        SootClass list = library("java.util.ArrayList", object, 0);
        SootMethod add = method(list, "add",
                Collections.<Type>singletonList(objectType),
                BooleanType.v(), 0);
        SootMethod size = method(list, "size", Collections.<Type>emptyList(),
                i, 0);
        SootClass bag = application("m.Bag", list, 0);
        SootMethod keep = method(bag, "keep",
                Collections.<Type>singletonList(objectType), VoidType.v(), 0);
        Local kept = local(keep, "r0", bag.getType());
        Local item = local(keep, "r1", objectType);
        body(keep, Jimple.v().newIdentityStmt(kept,
                        Jimple.v().newThisRef(bag.getType())),
                Jimple.v().newIdentityStmt(item,
                        Jimple.v().newParameterRef(objectType, 0)),
                Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(
                        kept, add.makeRef(), item)),
                Jimple.v().newReturnVoidStmt());
        SootMethod hold = method(pb, "hold", Arrays.<Type>asList(
                bag.getType(), objectType), i, Modifier.STATIC);
        Local bagged = local(hold, "r0", bag.getType());
        Local thing = local(hold, "r1", objectType);
        Local[] h = locals(hold, 1);
        body(hold, Jimple.v().newIdentityStmt(bagged,
                        Jimple.v().newParameterRef(bag.getType(), 0)),
                Jimple.v().newIdentityStmt(thing,
                        Jimple.v().newParameterRef(objectType, 1)),
                Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(
                        bagged, keep.makeRef(), thing)),
                Jimple.v().newAssignStmt(h[0], Jimple.v()
                        .newVirtualInvokeExpr(bagged, size.makeRef())),
                Jimple.v().newReturnStmt(h[0]));

        // Late.tick through Spi, which inherits it from Base: it returns its
        // formal and stores it into seen, which check reaches four calls
        // down, after the return made the formal return-only; spiIdle,
        // three calls down, drops the call's result.
        SootField seen = field(pb, "seen");
        SootClass baseType = application("m.Base", object,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        SootMethod tick = new SootMethod("tick",
                Collections.<Type>singletonList(i), i,
                Modifier.PUBLIC | Modifier.ABSTRACT);
        baseType.addMethod(tick);
        SootClass spi = application("m.Spi", object,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        spi.addInterface(baseType);
        storing(application("m.Late", object, 0), spi, "tick", seen);
        SootMethod spiKey = viaInterface(pb, "spiKey", spi,
                Scene.v().makeMethodRef(spi, "tick",
                        Collections.<Type>singletonList(i), i, false), true);
        SootMethod spiIdle = viaInterface(pb, "spiIdle", spi,
                Scene.v().makeMethodRef(spi, "tick",
                        Collections.<Type>singletonList(i), i, false), false);
        SootMethod idle2 = forward(pb, "idle2", spi, spiIdle);
        SootMethod idle1 = forward(pb, "idle1", spi, idle2);
        SootMethod seen1 = reading(pb, seen, 4);

        // Late2.probe through Spi2, inheriting a library's Probe.probe.
        SootField logged2 = field(pb, "logged2");
        SootClass probe = library("javax.probe.Probe", object,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        probe.addMethod(new SootMethod("probe",
                Collections.<Type>singletonList(i), i,
                Modifier.PUBLIC | Modifier.ABSTRACT));
        SootClass spi2 = application("m.Spi2", object,
                Modifier.INTERFACE | Modifier.ABSTRACT);
        spi2.addInterface(probe);
        storing(application("m.Late2", object, 0), spi2, "probe", logged2);
        viaInterface(pb, "spi2Idle", spi2, Scene.v().makeMethodRef(spi2,
                "probe", Collections.<Type>singletonList(i), i, false),
                false);

        SootMethod check = method(pb, "check", Arrays.<Type>asList(i,
                codec.getType(), scale.getType(), bag.getType(), objectType,
                spi.getType()), VoidType.v(), Modifier.STATIC);
        Local key = local(check, "i0", i);
        Local held = local(check, "r0", codec.getType());
        Local scaled = local(check, "r2", scale.getType());
        Local bagParam = local(check, "r3", bag.getType());
        Local objectParam = local(check, "r4", objectType);
        Local spiParam = local(check, "r5", spi.getType());
        Local array = local(check, "r6", ints);
        Value[] read = {
                Jimple.v().newStaticInvokeExpr(encodeKey.makeRef(), key),
                Jimple.v().newStaticInvokeExpr(recordKey.makeRef(), key),
                Jimple.v().newStaticFieldRef(last.makeRef()),
                Jimple.v().newStaticInvokeExpr(codeKey.makeRef(), held, key),
                Jimple.v().newStaticFieldRef(logged.makeRef()),
                Jimple.v().newStaticInvokeExpr(downKey.makeRef(), key),
                Jimple.v().newStaticInvokeExpr(parityKey.makeRef(), key),
                Jimple.v().newStaticInvokeExpr(lit.makeRef()),
                Jimple.v().newStaticInvokeExpr(applyKey.makeRef(), scaled,
                        key),
                Jimple.v().newStaticInvokeExpr(putKey.makeRef(), array, key),
                Jimple.v().newStaticInvokeExpr(hold.makeRef(), bagParam,
                        objectParam),
                Jimple.v().newStaticInvokeExpr(spiKey.makeRef(), spiParam,
                        key),
                Jimple.v().newStaticInvokeExpr(idle1.makeRef(), spiParam,
                        key),
                Jimple.v().newStaticInvokeExpr(seen1.makeRef()),
                Jimple.v().newStaticFieldRef(logged2.makeRef())};
        List<Unit> units = new ArrayList<>(Arrays.asList(
                Jimple.v().newIdentityStmt(key,
                        Jimple.v().newParameterRef(i, 0)),
                Jimple.v().newIdentityStmt(held,
                        Jimple.v().newParameterRef(codec.getType(), 1)),
                Jimple.v().newIdentityStmt(scaled,
                        Jimple.v().newParameterRef(scale.getType(), 2)),
                Jimple.v().newIdentityStmt(bagParam,
                        Jimple.v().newParameterRef(bag.getType(), 3)),
                Jimple.v().newIdentityStmt(objectParam,
                        Jimple.v().newParameterRef(objectType, 4)),
                Jimple.v().newIdentityStmt(spiParam,
                        Jimple.v().newParameterRef(spi.getType(), 5)),
                Jimple.v().newAssignStmt(array,
                        Jimple.v().newNewArrayExpr(i, IntConstant.v(1)))));
        Local sum = null;
        for (int n = 0; n < read.length; n++) {
            Local value = local(check, "v" + n, i);
            units.add(Jimple.v().newAssignStmt(value, read[n]));
            if (sum == null) {
                sum = value;
                continue;
            }
            Local next = local(check, "s" + n, i);
            units.add(Jimple.v().newAssignStmt(next,
                    Jimple.v().newAddExpr(sum, value)));
            sum = next;
        }
        RefType failure = RefType.v("java.lang.IllegalStateException");
        Local thrown = local(check, "r1", failure);
        Unit done = Jimple.v().newReturnVoidStmt();
        units.add(Jimple.v().newIfStmt(Jimple.v().newNeExpr(sum,
                IntConstant.v(0)), done));
        units.add(Jimple.v().newAssignStmt(thrown,
                Jimple.v().newNewExpr(failure)));
        units.add(Jimple.v().newThrowStmt(thrown));
        units.add(done);
        body(check, units.toArray(new Unit[0]));
        return new CausynthTargetContext(Paths.get("unused"),
                new ExceptionTargetSite("t", PB, "check", "(ILm/Codec;"
                        + "Lm/Scale;Lm/Bag;Ljava/lang/Object;Lm/Spi;)V",
                        CHECK, "java.lang.IllegalStateException", 0));
    }

    /** {@code int name(int k) { return callee(k); }} */
    private static SootMethod keyed(SootClass owner, String name,
                                    SootMethod callee) {
        SootMethod method = staticMethod(owner, name, IntType.v());
        Local[] k = locals(method, 2);
        body(method, param(k[0], 0), Jimple.v().newAssignStmt(k[1],
                Jimple.v().newStaticInvokeExpr(callee.makeRef(), k[0])),
                Jimple.v().newReturnStmt(k[1]));
        return method;
    }

    /** {@code [int] name(C c, int k) { [return] c.callee(k); }} */
    private static SootMethod viaReceiver(SootClass owner, String name,
                                          SootClass type, SootMethod callee,
                                          boolean keyed) {
        SootMethod method = method(owner, name, Arrays.<Type>asList(
                type.getType(), IntType.v()), keyed ? IntType.v()
                : VoidType.v(), Modifier.STATIC);
        Local held = local(method, "r0", type.getType());
        Local[] k = locals(method, 2);
        Value call = Jimple.v().newVirtualInvokeExpr(held, callee.makeRef(),
                k[0]);
        body(method, Jimple.v().newIdentityStmt(held,
                        Jimple.v().newParameterRef(type.getType(), 0)),
                param(k[0], 1),
                keyed ? Jimple.v().newAssignStmt(k[1], call)
                        : Jimple.v().newInvokeStmt(call),
                keyed ? Jimple.v().newReturnStmt(k[1])
                        : Jimple.v().newReturnVoidStmt());
        return method;
    }

    /** {@code int name(I s, int k) { return s.m(k); }} when keyed, else
     *  {@code int name(I s, int k) { s.m(k); return k + 1; }}: its own
     *  result is demanded, the call's is not. */
    private static SootMethod viaInterface(SootClass owner, String name,
                                           SootClass type,
                                           soot.SootMethodRef callee,
                                           boolean keyed) {
        SootMethod method = method(owner, name, Arrays.<Type>asList(
                type.getType(), IntType.v()), IntType.v(), Modifier.STATIC);
        Local held = local(method, "r0", type.getType());
        Local[] k = locals(method, 2);
        Value call = Jimple.v().newInterfaceInvokeExpr(held, callee, k[0]);
        body(method, Jimple.v().newIdentityStmt(held,
                        Jimple.v().newParameterRef(type.getType(), 0)),
                param(k[0], 1),
                keyed ? Jimple.v().newAssignStmt(k[1], call)
                        : Jimple.v().newInvokeStmt(call),
                keyed ? Jimple.v().newReturnStmt(k[1])
                        : Jimple.v().newAssignStmt(k[1], Jimple.v()
                        .newAddExpr(k[0], IntConstant.v(1))),
                keyed ? null : Jimple.v().newReturnStmt(k[1]));
        return method;
    }

    /** {@code int name(I s, int k) { return callee(s, k); }} */
    private static SootMethod forward(SootClass owner, String name,
                                      SootClass type, SootMethod callee) {
        SootMethod method = method(owner, name, Arrays.<Type>asList(
                type.getType(), IntType.v()), IntType.v(), Modifier.STATIC);
        Local held = local(method, "r0", type.getType());
        Local[] k = locals(method, 2);
        body(method, Jimple.v().newIdentityStmt(held,
                        Jimple.v().newParameterRef(type.getType(), 0)),
                param(k[0], 1), Jimple.v().newAssignStmt(k[1], Jimple.v()
                        .newStaticInvokeExpr(callee.makeRef(), held, k[0])),
                Jimple.v().newReturnStmt(k[1]));
        return method;
    }

    /** {@code int m(int k) { field = k; return k; }} in {@code type}, an
     *  implementation of {@code contract}. */
    private static void storing(SootClass type, SootClass contract,
                                String name, SootField field) {
        type.addInterface(contract);
        SootMethod method = method(type, name,
                Collections.<Type>singletonList(IntType.v()), IntType.v(), 0);
        Local self = local(method, "r0", type.getType());
        Local[] k = locals(method, 1);
        body(method, Jimple.v().newIdentityStmt(self,
                        Jimple.v().newThisRef(type.getType())),
                param(k[0], 0), Jimple.v().newAssignStmt(Jimple.v()
                        .newStaticFieldRef(field.makeRef()), k[0]),
                Jimple.v().newReturnStmt(k[0]));
    }

    /** {@code int seen<depth>() { return seen<depth-1>(); }} down to {@code
     *  seen1}'s read of {@code field}; answers the outermost. */
    private static SootMethod reading(SootClass owner, SootField field,
                                      int depth) {
        SootMethod inner = null;
        for (int n = depth; n >= 1; n--) {
            SootMethod method = method(owner, "seen" + n,
                    Collections.<Type>emptyList(), IntType.v(),
                    Modifier.STATIC);
            Local[] k = locals(method, 1);
            body(method, Jimple.v().newAssignStmt(k[0], inner == null
                            ? Jimple.v().newStaticFieldRef(field.makeRef())
                            : Jimple.v().newStaticInvokeExpr(inner.makeRef())),
                    Jimple.v().newReturnStmt(k[0]));
            inner = method;
        }
        return inner;
    }

    /** {@code void name(int k) { callee(k); }} */
    private static void idle(SootClass owner, String name,
                             SootMethod callee) {
        SootMethod method = staticMethod(owner, name, VoidType.v());
        Local[] k = locals(method, 1);
        body(method, param(k[0], 0), Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(callee.makeRef(), k[0])),
                Jimple.v().newReturnVoidStmt());
    }

    /** {@code int m(int k) { if (k == 0) return base; return callee(k - 1);
     *  }} */
    private static void recurse(SootMethod method, SootMethod callee,
                                int base) {
        Local[] k = locals(method, 3);
        Unit bottom = Jimple.v().newReturnStmt(IntConstant.v(base));
        body(method, param(k[0], 0), Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(k[0], IntConstant.v(0)), bottom),
                Jimple.v().newAssignStmt(k[1], Jimple.v().newSubExpr(k[0],
                        IntConstant.v(1))),
                Jimple.v().newAssignStmt(k[2], Jimple.v()
                        .newStaticInvokeExpr(callee.makeRef(), k[1])),
                Jimple.v().newReturnStmt(k[2]), bottom);
    }

    private static Unit param(Local local, int index) {
        return Jimple.v().newIdentityStmt(local,
                Jimple.v().newParameterRef(IntType.v(), index));
    }

    private static SootField field(SootClass owner, String name) {
        SootField field = new SootField(name, IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(field);
        return field;
    }

    private static SootMethod staticMethod(SootClass owner, String name,
                                           Type returned) {
        return method(owner, name, Collections.<Type>singletonList(
                IntType.v()), returned, Modifier.STATIC);
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
        method.setActiveBody(Jimple.v().newBody(method));
        return method;
    }

    /** {@code i0}, {@code i1}, ... in the method's body. */
    private static Local[] locals(SootMethod method, int count) {
        Local[] locals = new Local[count];
        for (int n = 0; n < count; n++) {
            locals[n] = local(method, "i" + n, IntType.v());
        }
        return locals;
    }

    private static Local local(SootMethod method, String name, Type type) {
        Local local = Jimple.v().newLocal(name, type);
        method.getActiveBody().getLocals().add(local);
        return local;
    }

    private static void body(SootMethod method, Unit... units) {
        for (Unit unit : units) {
            if (unit != null) method.getActiveBody().getUnits().add(unit);
        }
    }
}
