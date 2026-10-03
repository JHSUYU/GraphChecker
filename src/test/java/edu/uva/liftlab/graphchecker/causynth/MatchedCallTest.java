package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.Assert.assertEquals;

/**
 * Matched calls ({@link ReturnOnlyFormals}): a formal only its method's
 * return needs is demanded only at the calls whose result is.  The scene's
 * declared throw in {@code check} decides on the results of five keyed
 * callers and on two fields; beside each keyed caller an idle one makes the
 * same call and drops or stores the result where nothing reads it.
 */
public class MatchedCallTest {
    private static final String PB = "m.Pb";
    private static final String CHECK = "<m.Pb: void check(int,m.Codec)>";
    private static final Set<String> ARGUMENTS = names("call_argument",
            "caller_argument", "dispatch_argument",
            "dispatch_caller_argument");

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aFormalOnlyTheReturnNeedsReachesOnlyTheDemandedCalls()
            throws Exception {
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
                        callers(program, "int even(int)")}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** The names of the methods whose actuals reach the method's first
     *  formal. */
    private static Set<String> callers(StaticProgram program, String method) {
        String formal = (method.startsWith("<") ? method
                : "<" + PB + ": " + method + ">") + ".param0:int";
        Set<String> found = new TreeSet<>();
        for (Map<String, Object> edge : program.edges) {
            if (formal.equals(edge.get("toCell"))
                    && ARGUMENTS.contains(edge.get("kind"))) {
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

        SootMethod check = method(pb, "check", Arrays.<Type>asList(i,
                codec.getType()), VoidType.v(), Modifier.STATIC);
        Local key = local(check, "i0", i);
        Local held = local(check, "r0", codec.getType());
        Value[] read = {
                Jimple.v().newStaticInvokeExpr(encodeKey.makeRef(), key),
                Jimple.v().newStaticInvokeExpr(recordKey.makeRef(), key),
                Jimple.v().newStaticFieldRef(last.makeRef()),
                Jimple.v().newStaticInvokeExpr(codeKey.makeRef(), held, key),
                Jimple.v().newStaticFieldRef(logged.makeRef()),
                Jimple.v().newStaticInvokeExpr(downKey.makeRef(), key),
                Jimple.v().newStaticInvokeExpr(parityKey.makeRef(), key)};
        List<Unit> units = new ArrayList<>(Arrays.asList(
                Jimple.v().newIdentityStmt(key,
                        Jimple.v().newParameterRef(i, 0)),
                Jimple.v().newIdentityStmt(held,
                        Jimple.v().newParameterRef(codec.getType(), 1))));
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
                new ExceptionTargetSite("t", PB, "check", "(ILm/Codec;)V",
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
        method.getActiveBody().getUnits().addAll(Arrays.asList(units));
    }
}
