package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
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

import java.io.File;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §2.2: where a door fault goes -- to the handler catching it
 * (a guard with no boolean arm), out of a method, through a rethrow, back
 * from a proxy call -- and when a library call's result depends on its
 * receiver.
 */
public class FaultPropagationTest {
    private static final String IOE = "java.io.IOException";
    private static final String SEND = "<f.Door: void send()>";
    private static final Jimple J = Jimple.v();

    @Rule
    public final TemporaryFolder roots = new TemporaryFolder();

    @After
    public void resetSoot() {
        G.reset();
    }

    @Test
    public void aDoorFaultGoesToItsHandlerOrOut() {
        Scene scene = scene();
        FaultPropagation faults = FaultPropagation.current();
        SootMethod call = scene.getMethod("<f.Caller: void call(f.Door)>");
        List<Unit> units = new ArrayList<>(call.getActiveBody().getUnits());
        Unit send = units.get(2);
        Unit handler = units.get(5);
        SootMethod relay = scene.getMethod("<f.Caller: void relay(f.Door)>");
        SootMethod use = scene.getMethod("<f.Caller: void use(f.Proto)>");
        Object[][] rows = {
            {"the door's woven throw escapes it, from its marker", "[$z0]",
                markers(faults.escapes(SEND))},
            {"the caller's handler catches it",
                Collections.singleton(handler), faults.handlers(
                        call.getSignature(), send)},
            {"whose call is its origin", "[" + SEND + ".throws]",
                faults.raise(call.getSignature(), send).callees.toString()},
            {"nothing escapes the caller", 0,
                faults.escapes(call.getSignature()).size()},
            {"a finally block's rethrow lets it out, with its origin",
                "[" + SEND + ".throws]", origins(faults.escapes(
                        relay.getSignature()))},
            {"a proxy call raises what the handler's calls reach",
                "[" + SEND + ".throws]", origins(Collections.singleton(
                        faults.raise(use.getSignature(), new ArrayList<>(
                                use.getActiveBody().getUnits()).get(2))))},
            {"the store after the call is decided by the call, on no arm",
                "[<f.Caller: void call(f.Door)>#u2=null]",
                SiteControlDependence.MethodGuards.of(call.getSignature())
                        .at(3).toString()}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    @Test
    public void aLibraryCallReadsItsReceiverWhenItIsShared() throws Exception {
        scene();
        File system = roots.newFolder("classes");
        Files.createDirectories(system.toPath().resolve("f"));
        Files.createFile(system.toPath().resolve("f/Caller.class"));
        String both = system + File.pathSeparator + roots.newFolder("other");
        SootMethod read = Scene.v().getMethod("<f.Caller: void read()>");
        List<Unit> units = new ArrayList<>(read.getActiveBody().getUnits());
        List<Local> locals = new ArrayList<>(read.getActiveBody().getLocals());
        Object[][] rows = {
            {"a field's object, through a cast", true,
                LibraryReceivers.shared(units, 4, locals.get(2), c -> false)},
            {"an object the method allocated", false,
                LibraryReceivers.shared(units, 7, locals.get(3), c -> false)},
            {"a configuration", true,
                LibraryReceivers.stateful("f.Conf", "getBoolean")},
            {"a logger", false,
                LibraryReceivers.stateful("org.slf4j.Logger", "isDebugEnabled")},
            {"a metrics registry", false,
                LibraryReceivers.stateful("a.metrics2.Registry", "get")},
            {"an identity method", false,
                LibraryReceivers.stateful("f.Conf", "hashCode")},
            {"a class of the system's own roots is no library", true,
                LibraryReceivers.systemClasses(both).test("f.Caller")},
            {"a class no root holds is one", false,
                LibraryReceivers.systemClasses(both).test("f.Conf")},
            {"with no roots, every class is one", false,
                LibraryReceivers.systemClasses(null).test("f.Caller")}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    private static String markers(java.util.Collection<FaultPropagation.Raise>
                                          raises) {
        List<String> found = new ArrayList<>();
        for (FaultPropagation.Raise raise : raises) {
            for (Local marker : raise.markers) found.add(marker.getName());
        }
        return found.toString();
    }

    private static String origins(java.util.Collection<FaultPropagation.Raise>
                                          raises) {
        List<String> found = new ArrayList<>();
        for (FaultPropagation.Raise raise : raises) found.addAll(raise.callees);
        return found.toString();
    }

    /**
     * {@code f.Door.send()} is woven with an IPC door fault; {@code
     * f.Caller} calls it under an IOException handler ({@code call}), under
     * a finally block ({@code relay}), through a proxied interface a handler
     * serves ({@code use}), and reads a configuration ({@code read}).
     */
    private static Scene scene() {
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        SootClass throwable = library("java.lang.Throwable", object, 0);
        SootClass exception = library("java.lang.Exception", throwable, 0);
        SootClass ioe = library(IOE, exception, 0);
        method(ioe, "<init>", Collections.<Type>singletonList(
                RefType.v("java.lang.String")), VoidType.v(), 0);
        SootClass debug = library(
                "edu.uva.liftlab.graphchecker.annotation.Debug", object, 0);
        SootMethod marker = method(debug, "makeSymbolicBoolean",
                Collections.<Type>singletonList(RefType.v("java.lang.String")),
                BooleanType.v(), Modifier.STATIC | Modifier.NATIVE);
        SootClass handlerType = library("java.lang.reflect.InvocationHandler",
                null, Modifier.INTERFACE | Modifier.ABSTRACT);

        SootClass door = application("f.Door", object);
        SootMethod send = method(door, "send",
                Collections.<Type>emptyList(), VoidType.v(), 0);
        Local d0 = local(send, "r0", door.getType());
        Local chosen = local(send, "$z0", BooleanType.v());
        Local thrown = local(send, "$r1", ioe.getType());
        Unit done = J.newReturnVoidStmt();
        body(send, J.newIdentityStmt(d0, J.newThisRef(door.getType())),
                J.newAssignStmt(chosen, J.newStaticInvokeExpr(
                        marker.makeRef(),
                        StringConstant.v("FAULT:HADOOP_IPC:REQUEST"))),
                J.newIfStmt(J.newEqExpr(chosen, IntConstant.v(0)), done),
                J.newAssignStmt(thrown, J.newNewExpr(ioe.getType())),
                J.newInvokeStmt(J.newSpecialInvokeExpr(thrown, ioe
                        .getMethodByName("<init>").makeRef(),
                        StringConstant.v("symbolic"))),
                J.newThrowStmt(thrown), done);

        SootClass proto = application("f.Proto", null);
        proto.setModifiers(Modifier.PUBLIC | Modifier.INTERFACE
                | Modifier.ABSTRACT);
        SootMethod op = method(proto, "op", Collections.<Type>emptyList(),
                VoidType.v(), Modifier.ABSTRACT);
        op.addException(ioe);
        SootClass served = application("f.Handler", object);
        served.addInterface(handlerType);
        SootMethod invoke = method(served, "invoke", Arrays.<Type>asList(
                object.getType(), object.getType(), object.getType()),
                object.getType(), 0);
        Local h1 = local(invoke, "r1", door.getType());
        body(invoke, J.newAssignStmt(h1, J.newNewExpr(door.getType())),
                J.newInvokeStmt(J.newVirtualInvokeExpr(h1, send.makeRef())),
                J.newReturnStmt(h1));

        SootClass conf = library("f.Conf", object, 0);
        SootMethod flag = method(conf, "getBoolean",
                Collections.<Type>emptyList(), BooleanType.v(), 0);
        SootClass caller = application("f.Caller", object);
        SootField ok = new SootField("ok", IntType.v(), 0);
        SootField held = new SootField("conf", object.getType(), 0);
        caller.addField(ok);
        caller.addField(held);
        RefType self = caller.getType();

        SootMethod call = method(caller, "call",
                Collections.<Type>singletonList(door.getType()),
                VoidType.v(), 0);
        Local c0 = local(call, "r0", self);
        Local c1 = local(call, "r1", door.getType());
        Local caught = local(call, "$r2", ioe.getType());
        Unit sent = J.newInvokeStmt(J.newVirtualInvokeExpr(c1,
                send.makeRef()));
        Unit stored = J.newAssignStmt(J.newInstanceFieldRef(c0,
                ok.makeRef()), IntConstant.v(1));
        Unit left = J.newReturnVoidStmt();
        Unit handler = J.newIdentityStmt(caught,
                J.newCaughtExceptionRef());
        body(call, J.newIdentityStmt(c0, J.newThisRef(self)),
                J.newIdentityStmt(c1, J.newParameterRef(door.getType(), 0)),
                sent, stored, left, handler,
                J.newAssignStmt(J.newInstanceFieldRef(c0, ok.makeRef()),
                        IntConstant.v(0)), J.newReturnVoidStmt());
        call.getActiveBody().getTraps().add(J.newTrap(ioe, sent, left,
                handler));

        SootMethod relay = method(caller, "relay",
                Collections.<Type>singletonList(door.getType()),
                VoidType.v(), 0);
        Local r1 = local(relay, "r1", door.getType());
        Local any = local(relay, "$r2", throwable.getType());
        Local copy = local(relay, "$r3", throwable.getType());
        Unit relayed = J.newInvokeStmt(J.newVirtualInvokeExpr(r1,
                send.makeRef()));
        Unit relayEnd = J.newReturnVoidStmt();
        Unit relayHandler = J.newIdentityStmt(any, J.newCaughtExceptionRef());
        body(relay, J.newIdentityStmt(r1,
                        J.newParameterRef(door.getType(), 0)),
                relayed, relayEnd, relayHandler,
                J.newAssignStmt(copy, any), J.newThrowStmt(copy));
        relay.getActiveBody().getTraps().add(J.newTrap(throwable, relayed,
                relayEnd, relayHandler));

        SootMethod use = method(caller, "use",
                Collections.<Type>singletonList(proto.getType()),
                VoidType.v(), 0);
        Local u0 = local(use, "r0", self);
        Local u1 = local(use, "r1", proto.getType());
        body(use, J.newIdentityStmt(u0, J.newThisRef(self)),
                J.newIdentityStmt(u1, J.newParameterRef(proto.getType(), 0)),
                J.newInvokeStmt(J.newInterfaceInvokeExpr(u1, op.makeRef())),
                J.newReturnVoidStmt());

        SootMethod read = method(caller, "read",
                Collections.<Type>emptyList(), VoidType.v(), 0);
        Local e0 = local(read, "r0", self);
        Local field = local(read, "$r1", object.getType());
        Local cast = local(read, "$r2", conf.getType());
        Local fresh = local(read, "$r3", conf.getType());
        Local answer = local(read, "$z0", BooleanType.v());
        body(read, J.newIdentityStmt(e0, J.newThisRef(self)),
                J.newAssignStmt(field, J.newInstanceFieldRef(e0,
                        held.makeRef())),
                J.newAssignStmt(cast, J.newCastExpr(field, conf.getType())),
                J.newNopStmt(),
                J.newAssignStmt(answer, J.newVirtualInvokeExpr(cast,
                        flag.makeRef())),
                J.newAssignStmt(fresh, J.newNewExpr(conf.getType())),
                J.newNopStmt(),
                J.newAssignStmt(answer, J.newVirtualInvokeExpr(fresh,
                        flag.makeRef())),
                J.newReturnVoidStmt());
        return Scene.v();
    }

    private static SootClass application(String name, SootClass parent) {
        SootClass type = library(name, parent, 0);
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
        if ((modifiers & (Modifier.ABSTRACT | Modifier.NATIVE)) == 0) {
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
