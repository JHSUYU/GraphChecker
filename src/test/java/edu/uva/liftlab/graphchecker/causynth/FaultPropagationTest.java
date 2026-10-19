package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Test;
import soot.G;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Local;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * SYMBOL-SCOPE §2.2: where a door fault goes -- to the handler catching it
 * (a guard with no boolean arm), out of a method, through a rethrow, back
 * from a proxy call.
 */
public class FaultPropagationTest {
    private static final String IOE = "java.io.IOException";
    private static final String SEND = "<f.Door: void send()>";
    private static final String THROWABLE = "public class java.lang.Throwable"
            + " extends java.lang.Object { }";
    private static final String EXCEPTION = "public class java.lang.Exception"
            + " extends java.lang.Throwable { }";
    private static final String DEBUG_CLASS =
            "edu.uva.liftlab.graphchecker.annotation.Debug";
    private static final String DEBUG = "public class " + DEBUG_CLASS
            + " extends java.lang.Object { public static native boolean"
            + " makeSymbolicBoolean(java.lang.String); }";

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

    /** An exception class built with a message. */
    private static String ioe(String name, String parent) {
        return "public class " + name + " extends " + parent
                + " { public void <init>(java.lang.String) { } }";
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
     * serves ({@code use}).
     */
    private static Scene scene() {
        String send = "virtualinvoke r1." + SEND + "();";
        JimpleScene.load(JimpleScene.OBJECT, THROWABLE, EXCEPTION,
                ioe(IOE, "java.lang.Exception"), DEBUG,
                "public abstract interface java.lang.reflect"
                        + ".InvocationHandler { }",
                "application public class f.Door extends java.lang.Object {"
                        + " public void send() { f.Door r0; boolean $z0; " + IOE
                        + " $r1; r0 := @this: f.Door; $z0 = staticinvoke <"
                        + DEBUG_CLASS + ": boolean makeSymbolicBoolean("
                        + "java.lang.String)>(\"FAULT:HADOOP_IPC:REQUEST\");"
                        + " if $z0 == 0 goto label1; $r1 = new " + IOE + ";"
                        + " specialinvoke $r1.<" + IOE + ": void <init>("
                        + "java.lang.String)>(\"symbolic\"); throw $r1;"
                        + " label1: return; } }",
                "application public abstract interface f.Proto {"
                        + " public abstract void op() throws " + IOE + "; }",
                "application public class f.Handler extends java.lang.Object"
                        + " implements java.lang.reflect.InvocationHandler {"
                        + " public java.lang.Object invoke(java.lang.Object,"
                        + " java.lang.Object, java.lang.Object) { f.Door r1;"
                        + " r1 = new f.Door; " + send + " return r1; } }",
                "application public class f.Caller extends java.lang.Object {"
                        + " int ok; public void call(f.Door) { f.Caller r0;"
                        + " f.Door r1; " + IOE + " $r2; r0 := @this: f.Caller;"
                        + " r1 := @parameter0: f.Door; label1: " + send
                        + " r0.<f.Caller: int ok> = 1; label2: return;"
                        + " label3: $r2 := @caughtexception;"
                        + " r0.<f.Caller: int ok> = 0; return; catch " + IOE
                        + " from label1 to label2 with label3; }"
                        + " public void relay(f.Door) { f.Door r1;"
                        + " java.lang.Throwable $r2, $r3;"
                        + " r1 := @parameter0: f.Door; label1: " + send
                        + " label2: return; label3: $r2 := @caughtexception;"
                        + " $r3 = $r2; throw $r3; catch java.lang.Throwable"
                        + " from label1 to label2 with label3; }"
                        + " public void use(f.Proto) { f.Caller r0;"
                        + " f.Proto r1; r0 := @this: f.Caller;"
                        + " r1 := @parameter0: f.Proto;"
                        + " interfaceinvoke r1.<f.Proto: void op()>(); return;"
                        + " } }");
        return Scene.v();
    }
}
