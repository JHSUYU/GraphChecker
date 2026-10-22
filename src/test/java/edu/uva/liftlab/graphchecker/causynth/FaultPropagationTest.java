package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
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

    @Test
    public void aWriteAHandlerCallsIsGuardedByTheBranchDecidingTheCaughtThrow() {
        JimpleScene.load(JimpleScene.OBJECT, THROWABLE, EXCEPTION,
                ioe("f.Missing", "java.lang.Exception"),
                "application public class f.Header extends java.lang.Object {"
                        + " int type; public void <init>(int) { f.Header r0;"
                        + " int i0; r0 := @this: f.Header; i0 := @parameter0:"
                        + " int; r0.<f.Header: int type> = i0; return; } }",
                "application public class f.Lookup extends java.lang.Object {"
                        + " java.lang.Object held; public void find("
                        + "java.lang.Object) { f.Lookup r0; java.lang.Object r1,"
                        + " r3; f.Missing $r2; r0 := @this: f.Lookup;"
                        + " r1 := @parameter0: java.lang.Object;"
                        + " r3 = r0.<f.Lookup: java.lang.Object held>;"
                        + " if r1 == null goto label0; r3 = r1; label0:"
                        + " if r3 != null goto label1; $r2 = new f.Missing;"
                        + " specialinvoke $r2.<f.Missing: void <init>("
                        + "java.lang.String)>(\"none\"); throw $r2;"
                        + " label1: return; } }",
                "application public class f.Prep extends java.lang.Object {"
                        + " f.Header hdr; public void step(f.Lookup,"
                        + " java.lang.Object) { f.Prep r0; f.Lookup r1;"
                        + " java.lang.Object r2; f.Missing $r3; f.Header $r4;"
                        + " r0 := @this: f.Prep; r1 := @parameter0: f.Lookup;"
                        + " r2 := @parameter1: java.lang.Object; label1:"
                        + " virtualinvoke r1.<f.Lookup: void find("
                        + "java.lang.Object)>(r2); label2: return;"
                        + " label3: $r3 := @caughtexception; $r4 = new f.Header;"
                        + " specialinvoke $r4.<f.Header: void <init>(int)>(-1);"
                        + " r0.<f.Prep: f.Header hdr> = $r4; return;"
                        + " catch f.Missing from label1 to label2 with label3;"
                        + " }"
                        + " public void plain(java.lang.Object) { f.Prep r0;"
                        + " f.Header $r4; r0 := @this: f.Prep;"
                        + " $r4 = new f.Header; specialinvoke $r4.<f.Header:"
                        + " void <init>(int)>(1); return; } }");
        String write = "<f.Header: void <init>(int)>#u3";
        String handled = "<f.Prep: void step(f.Lookup,java.lang.Object)>#u8";
        StaticScopeMap.Guards guards = SiteControlDependence.over(
                java.util.Arrays.asList(write, handled));
        Object[][] rows = {
            {"the constructor a handler calls: the throw's deciding arm,"
                    + " and the branch choosing the value that arm tests",
                "[<f.Lookup: void find(java.lang.Object)>#u5=false,"
                        + " <f.Lookup: void find(java.lang.Object)>#u3=false]",
                guards.caughtInto(write).toString()},
            {"a store in the handler itself, the same",
                "[<f.Lookup: void find(java.lang.Object)>#u5=false,"
                        + " <f.Lookup: void find(java.lang.Object)>#u3=false]",
                guards.caughtInto(handled).toString()},
            {"the try's own call is no handler's: nothing",
                "[]", guards.caughtInto(
                        "<f.Prep: void step(f.Lookup,java.lang.Object)>#u3")
                        .toString()}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

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
