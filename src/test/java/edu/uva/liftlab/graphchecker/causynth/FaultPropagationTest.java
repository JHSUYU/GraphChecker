package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Test;
import soot.G;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Local;

import java.util.ArrayList;
import java.util.Arrays;
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
    private static final String ZK =
            "org.apache.solr.common.cloud.SolrZooKeeper";
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

    /**
     * SYMBOL-SCOPE §4.2: a door at calls (the catalog's DataTransfer
     * responses) is woven after the anchor in each analysed caller, its
     * kinds in row order, its units tagged as the weave's, and goes to that
     * caller's handler, which its marker branches decide; a library caller
     * is not woven.
     */
    @Test
    public void aDoorAtCallsIsWovenInEveryAnalysedCaller() {
        String ack = "org.apache.hadoop.hdfs.protocol.datatransfer"
                + ".PipelineAck";
        JimpleScene.load(JimpleScene.OBJECT, THROWABLE, EXCEPTION,
                ioe(IOE, "java.lang.Exception"),
                ioe("java.io.EOFException", IOE),
                ioe("java.net.SocketTimeoutException", IOE),
                "public class java.io.InputStream extends java.lang.Object"
                        + " { }",
                "public class " + ack + " extends java.lang.Object {"
                        + " public native void readFields("
                        + "java.io.InputStream); }",
                "application " + reader("g.Reader", ack),
                reader("g.Library", ack));
        SootMethod analysed = Scene.v().getMethod("<g.Reader: void read("
                + ack + ",java.io.InputStream)>");
        SootMethod unanalysed = Scene.v().getMethod("<g.Library: void read("
                + ack + ",java.io.InputStream)>");

        DoorWeave.apply();
        List<String> names = new ArrayList<>();
        Unit handler = null;
        List<Unit> throwsAt = new ArrayList<>();
        int program = 0;
        for (Unit unit : analysed.getActiveBody().getUnits()) {
            if (!DoorWeave.isWoven(unit)) program++;
            DoorWeave.Fault woven = DoorWeave.woven(analysed.getActiveBody(),
                    unit);
            if (woven != null) {
                names.add(woven.name);
                throwsAt.add(unit);
            }
            if (unit instanceof soot.jimple.IdentityStmt && ((soot.jimple
                    .IdentityStmt) unit).getRightOp()
                    instanceof soot.jimple.CaughtExceptionRef) {
                handler = unit;
            }
        }
        FaultPropagation faults = FaultPropagation.current();
        Object[][] rows = {
            {"the caller's markers, in the row's order",
                "[FAULT:HDFS_DATA_TRANSFER:RESPONSE, "
                        + "FAULT:HDFS_DATA_TRANSFER:RESPONSE:EOFException, "
                        + "FAULT:HDFS_DATA_TRANSFER:RESPONSE:"
                        + "SocketTimeoutException]", names.toString()},
            {"each goes to the caller's handler",
                Collections.nCopies(3, Collections.singleton(handler))
                        .toString(), handlersOf(faults,
                        analysed.getSignature(), throwsAt)},
            {"the handler's store is decided by each marker branch, on "
                    + "its throwing arm", "[" + analysed.getSignature()
                    + "#u5=false, " + analysed.getSignature()
                    + "#u10=false, " + analysed.getSignature()
                    + "#u15=false]", SiteControlDependence.MethodGuards.of(
                            analysed.getSignature()).at(22).toString()},
            {"the weave's units are its own, not the program's", "9 of 24",
                program + " of " + analysed.getActiveBody().getUnits()
                        .size()},
            {"a library caller is not woven", 9,
                unanalysed.getActiveBody().getUnits().size()}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * SYMBOL-SCOPE §4.2: a door a system's hook moved (Solr's ZooKeeper
     * create, woven in {@code SolrZkClient#create} after its store hook) is
     * also a door at every other direct call of the door method in that
     * class family -- through a subclass's reference, in a retry lambda --
     * after the hook call the door call reaches by control flow, its markers
     * woven right after that call: a makePath creating its nodes itself
     * would have none.
     * A call no hook call follows (create's own retry lambda, whose hook its
     * caller makes) or one outside the family carries none, and is named.
     */
    @Test
    public void aMovedDoorIsADoorAtEveryOtherCallItsHookFollows()
            throws Exception {
        String client = "org.apache.solr.common.cloud.SolrZkClient";
        String hookSig = "<" + client + ": java.lang.String create("
                + "java.lang.String,byte[],org.apache.zookeeper.CreateMode,"
                + "boolean)>";
        JimpleScene.load(JimpleScene.OBJECT, THROWABLE, EXCEPTION,
                keeper("ConnectionLossException"),
                keeper("SessionExpiredException"),
                "public class org.apache.zookeeper.ZooKeeper extends"
                        + " java.lang.Object { public native java.lang.String"
                        + " create(java.lang.String, byte[], java.util.List,"
                        + " org.apache.zookeeper.CreateMode); }",
                "public class " + ZK + " extends"
                        + " org.apache.zookeeper.ZooKeeper { }",
                "application public class " + client + " extends"
                        + " java.lang.Object { public static native void"
                        + " causynthWrote(java.lang.String, int, byte[]);"
                        + writer("java.lang.String create(java.lang.String,"
                        + " byte[], org.apache.zookeeper.CreateMode,"
                        + " boolean)", 1, true)
                        + writer("void lambda$create$1(java.lang.String)", 1,
                        false)
                        + writer("void makePath(java.lang.String)", 1, true)
                        + writer("void lambda$makePath$0(java.lang.String)",
                        1, true)
                        + writer("void createTwo(java.lang.String)", 2, true)
                        + writer("void delete(java.lang.String)", 0, true)
                        + " }",
                "application public class org.apache.solr.cloud.Other extends"
                        + " java.lang.Object {"
                        + writer("void write(java.lang.String)", 1, true)
                        + " }");
        SootMethod wrote = Scene.v().getMethod("<" + client + ": void"
                + " causynthWrote(java.lang.String,int,byte[])>");
        SootMethod hook = Scene.v().getMethod(hookSig);
        SootMethod retried = zk(client, "lambda$create$1");
        SootMethod makePath = zk(client, "makePath");
        SootMethod lambda = zk(client, "lambda$makePath$0");
        SootMethod twice = zk(client, "createTwo");
        SootMethod hookOnly = zk(client, "delete");
        SootMethod outside = zk("org.apache.solr.cloud.Other", "write");
        List<LibraryCatalog.Hook> hooks;
        try (java.io.BufferedReader reader = java.nio.file.Files
                .newBufferedReader(java.nio.file.Paths.get("experiments",
                        "solr", "doors.jsonl"))) {
            hooks = LibraryCatalog.hooks(LibraryCatalog.rows(reader,
                    "doors.jsonl"));
        }
        LibraryCatalog.Door door = null;
        for (LibraryCatalog.Door each : LibraryCatalog.placed(
                LibraryCatalog.doors(), hooks)) {
            if (hook.getSignature().equals(each.method)) door = each;
        }
        List<SootClass> analysed = new ArrayList<>(
                Scene.v().getApplicationClasses());
        analysed.sort((a, b) -> a.getName().compareTo(b.getName()));
        int named = DoorWeave.unplaced().size();
        java.util.Map<SootMethod, java.util.Set<soot.jimple.Stmt>> calls =
                DoorWeave.moved(door, analysed);
        List<String> unplaced = new ArrayList<>();
        for (java.util.Map<String, Object> row : DoorWeave.unplaced()
                .subList(named, DoorWeave.unplaced().size())) {
            unplaced.add(String.valueOf(row.get(
                    CommunicationCatalogContract.GAP_METHOD)));
        }
        Unit hooked = hookCall(makePath, wrote, 0);
        DoorWeave.weaveMoved(door, analysed);
        List<String> after = new ArrayList<>();
        for (Unit unit : makePath.getActiveBody().getUnits()) {
            DoorWeave.Fault fault = DoorWeave.woven(
                    makePath.getActiveBody(), unit);
            if (fault != null) after.add(fault.name);
        }
        Object[][] rows = {
            {"the create door was moved to the hook method",
                "<org.apache.zookeeper.ZooKeeper: java.lang.String create("
                        + "java.lang.String,byte[],java.util.List,"
                        + "org.apache.zookeeper.CreateMode)>",
                door.relocated},
            {"every other method of the family a create reaches a hook in",
                Arrays.asList(twice, lambda, makePath).toString(),
                new ArrayList<>(calls.keySet()).toString()},
            {"makePath's hook call", "[" + hooked + "]",
                calls.get(makePath).toString()},
            {"each of two creates its own",
                "[" + hookCall(twice, wrote, 0) + ", "
                        + hookCall(twice, wrote, 1) + "]",
                calls.get(twice).toString()},
            {"a hook call no door call precedes, none", false,
                calls.containsKey(hookOnly)},
            {"a create no hook call follows, or outside the family: named",
                Arrays.asList(outside.getSignature(),
                        retried.getSignature()).toString(),
                unplaced.toString()},
            {"the woven markers, the catalog's kinds in order",
                "[FAULT:ZOOKEEPER:WRITE:KeeperException$ConnectionLoss"
                        + "Exception, FAULT:ZOOKEEPER:WRITE:KeeperException$"
                        + "SessionExpiredException]",
                after.toString()},
            {"right after the hook call", true, DoorWeave.isWoven(
                makePath.getActiveBody().getUnits().getSuccOf(hooked))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** A static method of that declaration making {@code creates} creates
     *  through the SolrZooKeeper its {@code r1} holds, each followed by its
     *  store hook when {@code hooked}; with none, the hook alone. */
    private static String writer(String declaration, int creates,
                                 boolean hooked) {
        StringBuilder body = new StringBuilder(" public static "
                + declaration + " { java.lang.String r0; " + ZK + " r1;"
                + " r0 := @parameter0: java.lang.String; r1 = null;");
        for (int write = 0; write < Math.max(1, creates); write++) {
            if (creates > 0) {
                body.append(" virtualinvoke r1.<" + ZK + ": java.lang.String"
                        + " create(java.lang.String,byte[],java.util.List,"
                        + "org.apache.zookeeper.CreateMode)>(r0, null, null,"
                        + " null);");
            }
            if (hooked) {
                body.append(" staticinvoke <org.apache.solr.common.cloud"
                        + ".SolrZkClient: void causynthWrote(java.lang.String,"
                        + "int,byte[])>(r0, 0, null);");
            }
        }
        return body.append(declaration.startsWith("void") ? " return; }"
                : " return null; }").toString();
    }

    /** The one-path method {@code name} of {@code owner}. */
    private static SootMethod zk(String owner, String name) {
        return Scene.v().getMethod("<" + owner + ": void " + name
                + "(java.lang.String)>");
    }

    /** A KeeperException kind, built with no message. */
    private static String keeper(String kind) {
        return "public class org.apache.zookeeper.KeeperException$" + kind
                + " extends java.lang.Exception { public void <init>() { } }";
    }

    /** An exception class built with a message. */
    private static String ioe(String name, String parent) {
        return "public class " + name + " extends " + parent
                + " { public void <init>(java.lang.String) { } }";
    }

    /** The {@code ordinal}-th call of {@code hook} in {@code method}. */
    private static Unit hookCall(SootMethod method, SootMethod hook,
                                 int ordinal) {
        return DoorWeave.call(method.getActiveBody(), hook.getSignature(),
                ordinal);
    }

    /**
     * SYMBOL-SCOPE §4.2, §4.6: a demanded door is latent until the root
     * demand chooses its call -- a file open's kind, a throw on a failing
     * rename's arm, a call into the system outside the scope declaring a
     * checked exception -- and is then woven at that call alone, before
     * it, and raises from its marker, a failing result as the call's own
     * type (a timed wait's {@code awaitNanos} returns {@code 0L}); a door
     * asked again at a call that holds one is refused by name.
     */
    @Test
    public void aDemandedDoorStandsOnlyAtTheCallChosenForIt()
            throws Exception {
        String open = "<java.io.FileOutputStream: void <init>(java.io.File)>";
        String rename = "<java.io.File: boolean renameTo(java.io.File)>";
        String await = "<java.util.concurrent.locks.Condition: long "
                + "awaitNanos(long)>";
        SootMethod save = store();
        String method = save.getSignature();
        FaultPropagation latent = FaultPropagation.latent(
                owner -> owner.startsWith("g."));
        List<String> latentAt = new ArrayList<>();
        for (FaultPropagation.Raise raise : latent.escapes(method)) {
            if (raise.latent != null) {
                latentAt.add(raise.latent.getInvokeExpr().getMethodRef()
                        .getSignature());
            }
            if (raise.frontier != null) latentAt.add(raise.frontier);
        }
        java.nio.file.Path doors = java.nio.file.Files.createTempFile(
                "io_doors", ".jsonl");
        DemandedDoors.write(doors, Arrays.asList(
                new DemandedDoors.Site(method, open, 0, 2, "ESCAPE",
                        Collections.singletonList(method)),
                new DemandedDoors.Site(method, rename, 0, 2, "ESCAPE",
                        Collections.singletonList(method)),
                new DemandedDoors.Site(method, await, 0, 2, "VALUE",
                        Collections.singletonList(method))));
        System.setProperty(DemandedDoors.PROPERTY, doors.toString());
        String refused = "";
        try {
            DoorWeave.apply();
            try {
                DoorWeave.apply();
            } catch (IllegalStateException again) {
                refused = again.getMessage().split(":")[0];
            }
        } finally {
            System.clearProperty(DemandedDoors.PROPERTY);
            java.nio.file.Files.delete(doors);
        }
        List<String> woven = new ArrayList<>();
        List<String> guards = new ArrayList<>();
        int calls = 0;
        for (Unit unit : save.getActiveBody().getUnits()) {
            if (unit instanceof soot.jimple.Stmt
                    && ((soot.jimple.Stmt) unit).containsInvokeExpr()
                    && ((soot.jimple.Stmt) unit).getInvokeExpr()
                    .getMethodRef().getName().equals("timesOut")) {
                guards.add(((soot.jimple.Stmt) unit).getInvokeExpr()
                        .getArgs().toString());
            }
            DoorWeave.Fault thrown = DoorWeave.woven(save.getActiveBody(),
                    unit);
            DoorWeave.Fault failing = DoorWeave.wovenResult(
                    save.getActiveBody(), unit);
            if (thrown != null) woven.add(thrown.name);
            if (failing != null) {
                Unit value = save.getActiveBody().getUnits().getPredOf(
                        save.getActiveBody().getUnits().getPredOf(unit));
                woven.add(failing.name + " -> " + ((soot.jimple.AssignStmt)
                        value).getRightOp());
            }
            if (unit instanceof soot.jimple.Stmt
                    && ((soot.jimple.Stmt) unit).containsInvokeExpr()) {
                String callee = ((soot.jimple.Stmt) unit).getInvokeExpr()
                        .getMethodRef().getSignature();
                if (callee.equals(open) || callee.equals(rename)) calls++;
            }
        }
        Object[][] rows = {
            {"latent: the open, the throw on the rename's failing arm, the "
                    + "system call outside the scope",
                Arrays.asList(open, rename, "<g.Lib: void flush()>"),
                latentAt},
            {"woven at the chosen calls, the program's calls kept",
                "[FAULT:LOCAL_IO:OPEN:FileNotFoundException, "
                        + "FAULT:LOCAL_IO:NAMESPACE -> 0, "
                        + "FAULT:TIMED_WAIT:AWAIT -> 0L] 2",
                woven + " " + calls},
            {"a timed wait's planted timeout guarded by its receiver, the "
                    + "permits and the marker; a file operation's not",
                "[[$r5, 1, \"FAULT:TIMED_WAIT:AWAIT\"]]", guards.toString()},
            {"both escape from their markers",
                2, markers(FaultPropagation.current().escapes(method))
                        .split(",").length},
            {"a call holding a door is refused", "DEMANDED_DOOR_UNAVAILABLE",
                refused}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /**
     * {@code g.Store.save(File f, File g)}: opens {@code f} for writing,
     * renames it to {@code g} and throws when that fails, flushes through
     * the system's {@code g.Lib} (outside the scope), waits on a condition
     * ({@code awaitNanos}, a timed wait's door), then stores {@code ok}.
     */
    private static SootMethod store() {
        JimpleScene.load(JimpleScene.OBJECT, THROWABLE, EXCEPTION,
                "public class java.lang.RuntimeException extends"
                        + " java.lang.Exception { }",
                ioe(IOE, "java.lang.Exception"),
                ioe("java.io.FileNotFoundException", IOE), DEBUG,
                "public class java.io.File extends java.lang.Object {"
                        + " public native boolean renameTo(java.io.File); }",
                "public class java.io.FileOutputStream extends"
                        + " java.lang.Object { public native void <init>("
                        + "java.io.File); }",
                "public interface java.util.concurrent.locks.Condition"
                        + " extends java.lang.Object { public abstract long"
                        + " awaitNanos(long); }",
                "public class g.Lib extends java.lang.Object { public static"
                        + " native void flush() throws " + IOE + "; }",
                "application public class g.Store extends java.lang.Object {"
                        + " int ok; public void save(java.io.File,"
                        + " java.io.File) { g.Store r0; java.io.File r1, r2;"
                        + " java.io.FileOutputStream $r3; boolean $z0; " + IOE
                        + " $r4; java.util.concurrent.locks.Condition $r5;"
                        + " long $l0; r0 := @this: g.Store;"
                        + " r1 := @parameter0: java.io.File;"
                        + " r2 := @parameter1: java.io.File;"
                        + " $r3 = new java.io.FileOutputStream;"
                        + " specialinvoke $r3.<java.io.FileOutputStream: void"
                        + " <init>(java.io.File)>(r1); $z0 = virtualinvoke"
                        + " r1.<java.io.File: boolean renameTo(java.io.File)>"
                        + "(r2); if $z0 != 0 goto label1; $r4 = new " + IOE
                        + "; specialinvoke $r4.<" + IOE + ": void <init>("
                        + "java.lang.String)>(\"rename\"); throw $r4;"
                        + " label1: staticinvoke <g.Lib: void flush()>();"
                        + " $r5 = null; $l0 = interfaceinvoke $r5.<java.util"
                        + ".concurrent.locks.Condition: long awaitNanos(long)>"
                        + "(5L); r0.<g.Store: int ok> = 1; return; } }");
        return Scene.v().getMethod("<g.Store: void save(java.io.File,"
                + "java.io.File)>");
    }

    private static String handlersOf(FaultPropagation faults, String method,
                                     List<Unit> raises) {
        List<Object> found = new ArrayList<>();
        for (Unit raise : raises) found.add(faults.handlers(method, raise));
        return found.toString();
    }

    /** {@code void read(PipelineAck, InputStream)} of {@code owner}:
     *  {@code readFields} under an IOException handler, a store on each
     *  arm. */
    private static String reader(String owner, String ack) {
        return "public class " + owner + " extends java.lang.Object {"
                + " int ok; public void read(" + ack + ", java.io.InputStream)"
                + " { " + owner + " r0; " + ack + " r1; java.io.InputStream r2;"
                + " " + IOE + " $r3; r0 := @this: " + owner + ";"
                + " r1 := @parameter0: " + ack + ";"
                + " r2 := @parameter1: java.io.InputStream;"
                + " label1: virtualinvoke r1.<" + ack + ": void readFields("
                + "java.io.InputStream)>(r2); r0.<" + owner + ": int ok> = 1;"
                + " label2: return; label3: $r3 := @caughtexception;"
                + " r0.<" + owner + ": int ok> = 0; return;"
                + " catch " + IOE + " from label1 to label2 with label3; } }";
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
