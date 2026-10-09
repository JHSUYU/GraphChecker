package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.plan.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Test;
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
    private static final Jimple J = Jimple.v();

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
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        SootClass throwable = library("java.lang.Throwable", object, 0);
        SootClass exception = library("java.lang.Exception", throwable, 0);
        SootClass ioe = library(IOE, exception, 0);
        for (SootClass kind : new SootClass[]{ioe,
                library("java.io.EOFException", ioe, 0),
                library("java.net.SocketTimeoutException", ioe, 0)}) {
            method(kind, "<init>", Collections.<Type>singletonList(
                    RefType.v("java.lang.String")), VoidType.v(), 0);
        }
        SootClass stream = library("java.io.InputStream", object, 0);
        SootClass ack = library(
                "org.apache.hadoop.hdfs.protocol.datatransfer.PipelineAck",
                object, 0);
        SootMethod readFields = method(ack, "readFields",
                Collections.<Type>singletonList(stream.getType()),
                VoidType.v(), Modifier.NATIVE);
        SootMethod analysed = reader(application("g.Reader", object), ack,
                stream, readFields, ioe);
        SootMethod unanalysed = reader(library("g.Library", object, 0), ack,
                stream, readFields, ioe);

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
     * woven right after that call: makePath's creates
     * (solr-bugs-overseer-lock-leak's {@code DistributedMap#put}) had none.
     * A call no hook call follows (create's own retry lambda, whose hook its
     * caller makes) or one outside the family carries none, and is named.
     */
    @Test
    public void aMovedDoorIsADoorAtEveryOtherCallItsHookFollows()
            throws Exception {
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        SootClass throwable = library("java.lang.Throwable", object, 0);
        SootClass exception = library("java.lang.Exception", throwable, 0);
        for (String kind : new String[]{"ConnectionLossException",
                "SessionExpiredException", "OperationTimeoutException"}) {
            method(library("org.apache.zookeeper.KeeperException$" + kind,
                    exception, 0), "<init>", Collections.<Type>emptyList(),
                    VoidType.v(), 0);
        }
        RefType string = RefType.v("java.lang.String");
        RefType mode = RefType.v("org.apache.zookeeper.CreateMode");
        List<Type> created = Arrays.<Type>asList(string,
                soot.ArrayType.v(soot.ByteType.v(), 1),
                RefType.v("java.util.List"), mode);
        SootClass zooKeeper = library("org.apache.zookeeper.ZooKeeper",
                object, 0);
        method(zooKeeper, "create", created, string, Modifier.NATIVE);
        SootClass solrZooKeeper = library(
                "org.apache.solr.common.cloud.SolrZooKeeper", zooKeeper, 0);
        SootClass client = application(
                "org.apache.solr.common.cloud.SolrZkClient", object);
        SootMethod wrote = method(client, "causynthWrote",
                Arrays.<Type>asList(string, IntType.v()), VoidType.v(),
                Modifier.STATIC | Modifier.NATIVE);
        List<Type> one = Collections.<Type>singletonList(string);
        SootMethod hook = writer(client, "create", Arrays.<Type>asList(string,
                soot.ArrayType.v(soot.ByteType.v(), 1), mode,
                BooleanType.v()), string, solrZooKeeper, created, wrote, 1,
                true);
        SootMethod retried = writer(client, "lambda$create$1", one,
                VoidType.v(), solrZooKeeper, created, wrote, 1, false);
        SootMethod makePath = writer(client, "makePath", one, VoidType.v(),
                solrZooKeeper, created, wrote, 1, true);
        SootMethod lambda = writer(client, "lambda$makePath$0", one,
                VoidType.v(), solrZooKeeper, created, wrote, 1, true);
        SootMethod twice = writer(client, "createTwo", one, VoidType.v(),
                solrZooKeeper, created, wrote, 2, true);
        SootMethod hookOnly = writer(client, "delete", one, VoidType.v(),
                solrZooKeeper, created, wrote, 0, true);
        SootMethod outside = writer(application("org.apache.solr.cloud.Other",
                object), "write", one, VoidType.v(), solrZooKeeper, created,
                wrote, 1, true);
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
                        + "SessionExpiredException, FAULT:ZOOKEEPER:WRITE:"
                        + "KeeperException$OperationTimeoutException]",
                after.toString()},
            {"right after the hook call", true, DoorWeave.isWoven(
                makePath.getActiveBody().getUnits().getSuccOf(hooked))}};
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], row[2]);
        }
    }

    /** A method making {@code creates} creates through {@code keeper}'s
     *  class, each followed by its store hook when {@code hooked}; with
     *  none, the hook alone. */
    private static SootMethod writer(SootClass owner, String name,
                                     List<Type> parameters, Type returned,
                                     SootClass keeper, List<Type> created,
                                     SootMethod wrote, int creates,
                                     boolean hooked) {
        SootMethod method = method(owner, name, parameters, returned,
                Modifier.STATIC);
        Local path = local(method, "r0", RefType.v("java.lang.String"));
        Local held = local(method, "r1", keeper.getType());
        List<Unit> units = new ArrayList<>();
        units.add(J.newIdentityStmt(path, J.newParameterRef(
                RefType.v("java.lang.String"), 0)));
        units.add(J.newAssignStmt(held, soot.jimple.NullConstant.v()));
        soot.SootMethodRef create = Scene.v().makeMethodRef(keeper, "create",
                created, RefType.v("java.lang.String"), false);
        for (int write = 0; write < Math.max(1, creates); write++) {
            if (creates > 0) {
                units.add(J.newInvokeStmt(J.newVirtualInvokeExpr(held, create,
                        Arrays.<soot.Value>asList(path,
                                soot.jimple.NullConstant.v(),
                                soot.jimple.NullConstant.v(),
                                soot.jimple.NullConstant.v()))));
            }
            if (hooked) {
                units.add(J.newInvokeStmt(J.newStaticInvokeExpr(
                        wrote.makeRef(), path, IntConstant.v(0))));
            }
        }
        units.add(returned instanceof VoidType ? J.newReturnVoidStmt()
                : J.newReturnStmt(soot.jimple.NullConstant.v()));
        body(method, units.toArray(new Unit[0]));
        return method;
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
     * it, and raises from its marker; a door asked again at a call that
     * holds one is refused by name.
     */
    @Test
    public void aDemandedDoorStandsOnlyAtTheCallChosenForIt()
            throws Exception {
        String open = "<java.io.FileOutputStream: void <init>(java.io.File)>";
        String rename = "<java.io.File: boolean renameTo(java.io.File)>";
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
        int calls = 0;
        for (Unit unit : save.getActiveBody().getUnits()) {
            DoorWeave.Fault thrown = DoorWeave.woven(save.getActiveBody(),
                    unit);
            DoorWeave.Fault failing = DoorWeave.wovenResult(
                    save.getActiveBody(), unit);
            if (thrown != null) woven.add(thrown.name);
            if (failing != null) woven.add(failing.name + " -> false");
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
                        + "FAULT:LOCAL_IO:NAMESPACE -> false] 2",
                woven + " " + calls},
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
     * the system's {@code g.Lib} (outside the scope), then stores {@code
     * ok}.
     */
    private static SootMethod store() {
        G.reset();
        soot.options.Options.v().set_allow_phantom_refs(true);
        SootClass object = library("java.lang.Object", null, 0);
        SootClass throwable = library("java.lang.Throwable", object, 0);
        SootClass exception = library("java.lang.Exception", throwable, 0);
        library("java.lang.RuntimeException", exception, 0);
        SootClass ioe = library(IOE, exception, 0);
        SootClass missing = library("java.io.FileNotFoundException", ioe, 0);
        for (SootClass kind : new SootClass[]{ioe, missing}) {
            method(kind, "<init>", Collections.<Type>singletonList(
                    RefType.v("java.lang.String")), VoidType.v(), 0);
        }
        SootClass debug = library(
                "edu.uva.liftlab.graphchecker.annotation.Debug", object, 0);
        method(debug, "makeSymbolicBoolean", Collections.<Type>singletonList(
                RefType.v("java.lang.String")), BooleanType.v(),
                Modifier.STATIC | Modifier.NATIVE);
        SootClass file = library("java.io.File", object, 0);
        SootMethod renameTo = method(file, "renameTo",
                Collections.<Type>singletonList(file.getType()),
                BooleanType.v(), Modifier.NATIVE);
        SootClass stream = library("java.io.FileOutputStream", object, 0);
        SootMethod init = method(stream, "<init>",
                Collections.<Type>singletonList(file.getType()),
                VoidType.v(), Modifier.NATIVE);
        SootClass lib = library("g.Lib", object, 0);
        SootMethod flush = method(lib, "flush",
                Collections.<Type>emptyList(), VoidType.v(),
                Modifier.STATIC | Modifier.NATIVE);
        flush.addException(ioe);

        SootClass owner = application("g.Store", object);
        SootField ok = new SootField("ok", IntType.v(), 0);
        owner.addField(ok);
        SootMethod save = method(owner, "save", Arrays.<Type>asList(
                file.getType(), file.getType()), VoidType.v(), 0);
        Local r0 = local(save, "r0", owner.getType());
        Local r1 = local(save, "r1", file.getType());
        Local r2 = local(save, "r2", file.getType());
        Local out = local(save, "$r3", stream.getType());
        Local renamed = local(save, "$z0", BooleanType.v());
        Local thrown = local(save, "$r4", ioe.getType());
        Unit flushed = J.newInvokeStmt(J.newStaticInvokeExpr(
                flush.makeRef()));
        body(save, J.newIdentityStmt(r0, J.newThisRef(owner.getType())),
                J.newIdentityStmt(r1, J.newParameterRef(file.getType(), 0)),
                J.newIdentityStmt(r2, J.newParameterRef(file.getType(), 1)),
                J.newAssignStmt(out, J.newNewExpr(stream.getType())),
                J.newInvokeStmt(J.newSpecialInvokeExpr(out, init.makeRef(),
                        r1)),
                J.newAssignStmt(renamed, J.newVirtualInvokeExpr(r1,
                        renameTo.makeRef(), r2)),
                J.newIfStmt(J.newNeExpr(renamed, IntConstant.v(0)), flushed),
                J.newAssignStmt(thrown, J.newNewExpr(ioe.getType())),
                J.newInvokeStmt(J.newSpecialInvokeExpr(thrown, ioe
                        .getMethodByName("<init>").makeRef(),
                        StringConstant.v("rename"))),
                J.newThrowStmt(thrown), flushed,
                J.newAssignStmt(J.newInstanceFieldRef(r0, ok.makeRef()),
                        IntConstant.v(1)), J.newReturnVoidStmt());
        return save;
    }

    private static String handlersOf(FaultPropagation faults, String method,
                                     List<Unit> raises) {
        List<Object> found = new ArrayList<>();
        for (Unit raise : raises) found.add(faults.handlers(method, raise));
        return found.toString();
    }

    /** {@code void read(PipelineAck, InputStream)}: {@code readFields}
     *  under an IOException handler, a store on each arm. */
    private static SootMethod reader(SootClass owner, SootClass ack,
                                     SootClass stream, SootMethod readFields,
                                     SootClass ioe) {
        SootField ok = new SootField("ok", IntType.v(), 0);
        owner.addField(ok);
        SootMethod read = method(owner, "read", Arrays.<Type>asList(
                ack.getType(), stream.getType()), VoidType.v(), 0);
        Local r0 = local(read, "r0", owner.getType());
        Local r1 = local(read, "r1", ack.getType());
        Local r2 = local(read, "r2", stream.getType());
        Local caught = local(read, "$r3", ioe.getType());
        Unit called = J.newInvokeStmt(J.newVirtualInvokeExpr(r1,
                readFields.makeRef(), r2));
        Unit left = J.newReturnVoidStmt();
        Unit handler = J.newIdentityStmt(caught, J.newCaughtExceptionRef());
        body(read, J.newIdentityStmt(r0, J.newThisRef(owner.getType())),
                J.newIdentityStmt(r1, J.newParameterRef(ack.getType(), 0)),
                J.newIdentityStmt(r2, J.newParameterRef(stream.getType(), 1)),
                called, J.newAssignStmt(J.newInstanceFieldRef(r0,
                        ok.makeRef()), IntConstant.v(1)), left, handler,
                J.newAssignStmt(J.newInstanceFieldRef(r0, ok.makeRef()),
                        IntConstant.v(0)), J.newReturnVoidStmt());
        read.getActiveBody().getTraps().add(J.newTrap(ioe, called, left,
                handler));
        return read;
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

        SootClass caller = application("f.Caller", object);
        SootField ok = new SootField("ok", IntType.v(), 0);
        caller.addField(ok);
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
