package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * Coarse application-region exclusion at a communication boundary.
 *
 * <p>Segmentation splits a communicating method around its cuts, and a window
 * is one method's CFG fragment.  Three kinds of frame therefore sit outside
 * every window, and only one of them is a coverage gap:</p>
 *
 * <ul>
 *   <li>the <b>sending</b> transport - the cut callee and what it reaches.  On
 *       the far side of the cut by README section 3, and claiming it would be
 *       the merge the core invariants forbid;</li>
 *   <li>the <b>receiving</b> transport - the frame that hands the arrived
 *       request over and the frame that publishes the reply.  Equally far
 *       side, but reachable from the serving thread without crossing a cut, so
 *       no rule rooted at the cuts finds it.  It is declared;</li>
 *   <li>the activation's own <b>near-side</b> frames above the cut-holding
 *       method.  These are neither transport nor claimed, and covering them is
 *       an attribution the runtime makes over one observed activation - never
 *       a widened static window, because the same frame commonly reaches a
 *       client fragment and a server fragment in two different activations of
 *       one thread-entry method.</li>
 * </ul>
 *
 * <p>These tests pin that boundary, so the next reader does not have to
 * re-derive which of the three a given uncovered frame is.</p>
 */
public class CommunicationTransportDeclarationTest {
    private static final String CHANNEL = "example.Channel";
    private static final String CALL_SERVER =
            "<example.Channel: int callServer(int)>";
    private static final String AWAIT_REQUEST =
            "<example.Channel: int awaitRequest()>";
    private static final String PUBLISH_RESPONSE =
            "<example.Channel: void publishResponse(int)>";
    private static final String EXECUTE =
            "<example.ClientActivation: int execute(example.Channel,int)>";
    private static final String SERVE = "<example.Handler: int serve(int)>";
    private static final String EXECUTE_WORKER = "<example.ServerLoop: "
            + "void executeWorker(example.Channel,example.Handler)>";

    private final Map<String, Body> bodies = new LinkedHashMap<>();

    @Before
    public void resetBefore() {
        soot.G.reset();
        bodies.clear();
        buildSlice();
    }

    @After
    public void resetAfter() {
        soot.G.reset();
    }

    // ------------------------------------------------------------------
    // The declaration
    // ------------------------------------------------------------------

    /**
     * The declaration names both halves of the transport, and the receiving
     * half is the half that needs it: no cut callee reaches
     * {@code awaitRequest} or {@code publishResponse}, so before this they
     * were indistinguishable from a frame nothing had attributed yet.
     */
    @Test
    public void implementationFramesAreExcludedWithoutArtifactMetadata() {
        CommunicationCatalogPlanner.Result result = plan(
                Collections.<String>emptySet());

        assertEquals(new LinkedHashSet<>(Arrays.asList(
                AWAIT_REQUEST, CALL_SERVER, PUBLISH_RESPONSE)),
                new LinkedHashSet<>(result.regionEnvelopeExclusions));
        // The sending half is derivable from the cut alone; the receiving half
        // is exactly what a cut-callee-rooted rule cannot see.
        assertEquals(Collections.singleton(CALL_SERVER), result.callSiteCallees);
    }

    /**
     * An adapter may declare a transport frame the planner's own rule cannot
     * derive - a different package, a different type - and the union is used.
     */
    @Test
    public void adapterDeclarationIsAddedToTheDerivedSurface() {
        CommunicationCatalogPlanner.Result result = plan(
                Collections.singleton(EXECUTE_WORKER));

        assertTrue(result.regionEnvelopeExclusions.contains(EXECUTE_WORKER));
        assertTrue(result.regionEnvelopeExclusions.contains(AWAIT_REQUEST));
    }

    /**
     * A declaration never silences a fragment.  A cut holder and a server
     * entry are where the slice decides something, so an adapter that names
     * one of them is subtracted rather than obeyed, and both keep their
     * segments.
     */
    @Test
    public void aDeclarationCannotTurnADecisionSiteIntoTransport() {
        CommunicationCatalogPlanner.Result result = plan(
                new LinkedHashSet<>(Arrays.asList(EXECUTE, SERVE)));

        assertFalse(result.regionEnvelopeExclusions.contains(EXECUTE));
        assertFalse(result.regionEnvelopeExclusions.contains(SERVE));
        // Both remain decision sites of the slice: the call holder keeps its
        // call-site row and the entry stays a resolved server entry.
        assertEquals(Collections.singleton(EXECUTE), clientMethods(result));
        assertTrue(result.serverEntryMethods.contains(SERVE));
    }

    // ------------------------------------------------------------------
    // The window boundary
    // ------------------------------------------------------------------




    // ------------------------------------------------------------------
    // The declaration reaches the region
    // ------------------------------------------------------------------

    /**
     * The region skeleton publishes both halves, so a consumer that already
     * knows what to do with a cut callee's frames treats the receiving half
     * the same way.
     */
    @Test
    public void regionSkeletonContainsCallerAndHandlerButNotImplementation() {
        StaticProgram program = new StaticProgram();
        program.executionContextAuthorities.put(EXECUTE_WORKER,
                "THREAD_ENTRY");
        program.targetResolved.put("method", SERVE);
        program.edges.add(edge(EXECUTE_WORKER, AWAIT_REQUEST));
        program.edges.add(edge(EXECUTE_WORKER, SERVE));
        program.edges.add(edge(EXECUTE_WORKER, PUBLISH_RESPONSE));
        program.edges.add(exceptionEdge(SERVE));
        program.regionEnvelopeExclusions.addAll(Arrays.asList(
                AWAIT_REQUEST, CALL_SERVER, PUBLISH_RESPONSE));

        SymbolicRegionPlanner.planSelectedSkeleton(program, Arrays.asList(
                EXECUTE_WORKER, AWAIT_REQUEST, SERVE, PUBLISH_RESPONSE));

        List<?> methods = (List<?>) program.regions.get(0).get("methods");
        assertTrue(methods.contains(EXECUTE_WORKER));
        assertTrue(methods.contains(SERVE));
        assertFalse(methods.contains(AWAIT_REQUEST));
        assertFalse(methods.contains(PUBLISH_RESPONSE));
    }

    // ------------------------------------------------------------------
    // Fixture
    // ------------------------------------------------------------------

    private CommunicationCatalogPlanner.Result plan(
            Set<String> adapterDeclared) {
        return CommunicationCatalogPlanner.plan(bodies.keySet(), bodies::get,
                new StubAdapter(adapterDeclared));
    }

    /**
     * One synchronous exchange declared by a stub adapter, so the rules under
     * test are the planner's own and not a protocol adapter's.
     */
    private static final class StubAdapter
            implements CommunicationCallSiteAdapter {
        private final Set<String> declared;

        private StubAdapter(Set<String> declared) {
            this.declared = declared;
        }

        @Override
        public String name() {
            return "STUB";
        }

        @Override
        public void prepare(Collection<String> selectedMethods,
                            Function<String, Body> resolver) {
        }

        @Override
        public CommunicationResolution resolve(String enclosingMethod,
                                               int unitIndex,
                                               String declaredCallee) {
            if (!CALL_SERVER.equals(declaredCallee)) {
                return CommunicationResolution.none();
            }
            return CommunicationResolution.site(new CommunicationCallSite(
                    enclosingMethod, unitIndex, "STUB",
                    CommunicationCatalogContract.TRANSPORT_HADOOP_IPC,
                    CHANNEL, declaredCallee,
                    Collections.singletonList(SERVE), true, "int",
                    Collections.singletonList(
                            new CommunicationCallSite.RequestPort("p0", 0, 0,
                                    "int")), Collections
                    .<CommunicationCallSite.ResponseComponentPort>emptyList()));
        }

        @Override
        public Collection<String> transportImplementationMethods() {
            return declared;
        }
    }

    private void buildSlice() {
        SootClass object = libraryClass("java.lang.Object");
        SootClass channel = applicationClass(CHANNEL, object);
        SootClass handler = applicationClass("example.Handler", object);
        SootClass client = applicationClass("example.ClientActivation",
                object);
        SootClass loop = applicationClass("example.ServerLoop", object);

        SootMethod callServer = method(channel, "callServer",
                Collections.<Type>singletonList(IntType.v()), IntType.v(),
                Modifier.PUBLIC);
        SootMethod awaitRequest = method(channel, "awaitRequest",
                Collections.<Type>emptyList(), IntType.v(), Modifier.PUBLIC);
        SootMethod publishResponse = method(channel, "publishResponse",
                Collections.<Type>singletonList(IntType.v()), VoidType.v(),
                Modifier.PUBLIC);
        SootMethod serve = method(handler, "serve",
                Collections.<Type>singletonList(IntType.v()), IntType.v(),
                Modifier.PUBLIC);
        SootMethod execute = method(client, "execute",
                Arrays.<Type>asList(RefType.v(CHANNEL), IntType.v()),
                IntType.v(), Modifier.PUBLIC | Modifier.STATIC);
        SootMethod executeWorker = method(loop, "executeWorker",
                Arrays.<Type>asList(RefType.v(CHANNEL),
                        RefType.v("example.Handler")),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);

        branchingInstanceMethod(callServer, channel);
        branchingInstanceMethod(awaitRequest, channel);
        publishResponseBody(publishResponse, channel);
        serveBody(serve, handler);
        executeBody(execute, callServer);
        executeWorkerBody(executeWorker, awaitRequest, serve,
                publishResponse);
    }

    /**
     * <pre>
     * u0 self := @this
     * u1 chan := @parameter0
     * u2 seed := @parameter1
     * u3 if seed &lt;= 0 goto u9      // branch BEFORE the cut
     * u4 pre  = seed + 1
     * u5 reply = chan.callServer(seed)   // the cut
     * u6 if reply &lt;= 0 goto u10    // branch AFTER the cut
     * u7 total = reply + pre
     * u8 goto u10
     * u9 return seed
     * u10 return reply
     * </pre>
     */
    private void executeBody(SootMethod method, SootMethod callServer) {
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local chan = local(body, "chan", RefType.v(CHANNEL));
        Local seed = local(body, "seed", IntType.v());
        Local pre = local(body, "pre", IntType.v());
        Local reply = local(body, "reply", IntType.v());
        Local total = local(body, "total", IntType.v());
        Unit earlyReturn = Jimple.v().newReturnStmt(seed);
        Unit exit = Jimple.v().newReturnStmt(reply);
        // One leading unit that is neither identity nor branch keeps the cut
        // at u5, which the delta assertions name explicitly.
        body.getUnits().add(Jimple.v().newIdentityStmt(chan,
                Jimple.v().newParameterRef(chan.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(seed,
                Jimple.v().newParameterRef(IntType.v(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(reply,
                IntConstant.v(0)));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(seed, IntConstant.v(0)), earlyReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(pre,
                Jimple.v().newAddExpr(seed, IntConstant.v(1))));
        body.getUnits().add(Jimple.v().newAssignStmt(reply,
                Jimple.v().newVirtualInvokeExpr(chan, callServer.makeRef(),
                        seed)));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(reply, IntConstant.v(0)), exit));
        body.getUnits().add(Jimple.v().newAssignStmt(total,
                Jimple.v().newAddExpr(reply, pre)));
        body.getUnits().add(Jimple.v().newGotoStmt(exit));
        body.getUnits().add(earlyReturn);
        body.getUnits().add(exit);
        bodies.put(method.getSignature(), body);
    }

    /**
     * <pre>
     * u0 chan := @parameter0
     * u1 handler := @parameter1
     * u2 if chan == null goto u6
     * u3 request = chan.awaitRequest()
     * u4 response = handler.serve(request)
     * u5 chan.publishResponse(response)
     * u6 return
     * </pre>
     */
    private void executeWorkerBody(SootMethod method, SootMethod await,
                                   SootMethod serve, SootMethod publish) {
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local chan = local(body, "chan", RefType.v(CHANNEL));
        Local handler = local(body, "handler",
                RefType.v("example.Handler"));
        Local request = local(body, "request", IntType.v());
        Local response = local(body, "response", IntType.v());
        Unit exit = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIdentityStmt(chan,
                Jimple.v().newParameterRef(chan.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(handler,
                Jimple.v().newParameterRef(handler.getType(), 1)));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(chan, soot.jimple.NullConstant.v()),
                exit));
        body.getUnits().add(Jimple.v().newAssignStmt(request,
                Jimple.v().newVirtualInvokeExpr(chan, await.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(response,
                Jimple.v().newVirtualInvokeExpr(handler, serve.makeRef(),
                        request)));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newVirtualInvokeExpr(chan, publish.makeRef(),
                        response)));
        body.getUnits().add(exit);
        bodies.put(method.getSignature(), body);
    }

    /** {@code u2} is the only branch: the server fragment's own delta. */
    private void serveBody(SootMethod method, SootClass owner) {
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local self = local(body, "self", RefType.v(owner.getName()));
        Local arg = local(body, "arg", IntType.v());
        Local out = local(body, "out", IntType.v());
        Unit passthrough = Jimple.v().newReturnStmt(arg);
        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef((RefType) self.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(arg,
                Jimple.v().newParameterRef(IntType.v(), 0)));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(arg, IntConstant.v(0)), passthrough));
        body.getUnits().add(Jimple.v().newAssignStmt(out,
                Jimple.v().newAddExpr(arg, IntConstant.v(100))));
        body.getUnits().add(Jimple.v().newReturnStmt(out));
        body.getUnits().add(passthrough);
        bodies.put(method.getSignature(), body);
    }

    /** A transport frame with a branch of its own, which no window claims. */
    private void branchingInstanceMethod(SootMethod method, SootClass owner) {
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local self = local(body, "self", RefType.v(owner.getName()));
        Local value = local(body, "value", IntType.v());
        Unit zero = Jimple.v().newReturnStmt(IntConstant.v(0));
        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef((RefType) self.getType())));
        if (method.getParameterCount() == 1) {
            body.getUnits().add(Jimple.v().newIdentityStmt(value,
                    Jimple.v().newParameterRef(IntType.v(), 0)));
        } else {
            body.getUnits().add(Jimple.v().newAssignStmt(value,
                    IntConstant.v(1)));
        }
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(value, IntConstant.v(0)), zero));
        body.getUnits().add(Jimple.v().newReturnStmt(value));
        body.getUnits().add(zero);
        bodies.put(method.getSignature(), body);
    }

    private void publishResponseBody(SootMethod method, SootClass owner) {
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local self = local(body, "self", RefType.v(owner.getName()));
        Local value = local(body, "value", IntType.v());
        body.getUnits().add(Jimple.v().newIdentityStmt(self,
                Jimple.v().newThisRef((RefType) self.getType())));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(IntType.v(), 0)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        bodies.put(method.getSignature(), body);
    }

    private static SootMethod method(SootClass owner, String name,
                                     List<Type> parameters, Type returnType,
                                     int modifiers) {
        SootMethod method = new SootMethod(name, parameters, returnType,
                modifiers);
        owner.addMethod(method);
        return method;
    }

    private static SootClass applicationClass(String name, SootClass parent) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        sootClass.setSuperclass(parent);
        Scene.v().addClass(sootClass);
        sootClass.setApplicationClass();
        return sootClass;
    }

    private static SootClass libraryClass(String name) {
        SootClass sootClass = new SootClass(name, Modifier.PUBLIC);
        Scene.v().addClass(sootClass);
        sootClass.setLibraryClass();
        return sootClass;
    }

    private static Local local(Body body, String name, Type type) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }

    // ------------------------------------------------------------------
    // Row helpers
    // ------------------------------------------------------------------

    private static Map<String, Object> edge(String method, String invoke) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 3);
        row.put("method", method);
        row.put("invoke", invoke);
        row.put("transferKind", "VALUE_PASS");
        row.put("kind", "local");
        row.put("fromCell", "x");
        row.put("toCell", "y");
        return row;
    }

    private static Map<String, Object> exceptionEdge(String method) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion", 3);
        row.put("method", method);
        row.put("transferKind", "GUARD");
        row.put("kind", "exception_guard");
        row.put("fromCell", "guard");
        row.put("toCell", method + "#u2#exception:Failure");
        return row;
    }

    private static Set<String> clientMethods(
            CommunicationCatalogPlanner.Result result) {
        Set<String> methods = new LinkedHashSet<>();
        for (Map<String, Object> row : result.callSites) {
            methods.add(text(row.get(
                    CommunicationCatalogContract.CLIENT_METHOD)));
        }
        return methods;
    }

    private static String text(Object value) {
        return value == null ? "" : String.valueOf(value);
    }
}
