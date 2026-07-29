package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.Body;
import soot.BooleanType;
import soot.IntType;
import soot.Local;
import soot.Modifier;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.VoidType;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

public class SeedBackwardStaticAnalyzerTest {
    @Before
    public void resetBefore() {
        soot.G.reset();
        System.clearProperty("causynth.protocol.stubs");
    }

    @After
    public void resetAfter() {
        System.clearProperty("causynth.protocol.stubs");
        soot.G.reset();
    }

    @Test
    public void configuredProtocolStubMapsSelectedRequestPorts()
            throws Exception {
        RpcFixture fixture = rpcFixture();
        Path mappings = Files.createTempFile("protocol-stubs", ".jsonl");
        try {
            String row = "{\"schemaVersion\":1,"
                    + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                    + "\"id\":\"test.rpc\","
                    + "\"transport\":\"TEST_RPC\","
                    + "\"clientStub\":\""
                    + fixture.client.getSignature() + "\","
                    + "\"serverStub\":\""
                    + fixture.server.getSignature() + "\","
                    + "\"request\":[{\"name\":\"payload\","
                    + "\"clientArgument\":1,\"serverParameter\":0}],"
                    + "\"response\":true}\n";
            Files.write(mappings, row.getBytes(StandardCharsets.UTF_8));
            System.setProperty("causynth.protocol.stubs",
                    mappings.toString());

            StaticProgram program = analyze(fixture);
            Map<String, Object> edge = edge(program.edges,
                    "rpc_caller_argument");
            assertNotNull(edge);
            assertEquals("test.rpc", edge.get("protocolStubMappingId"));
            assertEquals("TEST_RPC", edge.get("protocolTransport"));
            assertEquals("payload", edge.get("protocolPort"));
            assertEquals(fixture.server.getSignature() + ".param0:int",
                    edge.get("toCell"));
            assertTrue(String.valueOf(edge.get("fromCell"))
                    .endsWith("::input"));
            assertFalse(program.edges.stream().anyMatch(candidate ->
                    String.valueOf(candidate.get("kind"))
                            .startsWith("dispatch_")));
            assertNotNull(edge(program.edges, "exception_guard"));
            assertFalse(program.edges.stream().anyMatch(candidate ->
                    "seed_exception_throw".equals(candidate.get("kind"))
                            || "exception_payload_argument".equals(
                            candidate.get("kind"))));
        } finally {
            Files.deleteIfExists(mappings);
        }
    }

    @Test
    public void protocolLikeNamesDoNotCreateRpcEdgesWithoutConfiguration()
            throws Exception {
        StaticProgram program = analyze(rpcFixture());
        assertFalse(program.edges.stream().anyMatch(edge ->
                String.valueOf(edge.get("kind")).startsWith("rpc_")));
    }

    @Test
    public void typedMapLookupProjectionRetainsReceiverAndMutationGuard()
            throws Exception {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass map = new SootClass("java.util.Map",
                Modifier.PUBLIC | Modifier.INTERFACE);
        Scene.v().addClass(map);
        SootMethod get = new SootMethod("get",
                Collections.singletonList(RefType.v(object.getName())),
                RefType.v(object.getName()),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        SootMethod put = new SootMethod("put",
                Arrays.asList(RefType.v(object.getName()),
                        RefType.v(object.getName())),
                RefType.v(object.getName()),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        map.addMethod(get);
        map.addMethod(put);

        SootClass node = applicationClass("example.CastNode", object);
        SootField nodeFlag = new SootField("flag", BooleanType.v(),
                Modifier.PUBLIC);
        SootField nodeValue = new SootField("value", IntType.v(),
                Modifier.PUBLIC);
        node.addField(nodeFlag);
        node.addField(nodeValue);

        SootClass bug = applicationClass("example.CastBug",
                runtimeException);
        SootMethod bugConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        bug.addMethod(bugConstructor);
        constructorBody(bugConstructor, runtimeConstructor);

        SootClass owner = applicationClass("example.CastProducer", object);
        SootField values = new SootField("values",
                RefType.v(map.getName()), Modifier.PUBLIC | Modifier.STATIC);
        SootField key = new SootField("key", RefType.v(object.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField fallback = new SootField("fallback", IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField replacement = new SootField("replacement",
                RefType.v(node.getName()), Modifier.PUBLIC | Modifier.STATIC);
        SootField mutate = new SootField("mutate", BooleanType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField output = new SootField("output", IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        for (SootField field : Arrays.asList(values, key, fallback,
                replacement, mutate, output)) {
            owner.addField(field);
        }

        SootMethod compute = buildCompute(owner, map, node, get, put,
                values, key, fallback, replacement, mutate,
                nodeFlag, nodeValue);
        buildProducer(owner, compute, output);
        SootMethod consumer = buildConsumer(owner, bug, bugConstructor,
                output);

        ExceptionTargetSite site = new ExceptionTargetSite(
                "typed-map-cast", owner.getName(), consumer.getName(), "()V",
                consumer.getSignature(), bug.getName(), 0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();
        SymbolicRegionPlanner.planSelected(program,
                program.graph().methods());

        String projectionEdge = edgeId(program.edges,
                "container_projection");
        String mutationGuardEdge = edgeId(program.edges,
                "heap_mutation_path_guard");
        assertNotNull(projectionEdge);
        assertNotNull(mutationGuardEdge);

        Map<String, Object> slice = sliceContaining(program,
                projectionEdge, mutationGuardEdge);
        assertNotNull(slice);
        assertTrue(inputCells(slice).contains(values.getSignature()));
    }

    private static SootMethod buildCompute(
            SootClass owner, SootClass map, SootClass node,
            SootMethod get, SootMethod put, SootField values,
            SootField key, SootField fallback, SootField replacement,
            SootField mutate, SootField nodeFlag, SootField nodeValue) {
        SootMethod method = new SootMethod("compute",
                Collections.emptyList(), IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local mapLocal = local(body, "map", RefType.v(map.getName()));
        Local keyLocal = local(body, "key", RefType.v("java.lang.Object"));
        Local replacementLocal = local(body, "replacement",
                RefType.v(node.getName()));
        Local mutateLocal = local(body, "mutate", BooleanType.v());
        Local objectResult = local(body, "raw",
                RefType.v("java.lang.Object"));
        Local typedResult = local(body, "node", RefType.v(node.getName()));
        Local flagLocal = local(body, "flag", BooleanType.v());
        Local valueLocal = local(body, "value", IntType.v());
        Local fallbackLocal = local(body, "fallback", IntType.v());

        body.getUnits().add(Jimple.v().newAssignStmt(mapLocal,
                Jimple.v().newStaticFieldRef(values.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(keyLocal,
                Jimple.v().newStaticFieldRef(key.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(fallbackLocal,
                Jimple.v().newStaticFieldRef(fallback.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(mutateLocal,
                Jimple.v().newStaticFieldRef(mutate.makeRef())));
        Unit lookup = Jimple.v().newAssignStmt(objectResult,
                Jimple.v().newInterfaceInvokeExpr(mapLocal, get.makeRef(),
                        keyLocal));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(mutateLocal, IntConstant.v(0)),
                lookup));
        body.getUnits().add(Jimple.v().newAssignStmt(replacementLocal,
                Jimple.v().newStaticFieldRef(replacement.makeRef())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(mapLocal, put.makeRef(),
                        keyLocal, replacementLocal)));
        body.getUnits().add(lookup);
        body.getUnits().add(Jimple.v().newAssignStmt(typedResult,
                Jimple.v().newCastExpr(objectResult,
                        RefType.v(node.getName()))));
        body.getUnits().add(Jimple.v().newAssignStmt(flagLocal,
                Jimple.v().newInstanceFieldRef(typedResult,
                        nodeFlag.makeRef())));
        Unit fallbackReturn = Jimple.v().newReturnStmt(fallbackLocal);
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(flagLocal, IntConstant.v(0)),
                fallbackReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(valueLocal,
                Jimple.v().newInstanceFieldRef(typedResult,
                        nodeValue.makeRef())));
        body.getUnits().add(Jimple.v().newReturnStmt(valueLocal));
        body.getUnits().add(fallbackReturn);
        return method;
    }

    private static void buildProducer(SootClass owner, SootMethod compute,
                                      SootField output) {
        SootMethod method = new SootMethod("produce",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local result = local(body, "result", IntType.v());
        body.getUnits().add(Jimple.v().newAssignStmt(result,
                Jimple.v().newStaticInvokeExpr(compute.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newStaticFieldRef(output.makeRef()), result));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
    }

    private static SootMethod buildConsumer(
            SootClass owner, SootClass bug, SootMethod bugConstructor,
            SootField output) {
        SootMethod method = new SootMethod("consume",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local value = local(body, "value", IntType.v());
        Local exception = local(body, "exception", RefType.v(bug.getName()));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newStaticFieldRef(output.makeRef())));
        Unit normalReturn = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(value, IntConstant.v(0)),
                normalReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(bug.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        bugConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(exception));
        body.getUnits().add(normalReturn);
        return method;
    }

    private static RpcFixture rpcFixture() {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass failure = applicationClass(
                "example.ProtocolFailure", runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass protocol = new SootClass("example.RemoteProtocol",
                Modifier.PUBLIC | Modifier.INTERFACE);
        Scene.v().addClass(protocol);
        protocol.setApplicationClass();
        SootMethod client = new SootMethod("request",
                Arrays.asList(IntType.v(), IntType.v()), IntType.v(),
                Modifier.PUBLIC | Modifier.ABSTRACT);
        protocol.addMethod(client);

        SootClass serverOwner = applicationClass(
                "example.RemoteServer", object);
        serverOwner.addInterface(protocol);
        SootMethod server = new SootMethod("request",
                Arrays.asList(IntType.v(), IntType.v()), IntType.v(),
                Modifier.PUBLIC);
        serverOwner.addMethod(server);
        Body serverBody = Jimple.v().newBody(server);
        server.setActiveBody(serverBody);
        Local receiver = local(serverBody, "this",
                RefType.v(serverOwner.getName()));
        Local parameter = local(serverBody, "payload", IntType.v());
        Local ignored = local(serverBody, "ignored", IntType.v());
        Local exception = local(serverBody, "failure",
                RefType.v(failure.getName()));
        serverBody.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef((RefType) receiver.getType())));
        serverBody.getUnits().add(Jimple.v().newIdentityStmt(parameter,
                Jimple.v().newParameterRef(IntType.v(), 0)));
        serverBody.getUnits().add(Jimple.v().newIdentityStmt(ignored,
                Jimple.v().newParameterRef(IntType.v(), 1)));
        Unit normalReturn = Jimple.v().newReturnStmt(parameter);
        serverBody.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(parameter, IntConstant.v(0)),
                normalReturn));
        serverBody.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        serverBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        serverBody.getUnits().add(Jimple.v().newThrowStmt(exception));
        serverBody.getUnits().add(normalReturn);

        SootClass callerOwner = applicationClass(
                "example.ProtocolCaller", object);
        SootField remote = new SootField("remote",
                RefType.v(protocol.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField input = new SootField("input", IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        callerOwner.addField(remote);
        callerOwner.addField(input);
        SootMethod caller = new SootMethod("call",
                Collections.emptyList(), IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        callerOwner.addMethod(caller);
        Body callerBody = Jimple.v().newBody(caller);
        caller.setActiveBody(callerBody);
        Local remoteLocal = local(callerBody, "remote",
                RefType.v(protocol.getName()));
        Local inputLocal = local(callerBody, "input", IntType.v());
        Local result = local(callerBody, "result", IntType.v());
        callerBody.getUnits().add(Jimple.v().newAssignStmt(remoteLocal,
                Jimple.v().newStaticFieldRef(remote.makeRef())));
        callerBody.getUnits().add(Jimple.v().newAssignStmt(inputLocal,
                Jimple.v().newStaticFieldRef(input.makeRef())));
        callerBody.getUnits().add(Jimple.v().newAssignStmt(result,
                Jimple.v().newInterfaceInvokeExpr(remoteLocal,
                        client.makeRef(), IntConstant.v(0), inputLocal)));
        callerBody.getUnits().add(Jimple.v().newReturnStmt(result));
        return new RpcFixture(client, server, failure);
    }

    private static StaticProgram analyze(RpcFixture fixture)
            throws Exception {
        ExceptionTargetSite site = new ExceptionTargetSite(
                "configured-rpc", fixture.server.getDeclaringClass().getName(),
                fixture.server.getName(), "(II)I",
                fixture.server.getSignature(),
                fixture.failure.getName(), 0, -1);
        return new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();
    }

    private static void constructorBody(SootMethod constructor,
                                        SootMethod parentConstructor) {
        Body body = Jimple.v().newBody(constructor);
        constructor.setActiveBody(body);
        Local receiver = local(body, "this",
                RefType.v(constructor.getDeclaringClass().getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newThisRef((RefType) receiver.getType())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(receiver,
                        parentConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
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

    private static Local local(Body body, String name, soot.Type type) {
        Local local = Jimple.v().newLocal(name, type);
        body.getLocals().add(local);
        return local;
    }

    private static String edgeId(List<Map<String, Object>> edges,
                                 String kind) {
        for (Map<String, Object> edge : edges) {
            if (kind.equals(edge.get("kind"))) {
                return String.valueOf(edge.get("id"));
            }
        }
        return null;
    }

    private static Map<String, Object> edge(
            List<Map<String, Object>> edges, String kind) {
        for (Map<String, Object> edge : edges) {
            if (kind.equals(edge.get("kind"))) {
                return edge;
            }
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> sliceContaining(
            StaticProgram program, String... edgeIds) {
        for (Map<String, Object> region : program.regions) {
            for (Map<String, Object> slice : (List<Map<String, Object>>)
                    region.get("outputSlices")) {
                List<String> causal = (List<String>)
                        slice.get("causalEdgeIds");
                if (causal.containsAll(Arrays.asList(edgeIds))) {
                    return slice;
                }
            }
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    private static List<String> inputCells(Map<String, Object> slice) {
        java.util.ArrayList<String> cells = new java.util.ArrayList<>();
        for (Map<String, Object> input : (List<Map<String, Object>>)
                slice.get("inputBindings")) {
            cells.add(String.valueOf(input.get("dependencyCell")));
        }
        return cells;
    }

    private static final class RpcFixture {
        private final SootMethod client;
        private final SootMethod server;
        private final SootClass failure;

        private RpcFixture(SootMethod client, SootMethod server,
                           SootClass failure) {
            this.client = client;
            this.server = server;
            this.failure = failure;
        }
    }
}
