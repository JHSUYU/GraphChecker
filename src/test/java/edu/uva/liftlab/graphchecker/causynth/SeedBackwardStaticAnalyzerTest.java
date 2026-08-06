package edu.uva.liftlab.graphchecker.causynth;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import soot.ArrayType;
import soot.Body;
import soot.BooleanType;
import soot.IntType;
import soot.Local;
import soot.LongType;
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
import soot.jimple.NullConstant;

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
import static org.junit.Assert.fail;

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
            assertEquals("EXECUTION_ENTRY",
                    edge.get("protocolServerContext"));
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
            assertEquals("RPC_HANDLER",
                    program.executionContextAuthorities.get(
                            fixture.server.getSignature()));
            assertFalse(program.nestedContextEndpoints.contains(
                    fixture.server.getSignature()));
        } finally {
            Files.deleteIfExists(mappings);
        }
    }

    @Test
    public void configuredInterfaceStubMapsConcreteClientInvocation()
            throws Exception {
        RpcFixture fixture = rpcFixture(true);
        Path mappings = Files.createTempFile("concrete-protocol-stubs",
                ".jsonl");
        try {
            String row = "{\"schemaVersion\":1,"
                    + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                    + "\"id\":\"test.concrete.rpc\","
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
            long callerEdges = program.edges.stream().filter(candidate ->
                    "rpc_caller_argument".equals(candidate.get("kind"))
                            && fixture.clientImplementation.getSignature()
                            .equals(candidate.get("invoke"))).count();
            long invokeEdges = program.edges.stream().filter(candidate ->
                    "rpc_argument".equals(candidate.get("kind"))
                            && fixture.clientImplementation.getSignature()
                            .equals(candidate.get("invoke"))).count();
            assertEquals(1L, callerEdges);
            assertEquals(1L, invokeEdges);
        } finally {
            Files.deleteIfExists(mappings);
        }
    }

    @Test
    public void nestedProtocolServerCallIsNotAnExecutionContextEntry()
            throws Exception {
        RpcFixture fixture = rpcFixture();
        Path mappings = Files.createTempFile("nested-protocol-stubs",
                ".jsonl");
        try {
            String row = "{\"schemaVersion\":1,"
                    + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                    + "\"id\":\"test.nested.rpc\","
                    + "\"transport\":\"TEST_RPC\","
                    + "\"serverContext\":\"NESTED_CALL\","
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
            assertEquals("NESTED_CALL",
                    edge.get("protocolServerContext"));
            assertFalse(program.executionContextAuthorities.containsKey(
                    fixture.server.getSignature()));
            assertTrue(program.nestedContextEndpoints.contains(
                    fixture.server.getSignature()));
        } finally {
            Files.deleteIfExists(mappings);
        }
    }

    @Test
    public void conflictingServerContextDeclarationsAreRejected()
            throws Exception {
        RpcFixture fixture = rpcFixture();
        Path mappings = Files.createTempFile("conflicting-protocol-stubs",
                ".jsonl");
        try {
            String prefix = "{\"schemaVersion\":1,"
                    + "\"kind\":\"PROTOCOL_STUB_MAPPING\","
                    + "\"transport\":\"TEST_RPC\","
                    + "\"clientStub\":\""
                    + fixture.client.getSignature() + "\","
                    + "\"serverStub\":\""
                    + fixture.server.getSignature() + "\","
                    + "\"request\":[{\"name\":\"payload\","
                    + "\"clientArgument\":1,\"serverParameter\":0}],"
                    + "\"response\":true,";
            String rows = prefix + "\"id\":\"entry\","
                    + "\"serverContext\":\"EXECUTION_ENTRY\"}\n"
                    + prefix + "\"id\":\"nested\","
                    + "\"serverContext\":\"NESTED_CALL\"}\n";
            Files.write(mappings, rows.getBytes(StandardCharsets.UTF_8));
            System.setProperty("causynth.protocol.stubs",
                    mappings.toString());

            try {
                analyze(fixture);
                fail("conflicting serverContext must be rejected");
            } catch (IllegalStateException expected) {
                assertTrue(String.valueOf(expected.getCause().getMessage())
                        .contains("Conflicting serverContext"));
            }
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
    public void inheritedLibraryPrimitiveGetterIsAStructuralAccessor()
            throws Exception {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass keyBase = libraryClass("example.LibraryKey");
        keyBase.setSuperclass(object);
        SootField expiry = new SootField("expiryDate", LongType.v(),
                Modifier.PRIVATE);
        keyBase.addField(expiry);
        SootMethod getter = new SootMethod("getExpiryDate",
                Collections.emptyList(), LongType.v(), Modifier.PUBLIC);
        keyBase.addMethod(getter);
        Body getterBody = Jimple.v().newBody(getter);
        getter.setActiveBody(getterBody);
        Local getterThis = local(getterBody, "this",
                RefType.v(keyBase.getName()));
        Local getterValue = local(getterBody, "value", LongType.v());
        getterBody.getUnits().add(Jimple.v().newIdentityStmt(getterThis,
                Jimple.v().newThisRef((RefType) getterThis.getType())));
        getterBody.getUnits().add(Jimple.v().newAssignStmt(getterValue,
                Jimple.v().newInstanceFieldRef(getterThis,
                        expiry.makeRef())));
        getterBody.getUnits().add(Jimple.v().newReturnStmt(getterValue));

        SootClass key = applicationClass("example.BlockKey", keyBase);
        SootClass failure = applicationClass("example.ExpiredKeyFailure",
                runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass owner = applicationClass("example.KeyManager", object);
        SootField currentKey = new SootField("currentKey",
                RefType.v(key.getName()), Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(currentKey);
        SootMethod check = new SootMethod("check",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(check);
        Body body = Jimple.v().newBody(check);
        check.setActiveBody(body);
        Local keyLocal = local(body, "key", RefType.v(key.getName()));
        Local expiryLocal = local(body, "expiry", LongType.v());
        Local exception = local(body, "failure", RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newAssignStmt(keyLocal,
                Jimple.v().newStaticFieldRef(currentKey.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(expiryLocal,
                Jimple.v().newVirtualInvokeExpr(keyLocal,
                        getter.makeRef())));
        Unit normalReturn = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newGeExpr(expiryLocal,
                        soot.jimple.LongConstant.v(0L)), normalReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(exception));
        body.getUnits().add(normalReturn);

        ExceptionTargetSite site = new ExceptionTargetSite(
                "inherited-accessor", owner.getName(), check.getName(),
                "()V", check.getSignature(), failure.getName(), 0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();

        Map<String, Object> edge = edge(program.edges,
                "accessor_field_return");
        assertNotNull(edge);
        assertEquals(expiry.getSignature(), edge.get("fromCell"));
        assertEquals(getter.getSignature(),
                edge.get("accessorImplementationMethod"));
    }

    @Test
    public void mapLookupUsedOnlyToSelectFieldOwnerIsStructureCarrier()
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
        map.addMethod(get);

        SootClass node = applicationClass("example.OwnerNode", object);
        SootField value = new SootField("value", IntType.v(),
                Modifier.PUBLIC);
        node.addField(value);
        SootClass failure = applicationClass("example.OwnerFailure",
                runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass owner = applicationClass("example.OwnerLookup", object);
        SootField values = new SootField("values", RefType.v(map.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        SootField key = new SootField("key", RefType.v(object.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(values);
        owner.addField(key);
        SootMethod check = new SootMethod("check",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(check);
        Body body = Jimple.v().newBody(check);
        check.setActiveBody(body);
        Local mapLocal = local(body, "map", RefType.v(map.getName()));
        Local keyLocal = local(body, "key", RefType.v(object.getName()));
        Local selected = local(body, "selected",
                RefType.v(object.getName()));
        Local nodeLocal = local(body, "node", RefType.v(node.getName()));
        Local scalar = local(body, "scalar", IntType.v());
        Local exception = local(body, "failure",
                RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newAssignStmt(mapLocal,
                Jimple.v().newStaticFieldRef(values.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(keyLocal,
                Jimple.v().newStaticFieldRef(key.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(selected,
                Jimple.v().newInterfaceInvokeExpr(mapLocal, get.makeRef(),
                        keyLocal)));
        body.getUnits().add(Jimple.v().newAssignStmt(nodeLocal,
                Jimple.v().newCastExpr(selected,
                        RefType.v(node.getName()))));
        Unit normal = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newEqExpr(nodeLocal, NullConstant.v()), normal));
        body.getUnits().add(Jimple.v().newAssignStmt(scalar,
                Jimple.v().newInstanceFieldRef(nodeLocal,
                        value.makeRef())));
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newNeExpr(scalar, IntConstant.v(0)), normal));
        body.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(exception));
        body.getUnits().add(normal);

        ExceptionTargetSite site = new ExceptionTargetSite(
                "owner-lookup", owner.getName(), check.getName(), "()V",
                check.getSignature(), failure.getName(), 0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();

        Map<String, Object> receiver = edge(program.edges,
                "container_receiver");
        assertNotNull(receiver);
        assertEquals("CONCRETE_STRUCTURE_CARRIER",
                receiver.get("dependencyRole"));
    }

    @Test
    public void typedMapLookupRetainsReceiverWithoutFieldProjection()
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

        SootMethod mutationHelper = buildMapMutationHelper(owner, map, node,
                put);
        SootMethod compute = buildCompute(owner, map, node, get, put,
                mutationHelper,
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
        assertFalse(program.edges.stream().anyMatch(edge ->
                String.valueOf(edge.get("kind")).startsWith("projected_")));
        assertEquals("CHEAP_RECEIVER_DEF_USE_JUMP_V1",
                program.targetResolved.get("candidateDiscoveryMode"));
        assertEquals(false,
                program.targetResolved.get("accessPathWorklistState"));
        assertEquals(true,
                program.targetResolved.get("receiverDefUseEnabled"));
        assertFalse(program.targetResolved.containsKey("fieldPathDepth"));
        assertEquals(false, program.targetResolved.get(
                "recursiveReceiverEffectClosure"));
        assertFalse(program.edges.stream().anyMatch(edge ->
                String.valueOf(edge.get("fromCell")).contains("#field:")
                        || String.valueOf(edge.get("toCell"))
                        .contains("#field:")));

        String receiverEdge = edgeId(program.edges,
                "container_receiver");
        String mutationArgumentEdge = edgeId(program.edges,
                "container_mutation_argument");
        String callMutationEdge = edgeId(program.edges,
                "container_call_mutation_effect");
        String mutationGuardEdge = edgeId(program.edges,
                "heap_mutation_path_guard");
        assertNotNull(receiverEdge);
        assertEquals("CONCRETE_STRUCTURE_CARRIER", edge(program.edges,
                "container_receiver").get("dependencyRole"));
        assertNotNull(mutationArgumentEdge);
        assertNotNull(callMutationEdge);
        assertEquals("MODEL_TRANSFORM", edge(program.edges,
                "container_mutation_argument").get("transferKind"));
        assertEquals("MODEL_TRANSFORM", edge(program.edges,
                "container_call_mutation_effect").get("transferKind"));
        assertNotNull(mutationGuardEdge);
        assertTrue(((Number) program.targetResolved.get(
                "globalFieldWriterIndexSize")).intValue() > 0);
    }

    @Test
    public void arrayStoreAndLoadCloseThroughBoundedElementCell()
            throws Exception {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass failure = applicationClass(
                "example.ArrayFailure", runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass owner = applicationClass("example.ArrayFlow", object);
        ArrayType ints = ArrayType.v(IntType.v(), 1);
        SootField source = new SootField("source", IntType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(source);

        SootMethod producer = new SootMethod("produce",
                Arrays.asList(IntType.v(), IntType.v()), ints,
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(producer);
        Body producerBody = Jimple.v().newBody(producer);
        producer.setActiveBody(producerBody);
        Local stored = local(producerBody, "stored", IntType.v());
        Local storeIndex = local(producerBody, "storeIndex", IntType.v());
        Local result = local(producerBody, "result", ints);
        producerBody.getUnits().add(Jimple.v().newIdentityStmt(stored,
                Jimple.v().newParameterRef(IntType.v(), 0)));
        producerBody.getUnits().add(Jimple.v().newIdentityStmt(storeIndex,
                Jimple.v().newParameterRef(IntType.v(), 1)));
        producerBody.getUnits().add(Jimple.v().newAssignStmt(result,
                Jimple.v().newNewArrayExpr(IntType.v(),
                        IntConstant.v(2))));
        producerBody.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newArrayRef(result, storeIndex), stored));
        producerBody.getUnits().add(Jimple.v().newReturnStmt(result));

        SootMethod consumer = new SootMethod("consume",
                Arrays.asList(ints, IntType.v()), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(consumer);
        Body consumerBody = Jimple.v().newBody(consumer);
        consumer.setActiveBody(consumerBody);
        Local input = local(consumerBody, "input", ints);
        Local loadIndex = local(consumerBody, "loadIndex", IntType.v());
        Local loaded = local(consumerBody, "loaded", IntType.v());
        Local exception = local(consumerBody, "failure",
                RefType.v(failure.getName()));
        consumerBody.getUnits().add(Jimple.v().newIdentityStmt(input,
                Jimple.v().newParameterRef(ints, 0)));
        consumerBody.getUnits().add(Jimple.v().newIdentityStmt(loadIndex,
                Jimple.v().newParameterRef(IntType.v(), 1)));
        consumerBody.getUnits().add(Jimple.v().newAssignStmt(loaded,
                Jimple.v().newArrayRef(input, loadIndex)));
        Unit normal = Jimple.v().newReturnVoidStmt();
        consumerBody.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(loaded, IntConstant.v(0)), normal));
        consumerBody.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        consumerBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        consumerBody.getUnits().add(Jimple.v().newThrowStmt(exception));
        consumerBody.getUnits().add(normal);

        SootMethod caller = new SootMethod("run",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(caller);
        Body callerBody = Jimple.v().newBody(caller);
        caller.setActiveBody(callerBody);
        Local sourceValue = local(callerBody, "source", IntType.v());
        Local produced = local(callerBody, "produced", ints);
        callerBody.getUnits().add(Jimple.v().newAssignStmt(sourceValue,
                Jimple.v().newStaticFieldRef(source.makeRef())));
        callerBody.getUnits().add(Jimple.v().newAssignStmt(produced,
                Jimple.v().newStaticInvokeExpr(producer.makeRef(),
                        sourceValue, IntConstant.v(0))));
        callerBody.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(consumer.makeRef(),
                        produced, IntConstant.v(0))));
        callerBody.getUnits().add(Jimple.v().newReturnVoidStmt());

        ExceptionTargetSite site = new ExceptionTargetSite(
                "array-flow", owner.getName(), consumer.getName(),
                "([II)V", consumer.getSignature(), failure.getName(),
                0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();

        String producerBase = producer.getSignature() + "::result";
        String producerElement = producerBase + "#array-element";
        String consumerBase = consumer.getSignature() + "::input";
        String consumerElement = consumerBase + "#array-element";
        assertTrue(hasEdge(program, "container_array_store_value",
                producer.getSignature() + "::stored", producerElement));
        assertTrue(hasEdge(program, "container_array_store_base",
                producerElement, producerBase));
        assertTrue(hasEdge(program, "container_array_load_base",
                consumerBase, consumerElement));
        assertTrue(hasEdge(program, "container_array_load_value",
                consumerElement, consumer.getSignature() + "::loaded"));
        assertEquals("RUNTIME_BOUNDED_SLOTS", edge(program.edges,
                "container_array_store_value").get("arraySlotPolicy"));
        assertFalse(program.edges.stream().anyMatch(candidate ->
                (producer.getSignature() + "::storeIndex").equals(
                        candidate.get("fromCell"))
                        || (producer.getSignature() + "::storeIndex").equals(
                        candidate.get("toCell"))
                        || (consumer.getSignature() + "::loadIndex").equals(
                        candidate.get("fromCell"))
                        || (consumer.getSignature() + "::loadIndex").equals(
                        candidate.get("toCell"))));
    }

    @Test
    public void nestedReceiverChainReachesParameterCallerAndFieldWriters()
            throws Exception {
        SootClass object = libraryClass("java.lang.Object");
        SootClass runtimeException = libraryClass(
                "java.lang.RuntimeException");
        runtimeException.setSuperclass(object);
        SootMethod runtimeConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        runtimeException.addMethod(runtimeConstructor);

        SootClass failure = applicationClass(
                "example.ReceiverFailure", runtimeException);
        SootMethod failureConstructor = new SootMethod("<init>",
                Collections.emptyList(), VoidType.v(), Modifier.PUBLIC);
        failure.addMethod(failureConstructor);
        constructorBody(failureConstructor, runtimeConstructor);

        SootClass rootType = applicationClass("example.RootState", object);
        SootClass middleType = applicationClass("example.MiddleState", object);
        SootClass leafType = applicationClass("example.LeafState", object);
        SootField rootMiddle = new SootField("middle",
                RefType.v(middleType.getName()), Modifier.PUBLIC);
        SootField middleLeaf = new SootField("leaf",
                RefType.v(leafType.getName()), Modifier.PUBLIC);
        SootField leafValue = new SootField("value", IntType.v(),
                Modifier.PUBLIC);
        rootType.addField(rootMiddle);
        middleType.addField(middleLeaf);
        leafType.addField(leafValue);

        SootClass owner = applicationClass("example.ReceiverComponent",
                object);
        SootField root = new SootField("root", RefType.v(rootType.getName()),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addField(root);

        SootMethod consume = buildNestedReceiverConsumer(owner, failure,
                failureConstructor, rootType, middleType, leafType,
                rootMiddle, middleLeaf, leafValue);
        SootMethod component = buildNestedReceiverCaller(owner, consume,
                rootType, root);
        SootMethod writeMiddle = buildInstanceFieldWriter(owner,
                "writeMiddle", rootType, middleType, rootMiddle);
        SootMethod writeLeaf = buildInstanceFieldWriter(owner,
                "writeLeaf", middleType, leafType, middleLeaf);
        SootMethod writeValue = buildIntFieldWriter(owner, leafType,
                leafValue);

        ExceptionTargetSite site = new ExceptionTargetSite(
                "receiver-def-use", owner.getName(), consume.getName(),
                "(" + rootType.getName().replace('.', '/') + ")V",
                consume.getSignature(), failure.getName(), 0, -1);
        StaticProgram program = new SeedBackwardStaticAnalyzer(
                new CausynthTargetContext(null, null, site.id, site,
                        "TEST")).analyze();

        assertTrue(program.traceMethods.contains(component.getSignature()));
        assertTrue(program.traceMethods.contains(writeMiddle.getSignature()));
        assertTrue(program.traceMethods.contains(writeLeaf.getSignature()));
        assertTrue(program.traceMethods.contains(writeValue.getSignature()));
        assertTrue(hasEdge(program, "local_def_use",
                consume.getSignature() + "::root",
                consume.getSignature() + "::middle"));
        assertTrue(hasEdge(program, "local_def_use",
                consume.getSignature() + "::middle",
                consume.getSignature() + "::leaf"));
        assertTrue(hasEdge(program, "local_def_use",
                consume.getSignature() + "::leaf",
                consume.getSignature() + "::value"));
        assertTrue(hasEdge(program, "caller_argument",
                component.getSignature() + "::root",
                consume.getSignature() + ".param0:" + rootType.getName()));
        assertNotNull(edge(program.edges, "method_activation"));
        assertTrue(hasEdge(program, "field_read", rootMiddle.getSignature(),
                consume.getSignature() + "::middle"));
        assertTrue(hasEdge(program, "field_read", middleLeaf.getSignature(),
                consume.getSignature() + "::leaf"));
        assertTrue(hasEdge(program, "field_read", leafValue.getSignature(),
                consume.getSignature() + "::value"));
        assertTrue(hasEdge(program, "field_write",
                writeMiddle.getSignature() + "::value",
                rootMiddle.getSignature()));
        assertFalse(hasEdge(program, "field_write",
                writeMiddle.getSignature() + "::receiver",
                rootMiddle.getSignature()));
        assertTrue(hasEdge(program, "field_write",
                writeValue.getSignature() + "::input",
                leafValue.getSignature()));
        assertFalse(hasEdge(program, "field_write",
                writeValue.getSignature() + "::receiver",
                leafValue.getSignature()));
        assertFalse(program.edges.stream().anyMatch(edge ->
                String.valueOf(edge.get("fromCell")).contains("#field:")
                        || String.valueOf(edge.get("toCell"))
                        .contains("#field:")));
    }

    private static SootMethod buildNestedReceiverConsumer(
            SootClass owner, SootClass failure,
            SootMethod failureConstructor, SootClass rootType,
            SootClass middleType, SootClass leafType,
            SootField rootMiddle, SootField middleLeaf,
            SootField leafValue) {
        SootMethod method = new SootMethod("consumeNested",
                Collections.singletonList(RefType.v(rootType.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local root = local(body, "root", RefType.v(rootType.getName()));
        Local middle = local(body, "middle",
                RefType.v(middleType.getName()));
        Local leaf = local(body, "leaf", RefType.v(leafType.getName()));
        Local value = local(body, "value", IntType.v());
        Local exception = local(body, "failure", RefType.v(failure.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(root,
                Jimple.v().newParameterRef((RefType) root.getType(), 0)));
        body.getUnits().add(Jimple.v().newAssignStmt(middle,
                Jimple.v().newInstanceFieldRef(root, rootMiddle.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(leaf,
                Jimple.v().newInstanceFieldRef(middle, middleLeaf.makeRef())));
        body.getUnits().add(Jimple.v().newAssignStmt(value,
                Jimple.v().newInstanceFieldRef(leaf, leafValue.makeRef())));
        Unit normalReturn = Jimple.v().newReturnVoidStmt();
        body.getUnits().add(Jimple.v().newIfStmt(
                Jimple.v().newLeExpr(value, IntConstant.v(0)), normalReturn));
        body.getUnits().add(Jimple.v().newAssignStmt(exception,
                Jimple.v().newNewExpr(RefType.v(failure.getName()))));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newSpecialInvokeExpr(exception,
                        failureConstructor.makeRef())));
        body.getUnits().add(Jimple.v().newThrowStmt(exception));
        body.getUnits().add(normalReturn);
        return method;
    }

    private static SootMethod buildNestedReceiverCaller(
            SootClass owner, SootMethod consume, SootClass rootType,
            SootField rootField) {
        SootMethod method = new SootMethod("componentEntry",
                Collections.emptyList(), VoidType.v(),
                Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local root = local(body, "root", RefType.v(rootType.getName()));
        body.getUnits().add(Jimple.v().newAssignStmt(root,
                Jimple.v().newStaticFieldRef(rootField.makeRef())));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newStaticInvokeExpr(consume.makeRef(), root)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod buildInstanceFieldWriter(
            SootClass owner, String name, SootClass receiverType,
            SootClass valueType, SootField field) {
        SootMethod method = new SootMethod(name,
                Arrays.asList(RefType.v(receiverType.getName()),
                        RefType.v(valueType.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = local(body, "receiver",
                RefType.v(receiverType.getName()));
        Local value = local(body, "value", RefType.v(valueType.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newParameterRef((RefType) receiver.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef((RefType) value.getType(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef()),
                value));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static SootMethod buildIntFieldWriter(
            SootClass owner, SootClass receiverType, SootField field) {
        SootMethod method = new SootMethod("writeValue",
                Arrays.asList(RefType.v(receiverType.getName()), IntType.v()),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local receiver = local(body, "receiver",
                RefType.v(receiverType.getName()));
        Local value = local(body, "input", IntType.v());
        body.getUnits().add(Jimple.v().newIdentityStmt(receiver,
                Jimple.v().newParameterRef((RefType) receiver.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(value,
                Jimple.v().newParameterRef(IntType.v(), 1)));
        body.getUnits().add(Jimple.v().newAssignStmt(
                Jimple.v().newInstanceFieldRef(receiver, field.makeRef()),
                value));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
        return method;
    }

    private static boolean hasEdge(StaticProgram program, String kind,
                                   String from, String to) {
        return program.edges.stream().anyMatch(edge ->
                kind.equals(edge.get("kind"))
                        && from.equals(edge.get("fromCell"))
                        && to.equals(edge.get("toCell")));
    }

    private static SootMethod buildCompute(
            SootClass owner, SootClass map, SootClass node,
            SootMethod get, SootMethod put, SootMethod mutationHelper,
            SootField values,
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
                Jimple.v().newStaticInvokeExpr(mutationHelper.makeRef(),
                        mapLocal, keyLocal, replacementLocal)));
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

    private static SootMethod buildMapMutationHelper(
            SootClass owner, SootClass map, SootClass node, SootMethod put) {
        SootMethod method = new SootMethod("mutateMap",
                Arrays.asList(RefType.v(map.getName()),
                        RefType.v("java.lang.Object"),
                        RefType.v(node.getName())),
                VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        owner.addMethod(method);
        Body body = Jimple.v().newBody(method);
        method.setActiveBody(body);
        Local mapLocal = local(body, "map", RefType.v(map.getName()));
        Local keyLocal = local(body, "key", RefType.v("java.lang.Object"));
        Local valueLocal = local(body, "value", RefType.v(node.getName()));
        body.getUnits().add(Jimple.v().newIdentityStmt(mapLocal,
                Jimple.v().newParameterRef(mapLocal.getType(), 0)));
        body.getUnits().add(Jimple.v().newIdentityStmt(keyLocal,
                Jimple.v().newParameterRef(keyLocal.getType(), 1)));
        body.getUnits().add(Jimple.v().newIdentityStmt(valueLocal,
                Jimple.v().newParameterRef(valueLocal.getType(), 2)));
        body.getUnits().add(Jimple.v().newInvokeStmt(
                Jimple.v().newInterfaceInvokeExpr(mapLocal, put.makeRef(),
                        keyLocal, valueLocal)));
        body.getUnits().add(Jimple.v().newReturnVoidStmt());
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
        return rpcFixture(false);
    }

    private static RpcFixture rpcFixture(boolean concreteClientInvocation) {
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

        SootMethod clientImplementation = null;
        SootClass concreteClient = null;
        if (concreteClientInvocation) {
            concreteClient = applicationClass(
                    "example.RemoteClient", object);
            concreteClient.addInterface(protocol);
            clientImplementation = new SootMethod("request",
                    Arrays.asList(IntType.v(), IntType.v()), IntType.v(),
                    Modifier.PUBLIC);
            concreteClient.addMethod(clientImplementation);
            Body clientBody = Jimple.v().newBody(clientImplementation);
            clientImplementation.setActiveBody(clientBody);
            Local clientThis = local(clientBody, "this",
                    RefType.v(concreteClient.getName()));
            Local first = local(clientBody, "first", IntType.v());
            Local payload = local(clientBody, "payload", IntType.v());
            clientBody.getUnits().add(Jimple.v().newIdentityStmt(clientThis,
                    Jimple.v().newThisRef(
                            (RefType) clientThis.getType())));
            clientBody.getUnits().add(Jimple.v().newIdentityStmt(first,
                    Jimple.v().newParameterRef(IntType.v(), 0)));
            clientBody.getUnits().add(Jimple.v().newIdentityStmt(payload,
                    Jimple.v().newParameterRef(IntType.v(), 1)));
            clientBody.getUnits().add(Jimple.v().newReturnStmt(payload));
        }

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
        RefType remoteType = RefType.v(concreteClientInvocation
                ? concreteClient.getName() : protocol.getName());
        SootField remote = new SootField("remote",
                remoteType,
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
                remoteType);
        Local inputLocal = local(callerBody, "input", IntType.v());
        Local result = local(callerBody, "result", IntType.v());
        callerBody.getUnits().add(Jimple.v().newAssignStmt(remoteLocal,
                Jimple.v().newStaticFieldRef(remote.makeRef())));
        callerBody.getUnits().add(Jimple.v().newAssignStmt(inputLocal,
                Jimple.v().newStaticFieldRef(input.makeRef())));
        callerBody.getUnits().add(Jimple.v().newAssignStmt(result,
                concreteClientInvocation
                        ? Jimple.v().newVirtualInvokeExpr(remoteLocal,
                        clientImplementation.makeRef(), IntConstant.v(0),
                        inputLocal)
                        : Jimple.v().newInterfaceInvokeExpr(remoteLocal,
                        client.makeRef(), IntConstant.v(0), inputLocal)));
        callerBody.getUnits().add(Jimple.v().newReturnStmt(result));
        return new RpcFixture(client, clientImplementation, server, failure);
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
        private final SootMethod clientImplementation;
        private final SootMethod server;
        private final SootClass failure;

        private RpcFixture(SootMethod client,
                           SootMethod clientImplementation,
                           SootMethod server, SootClass failure) {
            this.client = client;
            this.clientImplementation = clientImplementation;
            this.server = server;
            this.failure = failure;
        }
    }
}
