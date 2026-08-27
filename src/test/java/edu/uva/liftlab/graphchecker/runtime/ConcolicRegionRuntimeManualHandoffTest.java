package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.RpcExpressionHandoff;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/** Exact task-local lookup of adapter-owned VM handoff storage. */
public class ConcolicRegionRuntimeManualHandoffTest {

    private static final String CARRIER = Carrier.class.getName();
    private static final String FIELD = "keyId";
    private static final String DESCRIPTOR = "I";
    private static final long HANDLE = (37L << 32) | 11L;
    private static final String TARGET_PORT = "TARGET.local";
    private static final String TARGET_SOURCE = "TARGET.LOCAL";
    private static final String TARGET_FIELD =
            "<example.Target: long localValue>";
    private static final String TARGET_ROOT =
            "<example.Service: void run()>";
    private static final String SOURCE_HOOK_CALLEE =
            "<example.SourceHook: boolean symbolize()>";
    private static final int TARGET_SOURCE_UNIT = 1;
    private static final Gson GSON = new Gson();

    @Before
    public void resetRuntime() {
        ConcolicRegionRuntime.resetForTests();
        FakeVm.EXPORTS.set(0);
        FakeVm.ATTACHES.set(0);
    }

    @After
    public void clearRuntime() {
        ConcolicRegionRuntime.resetForTests();
    }

    @Test
    public void manualHandleRecoversExactProducerExecutionBeforeAttach()
            throws Exception {
        installFakeEngine();
        beginLineageSession(71L);
        Object producer = runtimeTask(task(
                "TASK.manual-producer", "source/producer#epoch0/region/P#7",
                handoff("PORT.keyId", true)));
        Object consumer = runtimeTask(task(
                "TASK.manual-consumer", "source/consumer#epoch0/region/C#3",
                handoff("PORT.keyId", false)));
        Carrier value = new Carrier();

        Object producerActive = activate(producer, 101L);
        ConcolicRegionRuntime.HandoffResult exported =
                ConcolicRegionRuntime.exportSymbolicLeaf(value, CARRIER,
                        FIELD, DESCRIPTOR);
        assertTrue(exported.toString(), exported.ok());
        deactivate(producerActive);

        Object consumerActive = activate(consumer, 102L);
        ConcolicRegionRuntime.HandoffResult received =
                ConcolicRegionRuntime.receiveSymbolicLeaf(value, CARRIER,
                        FIELD, DESCRIPTOR, exported.handle());

        assertTrue(received.toString(), received.ok());
        assertEquals(1, FakeVm.ATTACHES.get());
        assertEquals(0, handoffGaps(consumerActive).size());
        List<JsonObject> events = vmHandoffs(consumerActive);
        assertEquals(1, events.size());
        assertEquals("TASK.manual-producer", events.get(0).get(
                "producerTaskId").getAsString());
        assertEquals("source/producer#epoch0/region/P#7",
                events.get(0).get("producerOccurrenceId").getAsString());
    }

    @Test
    public void unknownAndPriorSessionHandlesNeverReachNativeAttach()
            throws Exception {
        installFakeEngine();
        beginLineageSession(72L);
        Object consumer = runtimeTask(task(
                "TASK.manual-consumer", "source/consumer#epoch0/region/C#3",
                handoff("PORT.keyId", false)));
        Object consumerActive = activate(consumer, 103L);

        ConcolicRegionRuntime.HandoffResult unknown =
                ConcolicRegionRuntime.receiveSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR, HANDLE + 1L);
        assertFalse(unknown.ok());
        assertEquals(RpcExpressionHandoff.UNKNOWN_HANDLE, unknown.status());
        assertEquals(0, FakeVm.ATTACHES.get());
        assertEquals(1, handoffGaps(consumerActive).size());
        deactivate(consumerActive);

        Object producer = runtimeTask(task(
                "TASK.manual-producer", "source/producer#epoch0/region/P#7",
                handoff("PORT.keyId", true)));
        Object producerActive = activate(producer, 104L);
        ConcolicRegionRuntime.HandoffResult exported =
                ConcolicRegionRuntime.exportSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR);
        assertTrue(exported.ok());
        deactivate(producerActive);

        beginLineageSession(73L);
        consumerActive = activate(consumer, 105L);
        ConcolicRegionRuntime.HandoffResult priorSession =
                ConcolicRegionRuntime.receiveSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR, exported.handle());
        assertFalse(priorSession.ok());
        assertEquals(0, FakeVm.ATTACHES.get());
        assertEquals(1, handoffGaps(consumerActive).size());
    }

    @Test
    public void conflictingProducerClaimPoisonsHandleDeterministically()
            throws Exception {
        installFakeEngine();
        beginLineageSession(74L);
        Object producerA = runtimeTask(task(
                "TASK.manual-producer-a", "source/a#epoch0/region/P#1",
                handoff("PORT.keyId", true)));
        Object producerB = runtimeTask(task(
                "TASK.manual-producer-b", "source/b#epoch0/region/P#1",
                handoff("PORT.keyId", true)));
        Object consumer = runtimeTask(task(
                "TASK.manual-consumer", "source/c#epoch0/region/C#1",
                handoff("PORT.keyId", false)));

        Object activeA = activate(producerA, 106L);
        assertTrue(ConcolicRegionRuntime.exportSymbolicLeaf(new Carrier(),
                CARRIER, FIELD, DESCRIPTOR).ok());
        deactivate(activeA);

        Object activeB = activate(producerB, 107L);
        ConcolicRegionRuntime.HandoffResult conflict =
                ConcolicRegionRuntime.exportSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR);
        assertFalse(conflict.ok());
        assertEquals(RpcExpressionHandoff.MISSING_METADATA,
                conflict.status());
        deactivate(activeB);

        Object consumerActive = activate(consumer, 108L);
        ConcolicRegionRuntime.HandoffResult received =
                ConcolicRegionRuntime.receiveSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR, HANDLE);
        assertFalse(received.ok());
        assertEquals(RpcExpressionHandoff.MISSING_METADATA,
                received.status());
        assertEquals(0, FakeVm.ATTACHES.get());
        assertEquals(1, handoffGaps(consumerActive).size());
    }

    @Test
    public void undeclaredManualStorageNeverReachesTheNativeBroker()
            throws Exception {
        installFakeEngine();
        beginLineageSession(75L);
        JsonObject encoded = task(handoff("PORT.unused", true));
        encoded.add(CommunicationHandoffSpec.FIELD, new JsonArray());
        Object active = activate(runtimeTask(encoded), 109L);

        ConcolicRegionRuntime.HandoffResult exported =
                ConcolicRegionRuntime.exportSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR);
        ConcolicRegionRuntime.HandoffResult received =
                ConcolicRegionRuntime.receiveSymbolicLeaf(new Carrier(),
                        CARRIER, FIELD, DESCRIPTOR, HANDLE);

        assertFalse(exported.ok());
        assertEquals(RpcExpressionHandoff.MISSING_METADATA,
                exported.status());
        assertFalse(received.ok());
        assertEquals(RpcExpressionHandoff.MISSING_METADATA,
                received.status());
        assertEquals(0, FakeVm.EXPORTS.get());
        assertEquals(0, FakeVm.ATTACHES.get());
        assertEquals(2, handoffGaps(active).size());
    }

    @Test
    public void exactRoleAndStorageResolveTheOnlyDeclaredManualComponent()
            throws Exception {
        Object task = runtimeTask(task(handoff("PORT.keyId", true)));

        CommunicationHandoffSpec resolved = lookup(task, CARRIER, FIELD,
                DESCRIPTOR, true);
        assertEquals("PORT.keyId", resolved.portId());
        assertNull(lookup(task, CARRIER, FIELD, DESCRIPTOR, false));
        assertNull(lookup(task, CARRIER, "nonce", DESCRIPTOR, true));
        assertNull(lookup(task, CARRIER, FIELD, "J", true));
    }

    @Test
    public void duplicateRoleAndStorageAreRejected() throws Exception {
        JsonObject encoded = task(handoff("PORT.keyId.first", true));
        encoded.getAsJsonArray(CommunicationHandoffSpec.FIELD).add(
                handoff("PORT.keyId.second", true));

        try {
            runtimeTask(encoded);
            fail("duplicate manual handoff storage must be rejected");
        } catch (InvocationTargetException failure) {
            if (!(failure.getCause() instanceof IllegalArgumentException)) {
                throw failure;
            }
        }
    }

    @Test
    public void targetTaskLoadsLocalSourceBesideResponseAttach()
            throws Exception {
        JsonObject encoded = task(responseAttach("XCH.remote.resp"));
        addTargetInputs(encoded, TARGET_FIELD);
        addTargetSource(encoded);
        addTargetSourceAssignment(encoded);

        Object loaded = runtimeTask(encoded);

        CommunicationHandoffSpec attached = lookup(loaded, CARRIER, FIELD,
                DESCRIPTOR, false);
        assertEquals("XCH.remote.resp", attached.portId());
    }

    private static Object runtimeTask(JsonObject encoded) throws Exception {
        Class<?> type = Class.forName(ConcolicRegionRuntime.class.getName()
                + "$RuntimeTask");
        Constructor<?> constructor = type.getDeclaredConstructor(
                ExecutionTask.class);
        constructor.setAccessible(true);
        return constructor.newInstance(ExecutionTask.decode(encoded));
    }

    @SuppressWarnings("unchecked")
    private static CommunicationHandoffSpec lookup(
            Object task, String carrierClass, String field,
            String descriptor, boolean exporting) throws Exception {
        Method key = task.getClass().getDeclaredMethod("handoffCarrierKey",
                String.class, String.class, String.class, boolean.class);
        key.setAccessible(true);
        Field carriers = task.getClass().getDeclaredField(
                "manualCommunicationHandoffs");
        carriers.setAccessible(true);
        return ((Map<String, CommunicationHandoffSpec>) carriers.get(task))
                .get((String) key.invoke(null, carrierClass, field,
                        descriptor, exporting));
    }

    private static void assertIllegalTask(JsonObject encoded)
            throws Exception {
        try {
            runtimeTask(encoded);
            fail("malformed target-local source task must be rejected");
        } catch (InvocationTargetException failure) {
            if (!(failure.getCause() instanceof IllegalArgumentException)) {
                throw failure;
            }
        }
    }

    private static void addTargetInputs(
            JsonObject task, String localField) {
        JsonObject local = new JsonObject();
        local.addProperty("mode", "CONCRETE");
        local.addProperty("portId", TARGET_PORT);
        local.addProperty("symbol", TARGET_PORT);
        local.addProperty("location", "HEAP_OBJECT_FIELD");
        local.addProperty("bindingMode", "FIELD_ACCESS");
        local.addProperty("javaType", "long");
        local.addProperty("accessFieldSignature", localField);
        task.getAsJsonArray("inputActions").add(local);

        JsonObject remote = new JsonObject();
        remote.addProperty("mode", "CONCRETE");
        remote.addProperty("portId", "XCH.remote.resp");
        remote.addProperty("symbol", "XCH.remote.resp");
        remote.addProperty("location", "CALL_RETURN");
        remote.addProperty("bindingMode", "LOCAL_DEFINITION");
        remote.addProperty("javaType", "long");
        remote.addProperty("symbolicDemand",
                "EXACT_INCOMING_COMPOSITION");
        remote.addProperty("selectedIncomingEdgeId", "EDGE.remote");
        task.getAsJsonArray("inputActions").add(remote);
    }

    private static void addTargetSource(JsonObject task) {
        // Wave 3: a task declares mint SITES only; the selected-source
        // row that used to travel beside them is gone.
        JsonArray declared = new JsonArray();
        declared.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH,
                TARGET_SOURCE, TARGET_FIELD, TARGET_ROOT,
                TARGET_SOURCE_UNIT));
        ConfiguredSourcePhaseContract.Declaration declaration =
                ConfiguredSourcePhaseContract.declarationsOf(declared).get(0);
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                declaration, task.get("occurrenceId").getAsString(), 1, 1L,
                1L, 1L, SOURCE_HOOK_CALLEE,
                Collections.singletonList(1L)));
        task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
    }

    private static void addTargetSourceAssignment(JsonObject task) {
        String phaseId = targetSourcePhaseId(task);
        JsonObject assignment = new JsonObject();
        assignment.addProperty("modelAssignmentKey", "MODEL.target.local");
        assignment.addProperty("engineSymbol",
                "M_J_field_SRC.example_example/Target");
        assignment.addProperty("inputSymbol", "SOURCE_PHASE:" + phaseId);
        assignment.addProperty("configuredSourcePhaseId", phaseId);
        assignment.addProperty("configuredSourceId", TARGET_SOURCE);
        assignment.addProperty("configuredSourceFieldSignature",
                TARGET_FIELD);
        assignment.addProperty("valueType", "INT");
        assignment.addProperty("value", "9");
        JsonArray assignments = new JsonArray();
        assignments.add(assignment);
        task.add("modelAssignments", assignments);
    }

    private static String targetSourcePhaseId(JsonObject task) {
        return ConfiguredSourcePhaseContract.phaseId(
                task.get("occurrenceId").getAsString(),
                ConfiguredSourcePhaseContract.siteId(
                        TARGET_ROOT, TARGET_SOURCE_UNIT),
                ConfiguredSourcePhaseContract.Phase.PUBLISH, 1);
    }

    private static JsonObject task(JsonObject handoff) {
        return task("TASK.manual-handoff",
                "test/source#epoch0/region/R#1", handoff);
    }

    private static JsonObject task(String taskId, String occurrenceId,
                                   JsonObject handoff) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", taskId);
        task.addProperty("goalId", "GOAL.manual-handoff");
        String sourceKey = occurrenceId.substring(0,
                occurrenceId.indexOf("/region/"));
        task.addProperty("sourceKey", sourceKey);
        task.addProperty("occurrenceId", occurrenceId);
        task.addProperty("relationKey", "test/source/relation/R");
        task.addProperty("regionId", "R");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", "<example.Service: void run()>");
        selector.addProperty("receiverClass", "example.Service");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", sourceKey);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        JsonArray handoffs = new JsonArray();
        handoffs.add(handoff);
        task.add(CommunicationHandoffSpec.FIELD, handoffs);
        return task;
    }

    private static JsonObject handoff(String portId, boolean exporting) {
        return handoff(portId, exporting, "REQUEST");
    }

    private static JsonObject responseAttach(String portId) {
        return handoff(portId, false, "RESPONSE");
    }

    private static JsonObject handoff(
            String portId, boolean exporting, String direction) {
        JsonObject site = new JsonObject();
        site.addProperty("schemaVersion", 1);
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", exporting
                ? CommunicationHandoffSpec.ROLE_EXPORT
                : CommunicationHandoffSpec.ROLE_ATTACH);
        site.addProperty("portId", portId);
        site.addProperty("handoffLeafPath", "SASL/keyId");
        site.addProperty("direction", direction);
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", "XCH.manual");
        site.addProperty("componentOfPortId", "PORT.parent");
        site.addProperty("encodingAuthority", "TEST_ENCODING_V1");
        site.addProperty("manualCarrierClass", CARRIER);
        site.addProperty("manualCarrierField", FIELD);
        site.addProperty("manualCarrierDescriptor", DESCRIPTOR);
        return site;
    }

    private static Object activate(Object task, long token) throws Exception {
        Class<?> activeType = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$ActiveRegion");
        Constructor<?> constructor = activeType.getDeclaredConstructor(
                long.class, task.getClass(), Object.class, Thread.class);
        constructor.setAccessible(true);
        Object active = constructor.newInstance(token, task, new Object(),
                Thread.currentThread());
        activeRegions().put(token, active);
        currentToken().set(token);
        return active;
    }

    private static void deactivate(Object active) throws Exception {
        Field token = active.getClass().getDeclaredField("token");
        token.setAccessible(true);
        activeRegions().remove(token.getLong(active));
        currentToken().remove();
    }

    @SuppressWarnings("unchecked")
    private static Map<Long, Object> activeRegions() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField("ACTIVE");
        field.setAccessible(true);
        return (Map<Long, Object>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static ThreadLocal<Long> currentToken() throws Exception {
        Field field = ConcolicRegionRuntime.class.getDeclaredField(
                "CURRENT_TOKEN");
        field.setAccessible(true);
        return (ThreadLocal<Long>) field.get(null);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> handoffGaps(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("rpcHandoffGaps");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    @SuppressWarnings("unchecked")
    private static List<JsonObject> vmHandoffs(Object active)
            throws Exception {
        Field field = active.getClass().getDeclaredField("vmHandoffEvents");
        field.setAccessible(true);
        return (List<JsonObject>) field.get(active);
    }

    private static void beginLineageSession(long sessionId) throws Exception {
        Method reset = ConcolicRegionRuntime.class.getDeclaredMethod(
                "resetManualHandoffLineageSession", long.class);
        reset.setAccessible(true);
        reset.invoke(null, sessionId);
        Field session = ConcolicRegionRuntime.class.getDeclaredField(
                "workloadSessionId");
        session.setAccessible(true);
        session.setLong(null, sessionId);
    }

    private static void installFakeEngine() throws Exception {
        Object engine = newEngine();
        bind(engine, "export", fake("exportExpression", Object.class,
                String.class, String.class, String.class, long[].class));
        bind(engine, "attach", fake("attachExpression", Object.class,
                String.class, String.class, String.class, long.class,
                long[].class));
        bind(engine, "getFieldExpression", fake("fieldExpression",
                Object.class, String.class, String.class, String.class,
                Object.class));
        bind(engine, "pausePathCondition", fake("pause"));
        bind(engine, "resumePathCondition", fake("resume"));
        install(engine);
    }

    /** A stock EngineApi with every VM method absent, for selective binding. */
    private static Object newEngine() throws Exception {
        Constructor<?> constructor = Class.forName(
                ConcolicRegionRuntime.class.getName() + "$EngineApi")
                .getDeclaredConstructor();
        constructor.setAccessible(true);
        return constructor.newInstance();
    }

    private static void bind(Object engine, String name, Method target)
            throws Exception {
        Field field = engine.getClass().getDeclaredField(name);
        field.setAccessible(true);
        field.set(engine, target);
    }

    private static void install(Object engine) throws Exception {
        Field engineApi = ConcolicRegionRuntime.class.getDeclaredField(
                "engineApi");
        engineApi.setAccessible(true);
        engineApi.set(null, engine);
    }

    private static Method fake(String name, Class<?>... parameters)
            throws Exception {
        return FakeVm.class.getDeclaredMethod(name, parameters);
    }

    public static final class FakeVm {
        private static final AtomicInteger EXPORTS = new AtomicInteger();
        private static final AtomicInteger ATTACHES = new AtomicInteger();

        public static void pause() { }
        public static void resume() { }

        public static long exportExpression(Object owner,
                                            String declaringClass,
                                            String fieldName,
                                            String descriptor,
                                            long[] eventOut) {
            EXPORTS.incrementAndGet();
            // README RPC-1: the VM names the export's own ledger event.
            if (eventOut != null && eventOut.length > 0) eventOut[0] = 90L;
            return HANDLE;
        }

        public static long attachExpression(Object owner,
                                            String declaringClass,
                                            String fieldName,
                                            String descriptor, long handle,
                                            long[] eventOut) {
            // Both endpoints: the export it consumed, and this exact attach.
            if (eventOut != null && eventOut.length > 0) {
                eventOut[0] = 92L + ATTACHES.get();
            }
            ATTACHES.incrementAndGet();
            return 91L;
        }

        public static String fieldExpression(Object owner,
                                             String declaringClass,
                                             String fieldName,
                                             String descriptor,
                                             Object value) {
            return "{\"expression\":{\"_type\":\"SymbolExpression\","
                    + "\"_java_type\":\"I\",\"_exp\":\"MANUAL.X\"}}";
        }
    }

    private static final class Carrier {
        @SuppressWarnings("unused")
        private int keyId = 7;
    }
}
