package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.fail;

/** Exact task-local lookup of adapter-owned VM handoff storage. */
public class ConcolicRegionRuntimeManualHandoffTest {

    private static final String CARRIER = "example.ExportedBlockKeys";
    private static final String FIELD = "keyId";
    private static final String DESCRIPTOR = "I";

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

    private static Object runtimeTask(JsonObject encoded) throws Exception {
        Class<?> type = Class.forName(ConcolicRegionRuntime.class.getName()
                + "$RuntimeTask");
        Constructor<?> constructor = type.getDeclaredConstructor(
                ExecutionTask.class);
        constructor.setAccessible(true);
        return constructor.newInstance(ExecutionTask.decode(encoded));
    }

    private static CommunicationHandoffSpec lookup(
            Object task, String carrierClass, String field,
            String descriptor, boolean exporting) throws Exception {
        Method method = task.getClass().getDeclaredMethod(
                "manualCommunicationHandoff", String.class, String.class,
                String.class, boolean.class);
        method.setAccessible(true);
        return (CommunicationHandoffSpec) method.invoke(task, carrierClass,
                field, descriptor, exporting);
    }

    private static JsonObject task(JsonObject handoff) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.manual-handoff");
        task.addProperty("goalId", "GOAL.manual-handoff");
        task.addProperty("sourceKey", "test/source#epoch0");
        task.addProperty("occurrenceId",
                "test/source#epoch0/region/R#1");
        task.addProperty("relationKey", "test/source/relation/R");
        task.addProperty("regionId", "R");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", "<example.Service: void run()>");
        selector.addProperty("receiverClass", "example.Service");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "test/source#epoch0");
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
        JsonObject site = new JsonObject();
        site.addProperty("schemaVersion", 1);
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", exporting
                ? CommunicationHandoffSpec.ROLE_EXPORT
                : CommunicationHandoffSpec.ROLE_ATTACH);
        site.addProperty("portId", portId);
        site.addProperty("handoffLeafPath", "SASL/keyId");
        site.addProperty("direction", "REQUEST");
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", "XCH.manual");
        site.addProperty("componentOfPortId", "PORT.parent");
        site.addProperty("encodingAuthority", "TEST_ENCODING_V1");
        site.addProperty("manualCarrierClass", CARRIER);
        site.addProperty("manualCarrierField", FIELD);
        site.addProperty("manualCarrierDescriptor", DESCRIPTOR);
        return site;
    }
}
