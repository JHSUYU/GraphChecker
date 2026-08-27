package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** Task-local selection of adapter-carried communication leaves. */
public class CommunicationHandoffSpecTest {

    private static final String EXCHANGE =
            "XCH.00000000-0000-3000-8000-000000000001";
    private static final String PARENT = EXCHANGE + ".req.p0";
    private static final String KEY_ID = EXCHANGE + ".req.keyId";
    private static final String NONCE = EXCHANGE + ".req.nonce";
    private static final String RESPONSE_PARENT = EXCHANGE + ".resp";
    private static final String RESPONSE_KEY_ID = RESPONSE_PARENT + ".keyId";

    @Test
    public void directComponentSelectionKeepsOnlyThatExactLeaf() {
        RegionInstancePlan.Goal goal = goal(component(KEY_ID,
                "HANDSHAKE/keyId"), component(NONCE, "HANDSHAKE/nonce"));
        JsonArray edges = new JsonArray();
        JsonObject selected = new JsonObject();
        selected.addProperty("fromOutputPort", KEY_ID);
        edges.add(selected);

        ExecutionTask task = ExecutionTask.create(goal, "TASK.export",
                new JsonArray(), new JsonArray(), edges,
                LoopBoundPolicy.cfgBackedges(8), true, null);

        List<CommunicationHandoffSpec> sites = task.communicationHandoffs();
        assertEquals(1, sites.size());
        assertEquals(KEY_ID, sites.get(0).portId());
        assertEquals("HANDSHAKE/keyId", sites.get(0).leafPath());
        assertEquals(PARENT, sites.get(0).componentOfPortId());
        assertTrue(sites.get(0).component());
        assertTrue(sites.get(0).manualCarrier());
        assertEquals("example.ExportCarrier", sites.get(0).carrierClass());
        assertEquals("keyId", sites.get(0).carrierField());
        assertEquals("I", sites.get(0).carrierDescriptor());
        assertFalse(sites.get(0).exportsCutArgument());
    }

    @Test
    public void selectedStructuredParentKeepsItsDeclaredComponents() {
        RegionInstancePlan.Goal goal = goal(component(KEY_ID,
                "HANDSHAKE/keyId"), component(NONCE, "HANDSHAKE/nonce"));
        JsonArray inputs = new JsonArray();
        JsonObject parent = new JsonObject();
        parent.addProperty("portId", PARENT);
        parent.addProperty("mode", "CONCRETE");
        inputs.add(parent);

        ExecutionTask task = ExecutionTask.create(goal, "TASK.attach",
                inputs, new JsonArray(), new JsonArray(),
                LoopBoundPolicy.cfgBackedges(8), true, null);

        assertEquals(2, task.communicationHandoffs().size());
    }

    @Test
    public void responseFieldPathIsAnEntryReturnExportNotAManualCarrier() {
        JsonObject site = new JsonObject();
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", CommunicationHandoffSpec.ROLE_EXPORT);
        site.addProperty("portId", RESPONSE_KEY_ID);
        site.addProperty("handoffLeafPath", "resp/currentKey/keyId");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", EXCHANGE);
        site.addProperty("componentOfPortId", RESPONSE_PARENT);
        site.addProperty("encodingAuthority",
                "CONFIGURED_RESPONSE_FIELD_PATH_V1");
        site.addProperty("definitionMethod",
                "<example.Server: example.Response getKeys()>");
        JsonArray path = new JsonArray();
        path.add(fieldStep("<example.Response: example.Key currentKey>"));
        path.add(fieldStep("<example.Key: int keyId>"));
        site.add(CommunicationCatalogContract.PORT_HANDOFF_PATH, path);
        JsonObject task = new JsonObject();
        JsonArray sites = new JsonArray();
        sites.add(site);
        task.add(CommunicationHandoffSpec.FIELD, sites);

        CommunicationHandoffSpec decoded =
                CommunicationHandoffSpec.decode(task).get(0);
        assertTrue(decoded.responsePathCarrier());
        assertFalse(decoded.manualCarrier());
        assertTrue(decoded.exportsEntryReturn());
        assertEquals(2, decoded.handoffPath().size());
    }

    private static JsonObject fieldStep(String declaration) {
        JsonObject step = new JsonObject();
        step.addProperty("kind", "FIELD");
        step.addProperty("declaration", declaration);
        return step;
    }

    private static RegionInstancePlan.Goal goal(JsonObject... handoffs) {
        JsonObject plan = new JsonObject();
        plan.addProperty("sourceKey", "test/source#epoch0");
        plan.addProperty("occurrenceId", "test/source#epoch0/region/R#1");
        plan.addProperty("relationKey", "test/source/relation/R");
        plan.addProperty("regionId", "R");
        JsonArray declarations = new JsonArray();
        for (JsonObject handoff : handoffs) declarations.add(handoff);
        plan.add(CommunicationHandoffSpec.FIELD, declarations);

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.1");
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        goal.add("runtimeDefinitionMethods", new JsonArray());
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());
        goal.add("edgeBindings", new JsonArray());
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        goal.add("admission", admission);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        return RegionInstancePlan.decode(plan).goals().get(0);
    }

    private static JsonObject component(String portId, String leafPath) {
        JsonObject site = new JsonObject();
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", CommunicationHandoffSpec.ROLE_EXPORT);
        site.addProperty("portId", portId);
        site.addProperty("handoffLeafPath", leafPath);
        site.addProperty("direction", "REQUEST");
        site.addProperty("javaType", "int");
        site.addProperty("exchangeSiteKey", EXCHANGE);
        site.addProperty("componentOfPortId", PARENT);
        site.addProperty("encodingAuthority", "TEST_ENCODING_V1");
        site.addProperty("manualCarrierClass", "example.ExportCarrier");
        site.addProperty("manualCarrierField",
                portId.endsWith("keyId") ? "keyId" : "nonce");
        site.addProperty("manualCarrierDescriptor",
                portId.endsWith("keyId") ? "I" : "[B");
        return site;
    }
}
