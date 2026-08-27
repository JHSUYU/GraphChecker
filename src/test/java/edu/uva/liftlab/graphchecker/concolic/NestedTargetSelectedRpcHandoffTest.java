package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/** A nested target retains selected RPC topology outside its current leaf. */
public class NestedTargetSelectedRpcHandoffTest {

    private static final String TARGET_OCCURRENCE =
            "cluster/nn#epoch0/region/REGION.target#1";
    private static final String TARGET_METHOD =
            "<NameNode: void compareValues()>";
    private static final String LOCAL_GATE = "REGION.target.in.localGate";
    private static final String SELECTED_EDGE = "RPC.selected.response";
    private static final String UNSELECTED_EDGE = "RPC.unselected.response";
    private static final String SELECTED_PORT =
            "XCH.00000000-0000-3000-8000-000000000001.resp";
    private static final String UNSELECTED_PORT =
            "XCH.00000000-0000-3000-8000-000000000002.resp";

    /**
     * The observed outer branch reads only a NameNode-local gate. The ranked
     * workflow has nevertheless selected one response that was delivered
     * before that branch. It remains task topology and therefore keeps its
     * caller-side ATTACH hook; an unselected response remains absent.
     */
    @Test
    public void localGateFrontierRetainsOnlySelectedResponseAttach() {
        RegionInstancePlan.Goal goal = goal();
        JsonArray actions = one(localGateAction());

        JsonArray retained = ConcolicScheduler.targetInputBindings(goal,
                actions, TARGET_OCCURRENCE,
                Collections.singleton(SELECTED_EDGE));
        ExecutionTask task = ExecutionTask.create(goal, "TASK.target",
                actions, new JsonArray(), retained,
                LoopBoundPolicy.cfgBackedges(
                        LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS),
                true, null);

        assertEquals(1, task.inputActions().all().size());
        assertEquals(LOCAL_GATE, task.inputActions().all().get(0)
                .getAsJsonObject().get("symbol").getAsString());

        assertEquals(1, task.edgeBindings().size());
        assertEquals(SELECTED_EDGE, task.edgeBindings().get(0)
                .getAsJsonObject().get("edgeId").getAsString());

        assertEquals(1, task.communicationHandoffs().size());
        assertFalse(task.communicationHandoffs().get(0).exports());
        assertTrue(task.communicationHandoffs().get(0)
                .attachesCutReturn());
        assertEquals(SELECTED_PORT,
                task.communicationHandoffs().get(0).portId());
    }

    private static RegionInstancePlan.Goal goal() {
        JsonObject plan = new JsonObject();
        plan.addProperty("sourceKey", "cluster/nn#epoch0");
        plan.addProperty("occurrenceId", TARGET_OCCURRENCE);
        plan.addProperty("relationKey",
                "cluster/nn/relation/REGION.target");
        plan.addProperty("regionId", "REGION.target");
        plan.addProperty("targetMethod", TARGET_METHOD);

        JsonArray handoffs = new JsonArray();
        handoffs.add(responseAttach(SELECTED_PORT));
        handoffs.add(responseAttach(UNSELECTED_PORT));
        plan.add(CommunicationHandoffSpec.FIELD, handoffs);

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.target");
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        JsonArray methods = new JsonArray();
        methods.add(TARGET_METHOD);
        goal.add("runtimeDefinitionMethods", methods);
        goal.add("symbolize", one(localGateAction()));
        goal.add("branches", new JsonArray());
        JsonArray edges = new JsonArray();
        edges.add(responseEdge(SELECTED_EDGE, SELECTED_PORT,
                "cluster/dn0#epoch0/region/REGION.producer#1"));
        edges.add(responseEdge(UNSELECTED_EDGE, UNSELECTED_PORT,
                "cluster/dn1#epoch0/region/REGION.producer#1"));
        goal.add("edgeBindings", edges);
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.add("blockers", new JsonArray());
        goal.add("admission", admission);

        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        return RegionInstancePlan.decode(plan).goals().get(0);
    }

    private static JsonObject localGateAction() {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", LOCAL_GATE);
        action.addProperty("portId", LOCAL_GATE);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        return action;
    }

    private static JsonObject responseEdge(String edgeId, String port,
                                           String producerOccurrence) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("direction", "RESPONSE");
        edge.addProperty("fromOccurrenceId", producerOccurrence);
        edge.addProperty("toOccurrenceId", TARGET_OCCURRENCE);
        edge.addProperty("fromOutputPort", port);
        edge.addProperty("toInputPort", port);
        edge.addProperty("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        edge.addProperty("evidenceState", "APPROXIMATE");
        return edge;
    }

    private static JsonObject responseAttach(String port) {
        JsonObject site = new JsonObject();
        site.addProperty("kind", CommunicationHandoffSpec.KIND);
        site.addProperty("role", CommunicationHandoffSpec.ROLE_ATTACH);
        site.addProperty("portId", port);
        site.addProperty("handoffLeafPath", "RETURN");
        site.addProperty("direction", "RESPONSE");
        site.addProperty("javaType", "long");
        site.addProperty("exchangeSiteKey",
                port.substring(0, port.length() - ".resp".length()));
        site.addProperty("definitionMethod", TARGET_METHOD);
        site.addProperty(CommunicationCatalogContract.DECLARED_CALLEE,
                "<DataNodeProtocol: long readValue()>");
        site.addProperty(
                CommunicationCatalogContract.PORT_DEFINITION_UNIT_INDEX,
                port.equals(SELECTED_PORT) ? 10 : 20);
        return site;
    }

    private static JsonArray one(JsonObject value) {
        JsonArray result = new JsonArray();
        result.add(value);
        return result;
    }
}
