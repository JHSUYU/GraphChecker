package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;

/** The target scheduler retains only selected, schedulable component edges. */
public class SelectedComponentTargetBindingTest {

    private static final String OCCURRENCE = "node/region/R.target#1";
    private static final String COMPONENT = "XCH.test.req.keyId";
    private static final String PARENT = "XCH.test.req.p0";

    @Test
    public void selectedComponentUsesSchedulingAdmissionOnly() {
        JsonObject component = protocol("RPC.component", COMPONENT);
        component.addProperty(
                CommunicationCatalogContract.PORT_COMPONENT_OF, PARENT);
        component.addProperty(
                CommunicationCatalogContract.PORT_HANDOFF_LEAF_PATH,
                "HANDSHAKE/keyId");
        component.addProperty(
                CommunicationCatalogContract.PORT_ENCODING_AUTHORITY,
                "TEST_ENCODING_V1");
        JsonObject ordinary = protocol("RPC.ordinary", PARENT);

        RegionInstancePlan.Goal goal = goal(component, ordinary);
        JsonArray actions = new JsonArray();
        JsonObject parentAction = new JsonObject();
        parentAction.addProperty("symbol", PARENT);
        actions.add(parentAction);

        JsonArray retained = ConcolicScheduler.targetInputBindings(goal,
                actions, OCCURRENCE, Collections.singleton("RPC.component"));

        assertEquals(1, retained.size());
        assertEquals("RPC.component", retained.get(0).getAsJsonObject()
                .get("edgeId").getAsString());
    }

    private static JsonObject protocol(String edgeId, String port) {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
        edge.addProperty("edgeId", edgeId);
        edge.addProperty("fromOccurrenceId", "node/region/R.source#1");
        edge.addProperty("toOccurrenceId", OCCURRENCE);
        edge.addProperty("fromOutputPort", port);
        edge.addProperty("toInputPort", port);
        edge.addProperty("correlationAuthority",
                AutomaticRegionEdge.TRACED_EXCHANGE_AUTHORITY);
        edge.addProperty("evidenceState", "APPROXIMATE");
        return edge;
    }

    private static RegionInstancePlan.Goal goal(JsonObject... bindings) {
        JsonObject plan = new JsonObject();
        plan.addProperty("sourceKey", "node");
        plan.addProperty("occurrenceId", OCCURRENCE);
        plan.addProperty("relationKey", "node/relation/R.target");
        plan.addProperty("regionId", "R.target");
        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.target");
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        goal.add("runtimeDefinitionMethods", new JsonArray());
        goal.add("symbolize", new JsonArray());
        goal.add("branches", new JsonArray());
        JsonArray edges = new JsonArray();
        for (JsonObject binding : bindings) edges.add(binding);
        goal.add("edgeBindings", edges);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        plan.add("closureGoals", goals);
        return RegionInstancePlan.decode(plan).goals().get(0);
    }
}
