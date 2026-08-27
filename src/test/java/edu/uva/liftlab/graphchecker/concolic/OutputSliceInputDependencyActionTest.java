package edu.uva.liftlab.graphchecker.concolic;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * What an output slice's input must have before its producer is demanded.
 *
 * <p>The backward walk asks, for every input of the demanded output member,
 * whether that input has to be chased upstream.  It asked by requiring a
 * declared dependency action, which is the right question for a port the
 * fragment materializes itself and the wrong one for the port a communication
 * cut delivers: README section 3's {@code Resp_in} is an input of the client
 * fragment and no action ever binds it, because the value crossed the cut.
 * {@code ConcolicScheduler.projectSymbolize} already states that exemption
 * over the same ports; this walk was the last place that asked without it, so
 * a demanded member that reads the response died with "no declared dependency
 * action" before any task was written.</p>
 *
 * <p>The exemption is the declared port and nothing else.  A region-minted
 * input with no action is an input this fragment cannot bind at all, and
 * admitting it would publish a relation over inputs the replay never
 * symbolized - so it stays a refusal, and it is refused by name.</p>
 */
public class OutputSliceInputDependencyActionTest {

    private static final String EXCHANGE =
            "XCH.11111111-2222-3333-4444-555555555555";
    private static final String RESPONSE_PORT = EXCHANGE + ".resp";
    private static final String HEAP_PORT = "REGION.P.out.h";
    private static final String HEAP_INPUT = "REGION.P.in.a";
    private static final String UNBOUND_INPUT = "REGION.P.in.z";
    private static final String TARGET_INPUT = "REGION.T.in.k";
    private static final String PRODUCER_OCCURRENCE =
            "cluster/client#epoch0/region/REGION.P#1";
    private static final String TARGET_OCCURRENCE =
            "cluster/target#epoch0/region/REGION.T#1";
    private static final String CLIENT_METHOD = "<C: void call()>";
    private static final String HEAP_EDGE = "RF.heap";

    /**
     * The demanded heap write reads a value the response delivered.  That
     * input crosses the cut, so the walk completes and the producer is
     * scheduled.
     */
    @Test
    public void aDemandedMemberMayReadTheCutsOwnResponse() throws Exception {
        RuntimeWorkflowDiscovery.RankedWorkflow workflow =
                RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                        producerRow(RESPONSE_PORT), targetRow()),
                        (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet());

        assertTrue(String.valueOf(workflow.producerGroups().size()),
                workflow.producerGroups().size() == 1);
    }

    /**
     * A region-minted input with no action is refused, and the refusal names
     * the port so the fragment whose evidence is missing can be found without
     * another campaign.
     */
    @Test
    public void aRegionInputWithNoActionIsRefusedByName() throws Exception {
        try {
            RuntimeWorkflowDiscovery.rankedWorkflow(plans(
                    producerRow(UNBOUND_INPUT), targetRow()),
                    (region, action) -> true, (regionId, closure) -> Collections.<String>emptySet());
            fail("an unbindable output slice input must be refused");
        } catch (java.io.IOException refused) {
            String message = String.valueOf(refused.getMessage());
            assertTrue(message, message.contains(RuntimeWorkflowDiscovery
                    .OUTPUT_SLICE_INPUT_UNMATERIALIZABLE));
            assertTrue(message, message.contains(UNBOUND_INPUT));
            assertTrue(message, message.contains(HEAP_PORT));
        }
    }

    // ---------------------------------------------------------------
    // Fixture: one client fragment whose demanded heap write also reads
    // the given port, and the target that demands that write.
    // ---------------------------------------------------------------

    private static JsonObject producerRow(String extraInput) {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("sourceKey", "cluster/client#epoch0");
        row.addProperty("occurrenceId", PRODUCER_OCCURRENCE);
        row.addProperty("regionId", "REGION.P");
        row.addProperty("relationKey",
                "cluster/client/relation/REGION.P/segment/SEG.p#0");

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.OUTPUT_RELATION.p");
        goal.addProperty("kind", "OUTPUT_RELATION_CLOSURE");
        goal.add("admission", admission());
        JsonArray methods = new JsonArray();
        methods.add(CLIENT_METHOD);
        goal.add("runtimeDefinitionMethods", methods);
        JsonArray symbolize = new JsonArray();
        symbolize.add(inputAction(HEAP_INPUT));
        goal.add("symbolize", symbolize);
        goal.add("branches", new JsonArray());
        JsonArray bindings = new JsonArray();
        bindings.add(heapEdge());
        goal.add("edgeBindings", bindings);
        goal.add("outputClosure", outputClosure(extraInput));
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
        return row;
    }

    private static JsonObject targetRow() {
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion", 3);
        row.addProperty("kind", "CONCOLIC_REGION_PLAN");
        row.addProperty("sourceKey", "cluster/target#epoch0");
        row.addProperty("occurrenceId", TARGET_OCCURRENCE);
        row.addProperty("regionId", "REGION.T");
        row.addProperty("relationKey",
                "cluster/target/relation/REGION.T/segment/SEG.t#0");

        JsonObject goal = new JsonObject();
        goal.addProperty("goalId", "GOAL.TARGET_REACH.t");
        goal.addProperty("kind", "TARGET_REACH_CLOSURE");
        goal.add("admission", admission());
        JsonArray methods = new JsonArray();
        methods.add("<T: void handle()>");
        goal.add("runtimeDefinitionMethods", methods);
        JsonArray symbolize = new JsonArray();
        symbolize.add(inputAction(TARGET_INPUT));
        goal.add("symbolize", symbolize);
        goal.add("branches", new JsonArray());
        JsonArray bindings = new JsonArray();
        bindings.add(heapEdge());
        goal.add("edgeBindings", bindings);
        JsonArray goals = new JsonArray();
        goals.add(goal);
        row.add("closureGoals", goals);
        return row;
    }

    private static JsonObject admission() {
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "READY");
        admission.addProperty("mode", "RUNTIME_FAILURE_CLOSURE");
        admission.add("blockers", new JsonArray());
        return admission;
    }

    private static JsonObject inputAction(String port) {
        JsonObject action = new JsonObject();
        action.addProperty("symbol", port);
        action.addProperty("portId", port);
        action.addProperty("mode", "SYMBOLIC");
        action.addProperty("dependencyRole", "VALUE_FRONTIER");
        return action;
    }

    /** The exact runtime read-from the target's input is demanded through. */
    private static JsonObject heapEdge() {
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("edgeId", HEAP_EDGE);
        edge.addProperty("evidenceKind", "FIELD_ASSIGNMENT_READ_FROM_V1");
        edge.addProperty("correlationAuthority",
                "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1");
        edge.addProperty("fromRegion", "REGION.P");
        edge.addProperty("fromOccurrenceId", PRODUCER_OCCURRENCE);
        edge.addProperty("fromSegmentKey", "SEG.p");
        edge.addProperty("fromSemanticOccurrenceId", 0);
        edge.addProperty("fromOutputPort", HEAP_PORT);
        edge.addProperty("toRegion", "REGION.T");
        edge.addProperty("toOccurrenceId", TARGET_OCCURRENCE);
        edge.addProperty("toSegmentKey", "SEG.t");
        edge.addProperty("toSemanticOccurrenceId", 0);
        edge.addProperty("toInputPort", TARGET_INPUT);
        edge.addProperty("dependencyRole", "VALUE_FRONTIER");
        edge.addProperty("receiverObjectId", 7);
        edge.addProperty("writerEventSeq", 10);
        edge.addProperty("readerEventSeq", 20);
        edge.addProperty("writerLaneId", "1");
        edge.addProperty("readerLaneId", "2");
        edge.addProperty("programOrderRequired", false);
        edge.addProperty("alignment", "ALIGNED");
        return edge;
    }

    private static JsonObject outputClosure(String extraInput) {
        JsonObject producer = new JsonObject();
        producer.addProperty("relationKey",
                "cluster/client/relation/REGION.P/segment/SEG.p#0");
        producer.addProperty("regionId", "REGION.P");

        JsonArray members = new JsonArray();
        members.add(heapMember(extraInput));

        JsonObject closure = new JsonObject();
        closure.addProperty("schemaVersion", 3);
        closure.addProperty("kind", "OUTPUT_CLOSURE_CONTRACT");
        closure.add("producer", producer);
        closure.add("members", members);
        return closure;
    }

    private static JsonObject heapMember(String extraInput) {
        String cell = "<C: int state>";
        JsonObject output = new JsonObject();
        output.addProperty("portId", HEAP_PORT);
        output.addProperty("cell", cell);
        output.addProperty("kind", "HEAP_STATE");
        output.addProperty("javaTypeDescriptor", "I");

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.heap");
        capture.addProperty("captureKind", "REGION_EXIT_FIELD");
        capture.addProperty("outputPort", HEAP_PORT);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        JsonArray fieldPath = new JsonArray();
        fieldPath.add("state");
        capture.add("fieldPath", fieldPath);
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", HEAP_INPUT);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", HEAP_PORT);
        slice.addProperty("outputCell", cell);
        JsonArray inputs = new JsonArray();
        inputs.add(HEAP_INPUT);
        inputs.add(extraInput);
        slice.add("inputPorts", inputs);
        slice.add("sites", new JsonArray());
        slice.add("staticSites", new JsonArray());
        JsonArray methods = new JsonArray();
        methods.add(CLIENT_METHOD);
        slice.add("methods", methods);
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject member = new JsonObject();
        member.add("output", output);
        member.add("slice", slice);
        return member;
    }

    /** The plan rows this fixture states, decoded the way the artifact does. */
    private static java.util.List<RegionInstancePlan> plans(
            JsonObject... rows) {
        java.util.List<RegionInstancePlan> decoded =
                new java.util.ArrayList<>();
        for (JsonObject row : rows) {
            decoded.add(RegionInstancePlan.decode(row));
        }
        return decoded;
    }

}
