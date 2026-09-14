package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A consumer keeps the ports it attaches.
 *
 * <p>Lane VM13's shape. {@code XCH....resp.block-key-id} is declared IN on
 * the DataNode region that decodes it ({@code REGION.16ba41cf}, captureKind
 * CALL_RETURN) and OUT on the NameNode region that encodes it
 * ({@code REGION.2392e4b7}, CALL_ARGUMENT) -- so the plan is right about who
 * the consumer is. What dropped it from the consumer's execution task was a
 * filter that kept only ports named by the task's edgeBindings, whose
 * {@code fromOutputPort} / {@code toInputPort} are field-flow ports, never
 * XCH ports. The attach then had no declaration to match and was read as an
 * UNPLANNED_HANDOFF fifteen times, while the exporter was told twenty-nine
 * times that it had not reproduced a handoff an exporter never publishes.</p>
 */
public class HandoffSideIsTheFrontierTest {
    private static final String PORT =
            "XCH.1174244c-0000-0000-0000-6cc5895259bf.resp.block-key-id";

    /** An IN site survives a filter no field-flow edge names. */
    @Test
    public void aConsumerKeepsThePortItAttaches() {
        List<String> ports = retained(handoff(PORT, "IN"));

        assertEquals(1, ports.size());
        assertEquals(PORT, ports.get(0));
    }

    /** An OUT site is still filtered by the selected edges. */
    @Test
    public void anExportIsStillSelectedByItsEdges() {
        assertTrue("no edge names it, so it is not this task's frontier",
                retained(handoff(PORT, "OUT")).isEmpty());
    }

    /** One task row, with one declared handoff and one field-flow edge. */
    private static List<String> retained(JsonObject declared) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.SEED.4dd307c1");
        task.addProperty("goalId", "GOAL.1");
        task.addProperty("goalKind", "REGION_PATH_CLOSURE");
        task.addProperty("regionId", "REGION.16ba41cf");
        task.addProperty("relationKey", "REL.1");
        task.addProperty("sourceKey", "hdfs-17899/target-dn#epoch0");
        task.addProperty("occurrenceId",
                "hdfs-17899/target-dn#epoch0/region/REGION.16ba41cf#1");
        task.addProperty("rootMethod", "<a.B: void run()>");
        task.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", "<a.B: void run()>");
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "hdfs-17899/target-dn#epoch0");
        anchor.addProperty("kind", "INHERITED_CONTEXT");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("branches", new JsonArray());
        task.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        task.add("loopBound", loopBound);

        JsonArray handoffs = new JsonArray();
        handoffs.add(declared);
        task.add("communicationHandoffs", handoffs);

        // One field-flow edge, as a region task carries: its ports are
        // region output/input ports, not the XCH port.
        JsonArray edges = new JsonArray();
        JsonObject edge = new JsonObject();
        edge.addProperty("schemaVersion", 3);
        edge.addProperty("kind", "RUNTIME_FIELD_FLOW");
        edge.addProperty("fromOutputPort", "REGION.16ba41cf.out.ea1e850d");
        edge.addProperty("toInputPort", "REGION.53092d3e.in.43545de8");
        edges.add(edge);
        task.add("edgeBindings", edges);

        // The filter the task builder applies, on the row it applies it to.
        ExecutionTask.retainSelectedCommunicationHandoffs(task, edges);

        List<String> ports = new ArrayList<>();
        for (CommunicationHandoffSpec site
                : ExecutionTask.decode(task).communicationHandoffs()) {
            ports.add(site.portId());
        }
        return ports;
    }

    private static JsonObject handoff(String portId, String side) {
        JsonObject row = new JsonObject();
        row.addProperty("portId", portId);
        row.addProperty("side", side);
        row.addProperty("direction", "RESPONSE");
        row.addProperty("captureKind",
                "IN".equals(side) ? "CALL_RETURN" : "CALL_ARGUMENT");
        row.addProperty("definitionMethod",
                "<org.apache.hadoop.hdfs.protocolPB.PBHelper: "
                        + "org.apache.hadoop.hdfs.security.token.block."
                        + "BlockKey convert(org.apache.hadoop.hdfs.protocol."
                        + "proto.HdfsServerProtos$BlockKeyProto)>");
        row.addProperty("definitionUnitIndex", 2);
        if ("OUT".equals(side)) {
            row.addProperty("argumentIndex", 0);
            row.addProperty("declaredCallee",
                    "<org.apache.hadoop.hdfs.protocol.proto."
                            + "HdfsServerProtos$BlockKeyProto$Builder: "
                            + "Builder setKeyId(int)>");
        } else {
            row.addProperty("declaredCallee",
                    "<org.apache.hadoop.hdfs.protocol.proto."
                            + "HdfsServerProtos$BlockKeyProto: "
                            + "int getKeyId()>");
        }
        row.addProperty("javaType", "int");
        row.addProperty("handoffLeafPath", portId);
        return row;
    }
}
