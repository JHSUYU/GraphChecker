package edu.uva.liftlab.graphchecker.causynth;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;
import org.junit.Test;

/**
 * A door woven into a method that is already an execution context, or the
 * target's own method, leaves it that region, and a region holding the
 * failure is its exception context, a door in it or not.  datatransfer-doors
 * wove the pipeline ack's RESPONSE door into
 * {@code BlockReceiver$PacketResponder#run}: re-rooted as
 * an explicit fault entry, its region was renamed and selected as a fault
 * context, and the failure closure found no exception context for
 * BlockReceiver-1448's throw there (FATAL_TARGET_NOT_IN_WINDOW).
 */
public class SymbolicRegionPlannerTest {
    private static final String RUN = "<p.Responder: void run()>";
    private static final String SEND = "<p.Door: void send()>";
    private static final String RECEIVE = "<p.Dispatcher: void receive()>";

    @Test
    public void aDoorKeepsItsMethodsRegionAndItsFailure() {
        StaticProgram program = new StaticProgram();
        program.executionContextAuthorities.put(RUN, "TASK_ENTRY");
        program.edges.add(edge(RUN, RUN + "#exception:java.io.IOException",
                false));
        program.edges.add(edge(RUN, "$z0", true));
        program.edges.add(edge(SEND, "$z0", true));
        program.targetResolved.put("method", RECEIVE);
        program.edges.add(edge(RECEIVE,
                RECEIVE + "#exception:java.io.IOException", false));
        program.edges.add(edge(RECEIVE, "$z0", true));
        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(RUN, SEND, RECEIVE));
        Map<String, Map<String, Object>> byRoot = new LinkedHashMap<>();
        for (Map<String, Object> region : program.regions) {
            byRoot.put((String) region.get("rootMethod"), region);
        }
        Object[][] rows = {
            {RUN, "TASK_ENTRY", "EXCEPTION_CONTEXT"},
            {SEND, SymbolicRegionPlanner.EXPLICIT_FAULT_ENTRY,
                    "EXPLICIT_FAULT_CONTEXT"},
            {RECEIVE, SymbolicRegionPlanner.FAILURE_TARGET_ENTRY,
                    "EXCEPTION_CONTEXT"},
        };
        for (Object[] row : rows) {
            Map<String, Object> region = byRoot.get(row[0]);
            assertEquals(row[0] + " authority", row[1],
                    region.get("rootAuthority"));
            assertEquals(row[0] + " selection", row[2],
                    region.get("selection"));
            assertEquals(row[0] + " address",
                    CausynthStaticFacts.nameId("REGION.", row[1] + "\n"
                            + row[0]), region.get("regionId"));
        }
    }

    private static Map<String, Object> edge(String method, String toCell,
                                            boolean fault) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("method", method);
        edge.put("toCell", toCell);
        edge.put("transferKind", "LOCAL");
        if (fault) edge.put("explicitSymbolicFault", true);
        return edge;
    }
}
