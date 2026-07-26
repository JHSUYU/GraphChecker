package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRegionPlannerTest {
    private static final String METHOD = "<example.Box: int compute()>";
    private static final String FIELD = "<example.Box: int value>";
    private static final String OUTPUT = "<example.Bus: int out>";
    private static final String CONSUMER = "<example.Consumer: int read()>";
    private static final String RECEIVER = METHOD + "::$r0";
    private static final String VALUE = METHOD + "::$i0";

    @Test
    public void onlyFreshReceiverFieldsAreRemovedFromLiveIns() {
        StaticProgram fresh = plan(true);
        assertFalse(String.valueOf(fresh.regions),
                inputCells(fresh).contains(FIELD));
        assertTrue(inputCells(plan(false)).contains(FIELD));
    }

    private static StaticProgram plan(boolean fresh) {
        StaticProgram program = new StaticProgram();
        if (fresh) {
            program.edges.add(edge("DF.0", "local_def_use", "COMPUTE",
                    "taint_depends_on", "new example.Box", RECEIVER, 0,
                    "$r0 = new example.Box"));
        }
        program.edges.add(edge("DF.1", "field_read", "HEAP_READ",
                "value_flow", FIELD, VALUE, 1,
                "$i0 = $r0.<example.Box: int value>"));
        Map<String, Object> receiverRead = edge("DF.2",
                "instance_field_read", "HEAP_READ", "value_flow",
                RECEIVER + "#field:value", VALUE, 1,
                "$i0 = $r0.<example.Box: int value>");
        receiverRead.put("fieldSensitive", true);
        receiverRead.put("objectFromCell", RECEIVER);
        receiverRead.put("objectToCell", VALUE);
        receiverRead.put("fieldPath", "#field:value");
        receiverRead.put("declaredFieldSignature", FIELD);
        program.edges.add(receiverRead);
        Map<String, Object> write = edge("DF.3", "field_write",
                "HEAP_WRITE", "value_flow", VALUE, OUTPUT, 2,
                "<example.Bus: int out> = $i0");
        write.put("declaredFieldSignature", OUTPUT);
        program.edges.add(write);
        Map<String, Object> read = edge("DF.4", "field_read", "HEAP_READ",
                "value_flow", OUTPUT, CONSUMER + "::$i0", 0,
                "$i0 = <example.Bus: int out>");
        read.put("method", CONSUMER);
        read.put("siteId", CONSUMER + "#u0");
        read.put("declaredFieldSignature", OUTPUT);
        program.edges.add(read);
        SymbolicRegionPlanner.plan(program);
        return program;
    }

    private static List<String> inputCells(StaticProgram program) {
        @SuppressWarnings("unchecked")
        Map<String, Object> region = null;
        for (Map<String, Object> candidate : program.regions) {
            if (METHOD.equals(candidate.get("rootMethod"))) {
                region = candidate;
                break;
            }
        }
        assertTrue("missing producer region", region != null);
        List<Map<String, Object>> inputs = (List<Map<String, Object>>)
                region.get("symbolicInputs");
        java.util.ArrayList<String> cells = new java.util.ArrayList<>();
        for (Map<String, Object> input : inputs) {
            cells.add(String.valueOf(input.get("cell")));
        }
        return cells;
    }

    private static Map<String, Object> edge(
            String id, String kind, String transfer, String relation,
            String from, String to, int unitIndex, String unit) {
        Map<String, Object> edge = new LinkedHashMap<>();
        edge.put("schemaVersion", 2);
        edge.put("id", id);
        edge.put("kind", kind);
        edge.put("transferKind", transfer);
        edge.put("semanticMode", "ASSERTABLE");
        edge.put("relation", relation);
        edge.put("fromCell", from);
        edge.put("toCell", to);
        edge.put("method", METHOD);
        edge.put("siteId", METHOD + "#u" + unitIndex);
        edge.put("unitIndex", unitIndex);
        edge.put("unit", unit);
        return edge;
    }
}
