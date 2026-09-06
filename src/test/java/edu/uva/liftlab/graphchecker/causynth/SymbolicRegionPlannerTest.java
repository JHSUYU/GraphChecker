package edu.uva.liftlab.graphchecker.causynth;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRegionPlannerTest {
    @Before
    public void resetBefore() {
        soot.G.reset();
    }

    @After
    public void resetAfter() {
        soot.G.reset();
    }

    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";
    private static final String COMMUNICATION =
            "<example.Client: int request()>";
    private static final String WRITER = "<example.Store: void update(int)>";
    private static final String STATE = "<example.Store: int state>";

    @Test
    @SuppressWarnings("unchecked")
    public void targetBoundarySeparatesCommunicationDemand() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, TARGET, "VALUE_PASS", "local", "x",
                "y"));
        program.edges.add(edge(ROOT, COMMUNICATION, "VALUE_PASS", "local",
                "request", "reply"));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                "guard", TARGET + "#u7#exception:Failure"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");
        program.targetResolved.put("method", TARGET);
        Map<String, Object> communication = new LinkedHashMap<>();
        Map<String, Object> producer = new LinkedHashMap<>();
        producer.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                COMMUNICATION);
        communication.put(WireFlowCatalog.PRODUCER, producer);
        program.communicationCallSites.add(communication);

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET, COMMUNICATION));

        Map<String, Object> region = regionContaining(program, COMMUNICATION);
        assertTrue(((List<String>) region.get("methods"))
                .contains(COMMUNICATION));
        List<String> demanded = (List<String>) region.get(
                RuntimeSelectedRegionFinalizer.DEMAND_SCOPE);
        assertTrue(demanded.contains(ROOT));
        assertTrue(demanded.contains(COMMUNICATION));
        assertFalse(demanded.contains(TARGET));
        assertEquals(TARGET,
                regionContaining(program, TARGET).get("rootMethod"));
    }

    @Test
    public void rootsAnUnownedFailureRelevantStateWriter() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(TARGET, "", "HEAP_READ", "field_read",
                STATE, TARGET + "::value"));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                TARGET + "::value", TARGET + "#u7#exception:Failure"));
        program.edges.add(edge(WRITER, "", "HEAP_WRITE", "field_write",
                WRITER + ".param0:int", STATE));
        program.targetResolved.put("method", TARGET);

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(TARGET, WRITER));

        Map<String, Object> writer = regionContaining(program, WRITER);
        assertEquals(SymbolicRegionPlanner.STATE_WRITER_ENTRY,
                writer.get("rootAuthority"));
        assertEquals("STATE_CONTEXT", writer.get("selection"));
        assertEquals(Collections.singletonList(WRITER),
                writer.get("methods"));
    }

    private static Map<String, Object> edge(
            String method, String invoke, String transfer, String kind,
            String from, String to) {
        Map<String, Object> result = new LinkedHashMap<>();
        result.put("schemaVersion", 3);
        result.put("method", method);
        if (!invoke.isEmpty()) {
            result.put("invoke", invoke);
        }
        result.put("transferKind", transfer);
        result.put("kind", kind);
        result.put("fromCell", from);
        result.put("toCell", to);
        return result;
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> regionContaining(
            StaticProgram program, String method) {
        for (Map<String, Object> region : program.regions) {
            if (((java.util.List<String>) region.get("methods"))
                    .contains(method)) {
                return region;
            }
        }
        throw new AssertionError("missing region for " + method);
    }
}
