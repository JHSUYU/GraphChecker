package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRegionPlannerTest {
    private static final String ROOT = "<example.Root: void run()>";
    private static final String TARGET = "<example.Target: void fail()>";
    private static final String REMOTE = "<example.Remote: void send()>";
    private static final String ASYNC = "<example.Worker: void run()>";

    @Test
    public void partitionsMethodsAndStopsBeforeStatePlanning() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, TARGET, "VALUE_PASS", "local", "x",
                "y"));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                "guard", TARGET + "#u7#exception:Failure"));
        program.edges.add(edge(TARGET, REMOTE, "PROTOCOL_TRANSFER", "rpc",
                "request", "parameter"));
        program.edges.add(edge(TARGET, ASYNC, "DYNAMIC_DISPATCH", "dispatch",
                "task", "receiver"));

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET, REMOTE, ASYNC));

        assertEquals(3, program.regions.size());
        Map<String, Object> target = regionContaining(program, TARGET);
        assertEquals(3, target.get("schemaVersion"));
        assertEquals("REGION_SKELETON", target.get("kind"));
        assertEquals(ROOT, target.get("rootMethod"));
        assertEquals(TARGET, target.get("anchorMethod"));
        assertEquals(Arrays.asList(ROOT, TARGET), target.get("methods"));
        assertFalse(target.containsKey("symbolicInputs"));
        assertFalse(target.containsKey("outputs"));
        assertFalse(target.containsKey("branchPolicies"));
        assertFalse(target.containsKey("fieldPath"));
        assertTrue(program.regionEdges.isEmpty());
    }

    @Test
    public void configuredProtocolMethodsBecomeRuntimeSelectionAnchors() {
        StaticProgram program = new StaticProgram();
        Map<String, Object> protocol = edge(ROOT, TARGET,
                "PROTOCOL_TRANSFER", "rpc", "request", "parameter");
        protocol.put("protocolStubMappingId", "example.rpc");
        protocol.put("protocolClientStub", ROOT);
        protocol.put("protocolServerStub", TARGET);
        program.edges.add(protocol);

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET));

        assertEquals(2, program.regions.size());
        assertEquals(ROOT, program.regions.get(0).get("anchorMethod"));
        assertEquals(TARGET, program.regions.get(1).get("anchorMethod"));
        assertEquals("PROTOCOL_COMPONENT",
                program.regions.get(0).get("selection"));
        assertEquals("PROTOCOL_COMPONENT",
                program.regions.get(1).get("selection"));
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
