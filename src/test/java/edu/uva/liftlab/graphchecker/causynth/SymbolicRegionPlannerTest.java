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
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");
        program.executionContextAuthorities.put(ASYNC, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET, REMOTE, ASYNC));

        assertEquals(2, program.regions.size());
        Map<String, Object> target = regionContaining(program, TARGET);
        assertEquals(3, target.get("schemaVersion"));
        assertEquals("REGION_SKELETON", target.get("kind"));
        assertEquals(ROOT, target.get("rootMethod"));
        assertEquals("TASK_ENTRY", target.get("rootAuthority"));
        assertEquals(TARGET, target.get("anchorMethod"));
        assertEquals(Arrays.asList(ROOT, TARGET), target.get("methods"));
        assertFalse(target.containsKey("symbolicInputs"));
        assertFalse(target.containsKey("outputs"));
        assertFalse(target.containsKey("branchPolicies"));
        assertFalse(target.containsKey("fieldPath"));
        Map<String, Object> async = regionContaining(program, ASYNC);
        assertEquals("AUTHORITY_ENVELOPE", async.get("selection"));
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
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");
        program.executionContextAuthorities.put(TARGET, "RPC_HANDLER");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET));

        assertEquals(2, program.regions.size());
        assertEquals(ROOT, program.regions.get(0).get("rootMethod"));
        assertEquals(ROOT, program.regions.get(0).get("anchorMethod"));
        assertEquals(TARGET, program.regions.get(1).get("rootMethod"));
        assertEquals(TARGET, program.regions.get(1).get("anchorMethod"));
        assertEquals("PROTOCOL_CONTEXT",
                program.regions.get(0).get("selection"));
        assertEquals("PROTOCOL_CONTEXT",
                program.regions.get(1).get("selection"));
    }

    @Test
    public void executionScopeIsRootedAtTheDemandingAnchor() {
        String anchor = "<example.Demand: void act()>";
        String needed = "<example.Needed: void helper()>";
        String aside = "<example.Aside: void other()>";
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, anchor, "VALUE_PASS", "call", "arg",
                "param"));
        program.edges.add(edge(ROOT, aside, "VALUE_PASS", "call", "arg",
                "param"));
        program.edges.add(edge(anchor, needed, "VALUE_PASS", "call", "arg",
                "param"));
        program.edges.add(edge(anchor, "", "GUARD", "exception_guard",
                "guard", anchor + "#u7#exception:Failure"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, anchor, needed, aside));

        assertEquals(1, program.regions.size());
        assertEquals("EXCEPTION_CONTEXT",
                program.regions.get(0).get("selection"));
        assertEquals(anchor, program.regions.get(0).get("anchorMethod"));
        // The region still contains the context -- its outputs are produced
        // there -- but only what the anchor reaches is demanded, so the other
        // thing the outer frame does buys no path here.
        assertEquals(Arrays.asList(aside, anchor, needed, ROOT),
                program.regions.get(0).get("methods"));
        assertEquals(Arrays.asList(anchor, needed, ROOT),
                program.regions.get(0).get(
                        RuntimeSelectedRegionFinalizer.DEMAND_SCOPE));
    }

    @Test
    public void configuredClientStubCallEndsTheExecutionScope() {
        String stub = "<example.Transport: void send(java.lang.String)>";
        String internal = "<example.Transport: void frame()>";
        String shared = "<example.Codec: void encode()>";
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, "", "GUARD", "exception_guard",
                "guard", ROOT + "#u7#exception:Failure"));
        program.edges.add(edge(ROOT, stub, "VALUE_PASS", "call", "arg",
                "param"));
        program.edges.add(edge(ROOT, shared, "VALUE_PASS", "call", "arg",
                "param"));
        program.edges.add(edge(stub, internal, "VALUE_PASS", "call", "arg",
                "param"));
        program.edges.add(edge(stub, shared, "VALUE_PASS", "call", "arg",
                "param"));
        Map<String, Object> protocol = edge(ROOT, TARGET,
                "PROTOCOL_TRANSFER", "rpc", "request", "parameter");
        protocol.put("protocolStubMappingId", "example.transport");
        protocol.put("protocolClientStub", stub);
        protocol.put("protocolServerStub", TARGET);
        program.edges.add(protocol);
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, stub, internal, shared, TARGET));

        assertEquals(1, program.regions.size());
        // The region still contains the transport methods; they are simply
        // not what it has to decide.  A callee the anchors also reach without
        // crossing the boundary stays demanded.
        assertEquals(Arrays.asList(shared, ROOT, internal, stub),
                program.regions.get(0).get("methods"));
        assertEquals(Arrays.asList(shared, ROOT),
                program.regions.get(0).get(
                        RuntimeSelectedRegionFinalizer.DEMAND_SCOPE));
    }

    @Test
    public void concreteDynamicDispatchTargetJoinsOwningRegion() {
        String declared = "<example.Factory: example.Value create()>";
        String concrete = "<example.FactoryImpl: example.Value create()>";
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, declared, "DYNAMIC_DISPATCH",
                "dispatch_activation", ROOT + "#u3",
                concrete + ".activation"));
        program.edges.add(edge(concrete, "", "GUARD", "exception_guard",
                "guard", concrete + "#u7#exception:Failure"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, concrete));

        assertEquals(1, program.regions.size());
        assertEquals(Arrays.asList(concrete, ROOT),
                program.regions.get(0).get("methods"));
        assertEquals(concrete, program.regions.get(0).get("anchorMethod"));
    }

    @Test
    public void nestedProtocolEndpointStaysInOwningContext() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, TARGET, "VALUE_PASS", "call",
                "request", "parameter"));
        Map<String, Object> protocol = edge(REMOTE, TARGET,
                "PROTOCOL_TRANSFER", "rpc", "request", "parameter");
        protocol.put("protocolStubMappingId", "example.nested");
        protocol.put("protocolClientStub", REMOTE);
        protocol.put("protocolServerStub", TARGET);
        protocol.put("protocolServerContext", "NESTED_CALL");
        program.edges.add(protocol);
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET, REMOTE));

        assertEquals(1, program.regions.size());
        assertEquals(ROOT, program.regions.get(0).get("rootMethod"));
        assertEquals(Arrays.asList(ROOT, TARGET),
                program.regions.get(0).get("methods"));
        assertEquals("PROTOCOL_CONTEXT",
                program.regions.get(0).get("selection"));
    }

    @Test
    public void disconnectedNestedEndpointBecomesRuntimeBoundFragment() {
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                "guard", TARGET + "#u7#exception:Failure"));
        program.nestedContextEndpoints.add(TARGET);
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, TARGET));

        assertEquals(2, program.regions.size());
        assertEquals(ROOT, program.regions.get(0).get("rootMethod"));
        assertEquals("AUTHORITY_ENVELOPE",
                program.regions.get(0).get("selection"));
        assertEquals(TARGET, program.regions.get(1).get("rootMethod"));
        assertEquals("NESTED_CALL",
                program.regions.get(1).get("rootAuthority"));
        assertEquals("EXCEPTION_CONTEXT",
                program.regions.get(1).get("selection"));
        assertEquals("STATIC_NESTED_CONTEXT_FRAGMENT",
                program.regions.get(1).get("planningMode"));
    }

    @Test
    public void constructorIsFoldedIntoOwningExecutionContext() {
        String constructor = "<example.State: void <init>(int)>";
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, "", "GUARD", "exception_guard",
                "guard", ROOT + "#u7#exception:Failure"));
        program.edges.add(edge(ROOT, constructor, "VALUE_PASS", "call",
                "arg", "param"));
        program.edges.add(edge(constructor, "", "HEAP_WRITE",
                "field_write", "value", "<example.State: int value>"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, constructor));

        assertEquals(1, program.regions.size());
        assertEquals(ROOT, program.regions.get(0).get("rootMethod"));
        assertTrue(((java.util.List<?>) program.regions.get(0).get("methods"))
                .contains(constructor));
        assertEquals(ROOT, program.regions.get(0).get("anchorMethod"));
    }

    @Test
    public void constructorStateAloneDoesNotAdmitARegion() {
        String constructor = "<example.State: void <init>(int)>";
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(ROOT, constructor, "VALUE_PASS", "call",
                "arg", "param"));
        program.edges.add(edge(constructor, "", "HEAP_WRITE",
                "field_write", "value", "<example.State: int value>"));
        program.executionContextAuthorities.put(ROOT, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(ROOT, constructor));

        assertEquals(1, program.regions.size());
        assertEquals("AUTHORITY_ENVELOPE",
                program.regions.get(0).get("selection"));
    }

    @Test
    public void onlyFailureSlicedStateAdmitsStateRegions() {
        String writer = "<example.Writer: void run()>";
        String noise = "<example.Noise: void run()>";
        String demanded = "<example.State: int key>";
        String unrelated = "<example.State: int metric>";
        String local = TARGET + "::key";
        StaticProgram program = new StaticProgram();
        program.edges.add(edge(TARGET, "", "HEAP_READ", "field_read",
                demanded, local));
        program.edges.add(edge(TARGET, "", "GUARD", "exception_guard",
                local, TARGET + "#u7#exception:Failure"));
        program.edges.add(edge(writer, "", "HEAP_WRITE", "field_write",
                writer + "::value", demanded));
        program.edges.add(edge(noise, "", "HEAP_WRITE", "field_write",
                noise + "::value", unrelated));
        program.executionContextAuthorities.put(TARGET, "TASK_ENTRY");
        program.executionContextAuthorities.put(writer, "TASK_ENTRY");
        program.executionContextAuthorities.put(noise, "TASK_ENTRY");

        SymbolicRegionPlanner.planSelectedSkeleton(program,
                Arrays.asList(TARGET, writer, noise));

        assertEquals("EXCEPTION_CONTEXT",
                regionRootedAt(program, TARGET).get("selection"));
        assertEquals("STATE_CONTEXT",
                regionRootedAt(program, writer).get("selection"));
        assertEquals("AUTHORITY_ENVELOPE",
                regionRootedAt(program, noise).get("selection"));
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

    private static Map<String, Object> regionRootedAt(
            StaticProgram program, String method) {
        for (Map<String, Object> region : program.regions) {
            if (method.equals(region.get("rootMethod"))) {
                return region;
            }
        }
        throw new AssertionError("missing region rooted at " + method);
    }
}
