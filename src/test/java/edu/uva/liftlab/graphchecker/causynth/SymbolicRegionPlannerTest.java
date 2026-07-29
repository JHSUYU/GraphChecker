package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class SymbolicRegionPlannerTest {
    private static final String METHOD = "<example.Box: int compute()>";
    private static final String FIELD = "<example.Box: int value>";
    private static final String OUTPUT = "<example.Bus: int out>";
    private static final String CONSUMER = "<example.Consumer: int read()>";
    private static final String RECEIVER = METHOD + "::$r0";
    private static final String VALUE = METHOD + "::$i0";
    private static final String OUTER =
            "<example.Factory: void build(int)>";
    private static final String CONSTRUCTOR =
            "<example.Value: void <init>(int)>";
    private static final String OUTER_PARAMETER = OUTER + ".param0:int";
    private static final String CONSTRUCTOR_PARAMETER =
            CONSTRUCTOR + ".param0:int";
    private static final String CONSTRUCTOR_LOCAL = CONSTRUCTOR + "::$i0";
    private static final String CONSTRUCTOR_FIELD =
            "<example.Value: int state>";

    @Test
    public void runtimeSelectionKeepsGuardOnlyExceptionTarget() {
        StaticProgram program = new StaticProgram();
        Map<String, Object> targetGuard = edge("DF.0",
                "exception_guard", "GUARD", "taint_depends_on",
                VALUE, METHOD + "#u9#exception:example.Failure",
                9, "if $i0 == 0 goto return");
        program.edges.add(targetGuard);

        String unobservedMethod = "<example.Unused: void run()>";
        Map<String, Object> unobservedGuard = edge("DF.1",
                "exception_guard", "GUARD", "taint_depends_on",
                unobservedMethod + "::$i0",
                unobservedMethod + "#u2#exception:example.Failure",
                2, "if $i0 == 0 goto return");
        unobservedGuard.put("method", unobservedMethod);
        unobservedGuard.put("siteId", unobservedMethod + "#u2");
        program.edges.add(unobservedGuard);

        SymbolicRegionPlanner.planSelected(program,
                Collections.singleton(METHOD));

        assertEquals(1, program.regions.size());
        Map<String, Object> region = program.regions.get(0);
        assertEquals(METHOD, region.get("rootMethod"));
        assertEquals("EXCEPTION_BACKWARD_CAUSAL_CLOSURE",
                region.get("selection"));
    }

    @Test
    public void onlyFreshReceiverFieldsAreRemovedFromLiveIns() {
        StaticProgram fresh = plan(true);
        assertFalse(String.valueOf(fresh.regions),
                inputCells(fresh).contains(FIELD));
        assertTrue(inputCells(plan(false)).contains(FIELD));
    }

    @Test
    public void outputSliceRetainsNestedConstructorFormalAsDormantPort() {
        StaticProgram program = new StaticProgram();
        Map<String, Object> argument = edge("DF.10", "call_argument",
                "ARGUMENT_BINDING", "value_flow", OUTER_PARAMETER,
                CONSTRUCTOR_PARAMETER, 1, "specialinvoke value.<init>(p0)");
        argument.put("method", OUTER);
        argument.put("siteId", OUTER + "#u1");
        argument.put("invoke", CONSTRUCTOR);
        program.edges.add(argument);

        Map<String, Object> identity = edge("DF.11", "local_def_use",
                "IDENTITY_BINDING", "value_flow", CONSTRUCTOR_PARAMETER,
                CONSTRUCTOR_LOCAL, 0, "$i0 := @parameter0");
        identity.put("method", CONSTRUCTOR);
        identity.put("siteId", CONSTRUCTOR + "#u0");
        identity.put("directCopyKind", "PARAMETER_IDENTITY");
        identity.put("valueFlowAuthority",
                "SOOT_EXACT_PARAMETER_IDENTITY_BINDING_V1");
        program.edges.add(identity);

        Map<String, Object> write = edge("DF.12", "field_write",
                "HEAP_WRITE", "value_flow", CONSTRUCTOR_LOCAL,
                CONSTRUCTOR_FIELD, 3, "this.state = $i0");
        write.put("method", CONSTRUCTOR);
        write.put("siteId", CONSTRUCTOR + "#u3");
        write.put("declaredFieldSignature", CONSTRUCTOR_FIELD);
        program.edges.add(write);

        Map<String, Object> read = edge("DF.13", "field_read",
                "HEAP_READ", "value_flow", CONSTRUCTOR_FIELD,
                CONSUMER + "::$i1", 1, "$i1 = value.state");
        read.put("method", CONSUMER);
        read.put("siteId", CONSUMER + "#u1");
        read.put("declaredFieldSignature", CONSTRUCTOR_FIELD);
        program.edges.add(read);

        SymbolicRegionPlanner.plan(program);

        Map<String, Object> region = region(program, OUTER);
        Map<String, Object> slice = outputSlice(region, CONSTRUCTOR_FIELD);
        String constructorPort = inputPort(region, CONSTRUCTOR_PARAMETER);
        assertFalse("nested constructor formal was not promoted",
                constructorPort.isEmpty());
        assertTrue(strings(slice.get("inputPorts")).contains(
                constructorPort));
        assertTrue(hasBinding(slice, CONSTRUCTOR_PARAMETER,
                constructorPort));
    }

    @Test
    public void sameReceiverFieldReadsShareCanonicalAccessSites() {
        StaticProgram program = multipleFieldReadPlan(RECEIVER, RECEIVER);
        Map<String, Object> input = input(region(program, METHOD), FIELD);
        Map<String, Object> materialization = map(
                input.get("materialization"));

        assertEquals("FIELD_READ", materialization.get("kind"));
        assertEquals(Arrays.asList(METHOD + "#u5", METHOD + "#u7"),
                materialization.get("accessSites"));
        assertFalse(materialization.containsKey("method"));
        assertFalse(materialization.containsKey("unitIndex"));
    }

    @Test
    public void distinctReceiverFieldReadsAreNotMerged() {
        StaticProgram program = multipleFieldReadPlan(
                METHOD + "::$r1", METHOD + "::$r2");
        Map<String, Object> input = input(region(program, METHOD), FIELD);

        assertFalse(input.containsKey("materialization"));
    }

    @Test
    public void staticFieldReadNeedsNoReceiverPair() {
        StaticProgram program = new StaticProgram();
        Map<String, Object> read = edge("DF.30", "field_read",
                "HEAP_READ", "value_flow", FIELD, VALUE, 1,
                "$i0 = <example.Box: int value>");
        read.put("declaredFieldSignature", FIELD);
        read.put("declaredFieldStatic", true);
        program.edges.add(read);
        Map<String, Object> write = edge("DF.31", "field_write",
                "HEAP_WRITE", "value_flow", VALUE, OUTPUT, 2,
                "<example.Bus: int out> = $i0");
        write.put("declaredFieldSignature", OUTPUT);
        program.edges.add(write);
        SymbolicRegionPlanner.plan(program);

        Map<String, Object> materialization = map(input(
                region(program, METHOD), FIELD).get("materialization"));
        assertEquals("FIELD_READ", materialization.get("kind"));
        assertEquals(Collections.singletonList(METHOD + "#u1"),
                materialization.get("accessSites"));
    }

    private static StaticProgram multipleFieldReadPlan(
            String firstReceiver, String secondReceiver) {
        StaticProgram program = new StaticProgram();
        addFieldReadPair(program, "DF.20", "DF.21", firstReceiver,
                METHOD + "::$i5", 5);
        addFieldReadPair(program, "DF.22", "DF.23", secondReceiver,
                METHOD + "::$i7", 7);
        Map<String, Object> write = edge("DF.24", "field_write",
                "HEAP_WRITE", "value_flow", METHOD + "::$i5", OUTPUT,
                8, "<example.Bus: int out> = $i5");
        write.put("declaredFieldSignature", OUTPUT);
        program.edges.add(write);
        Map<String, Object> read = edge("DF.25", "field_read",
                "HEAP_READ", "value_flow", OUTPUT,
                CONSUMER + "::$i0", 0,
                "$i0 = <example.Bus: int out>");
        read.put("method", CONSUMER);
        read.put("siteId", CONSUMER + "#u0");
        read.put("declaredFieldSignature", OUTPUT);
        program.edges.add(read);
        SymbolicRegionPlanner.plan(program);
        return program;
    }

    private static void addFieldReadPair(
            StaticProgram program, String declaredId, String instanceId,
            String receiver, String target, int unitIndex) {
        String unit = target.substring(target.indexOf("::") + 2)
                + " = " + receiver.substring(receiver.indexOf("::") + 2)
                + ".<example.Box: int value>";
        Map<String, Object> declared = edge(declaredId, "field_read",
                "HEAP_READ", "value_flow", FIELD, target, unitIndex, unit);
        declared.put("declaredFieldSignature", FIELD);
        declared.put("declaredFieldStatic", false);
        program.edges.add(declared);

        Map<String, Object> instance = edge(instanceId,
                "instance_field_read", "HEAP_READ", "value_flow",
                receiver + "#field:value", target, unitIndex, unit);
        instance.put("fieldSensitive", true);
        instance.put("objectFromCell", receiver);
        instance.put("objectToCell", target);
        instance.put("fieldPath", "#field:value");
        instance.put("declaredFieldSignature", FIELD);
        program.edges.add(instance);
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
        Map<String, Object> region = region(program, METHOD);
        List<Map<String, Object>> inputs = (List<Map<String, Object>>)
                region.get("symbolicInputs");
        java.util.ArrayList<String> cells = new java.util.ArrayList<>();
        for (Map<String, Object> input : inputs) {
            cells.add(String.valueOf(input.get("cell")));
        }
        return cells;
    }

    private static Map<String, Object> region(
            StaticProgram program, String root) {
        for (Map<String, Object> candidate : program.regions) {
            if (root.equals(candidate.get("rootMethod"))) {
                return candidate;
            }
        }
        throw new AssertionError("missing region rooted at " + root
                + ": " + program.regions);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> outputSlice(
            Map<String, Object> region, String outputCell) {
        for (Map<String, Object> slice
                : (List<Map<String, Object>>) region.get("outputSlices")) {
            if (outputCell.equals(slice.get("outputCell"))) {
                return slice;
            }
        }
        throw new AssertionError("missing output slice for " + outputCell
                + ": " + region);
    }

    @SuppressWarnings("unchecked")
    private static String inputPort(
            Map<String, Object> region, String cell) {
        for (Map<String, Object> input
                : (List<Map<String, Object>>) region.get("symbolicInputs")) {
            if (cell.equals(input.get("cell"))) {
                return String.valueOf(input.get("portId"));
            }
        }
        return "";
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> input(
            Map<String, Object> region, String cell) {
        for (Map<String, Object> input
                : (List<Map<String, Object>>) region.get("symbolicInputs")) {
            if (cell.equals(input.get("cell"))) {
                return input;
            }
        }
        throw new AssertionError("missing input " + cell + ": " + region);
    }

    @SuppressWarnings("unchecked")
    private static Map<String, Object> map(Object value) {
        return value instanceof Map
                ? (Map<String, Object>) value
                : Collections.<String, Object>emptyMap();
    }

    @SuppressWarnings("unchecked")
    private static boolean hasBinding(
            Map<String, Object> slice, String cell, String port) {
        for (Map<String, Object> binding
                : (List<Map<String, Object>>) slice.get("inputBindings")) {
            if (cell.equals(binding.get("dependencyCell"))
                    && port.equals(binding.get("inputPort"))) {
                return true;
            }
        }
        return false;
    }

    @SuppressWarnings("unchecked")
    private static List<String> strings(Object value) {
        return (List<String>) value;
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
