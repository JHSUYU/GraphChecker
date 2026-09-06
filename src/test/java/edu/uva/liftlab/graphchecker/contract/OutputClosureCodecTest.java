package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;

import static org.junit.Assert.assertEquals;

public class OutputClosureCodecTest {
    @Rule
    public final TemporaryFolder temporary = new TemporaryFolder();

    @Test
    public void selectedOutputProjectionDropsUnrelatedProducerPhase() {
        OutputClosureContract first = singleton(
                "registration", "EDGE.registration",
                "REGION.1.in.registration", "<P: void register()>");
        OutputClosureContract second = singleton(
                "heartbeat", "EDGE.heartbeat",
                "REGION.1.in.heartbeat", "<P: void heartbeat()>");
        OutputClosureContract catalog = OutputClosureCodec.merge(
                Arrays.asList(first, second));

        OutputClosureContract selected = OutputClosureCodec.project(catalog,
                new LinkedHashSet<>(Collections.singletonList(
                        "REGION.1.out.heartbeat")));

        assertEquals(Collections.singleton("REGION.1.out.heartbeat"),
                selected.outputPorts());
        assertEquals(Collections.singleton("REGION.1.in.heartbeat"),
                selected.executionScope().inputPorts());
        assertEquals(Collections.singleton("<P: void heartbeat()>"),
                selected.executionScope().methods());
        assertEquals(Collections.singleton("EDGE.heartbeat"),
                selected.executionScope().causalEdgeIds());
    }

    @Test
    public void mergeIsOrderIndependentForCapturesAndSourceDemands() {
        String port = "REGION.1.out.value";
        String cell = "<P: int value>";
        JsonObject firstSlice = slice(port, cell, "EDGE.first",
                "REGION.1.in.first", "<P: void first()>");
        firstSlice.add("demandedHeapDeclarations",
                strings("<P: int first>"));
        JsonObject secondSlice = slice(port, cell, "EDGE.second",
                "REGION.1.in.second", "<P: void second()>");
        secondSlice.add("demandedHeapDeclarations",
                strings("<P: int second>"));
        OutputClosureContract first = OutputClosureCodec.singleton("REL.1",
                "REGION.1", Collections.<String>emptyList(), port, cell, "HEAP_STATE", "int", firstSlice);
        OutputClosureContract second = OutputClosureCodec.singleton("REL.1",
                "REGION.1", Collections.<String>emptyList(), port, cell, "HEAP_STATE", "int", secondSlice);

        OutputClosureContract forward = OutputClosureCodec.merge(
                Arrays.asList(first, second));
        OutputClosureContract reverse = OutputClosureCodec.merge(
                Arrays.asList(second, first));

        assertEquals(forward.toJson(), reverse.toJson());
        assertEquals(forward.closureFingerprint(),
                reverse.closureFingerprint());
        assertEquals(strings("<P: int first>", "<P: int second>"),
                forward.member(port).slice().getAsJsonArray(
                        "demandedHeapDeclarations"));
    }

    private static OutputClosureContract singleton(
            String field, String edgeId, String input, String method) {
        String port = "REGION.1.out." + field;
        String cell = "<P: int " + field + ">";
        return OutputClosureCodec.singleton("REL.1", "REGION.1", Collections.<String>emptyList(), port, cell, "HEAP_STATE", "int",
                slice(port, cell, edgeId, input, method));
    }

    private static JsonObject slice(
            String port, String cell, String edgeId,
            String input, String method) {
        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", port);
        slice.addProperty("outputCell", cell);
        slice.add("inputPorts", strings(input));
        slice.add("sites", strings(method + "#u1"));
        slice.add("staticSites", new JsonArray());
        slice.add("methods", strings(method));
        slice.add("causalEdgeIds", strings(edgeId));
        slice.add("captureBindingIssues", new JsonArray());

        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + cell);
        capture.addProperty("captureKind",
                OutputCaptureSpec.REGION_EXIT_FIELD);
        capture.addProperty("outputPort", port);
        capture.addProperty("outputCell", cell);
        capture.addProperty("fieldSignature", cell);
        capture.add("fieldPath", strings(cell.substring(
                cell.lastIndexOf(' ') + 1, cell.length() - 1)));
        capture.addProperty("javaType", "int");
        capture.addProperty("accessRootInputPort", input);
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        return slice;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }
}
