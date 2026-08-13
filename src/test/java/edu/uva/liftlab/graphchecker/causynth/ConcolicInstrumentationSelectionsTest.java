package edu.uva.liftlab.graphchecker.causynth;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import org.junit.Test;

import java.lang.reflect.Constructor;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ConcolicInstrumentationSelectionsTest {
    private static final String DEFINITION =
            "<wire.Response: model.Key currentKey>";
    private static final String LEAF =
            "<model.KeyBase: int keyId>";
    private static final String METHOD = "<wire.Response: void set()>";

    @Test
    public void exactHeapSelectionTargetsDefinitionAndCarriesLeafPath()
            throws Exception {
        OutputCaptureSpec spec = nestedCaptureSpec();
        Constructor<ConcolicInstrumentationSelections.ExactHeapOutputCapture>
                constructor = ConcolicInstrumentationSelections
                .ExactHeapOutputCapture.class.getDeclaredConstructor(
                        OutputCaptureSpec.class);
        constructor.setAccessible(true);
        ConcolicInstrumentationSelections.ExactHeapOutputCapture selection =
                constructor.newInstance(spec);

        // CausynthPipeline's existing selector calls fieldSignature(); it
        // must match the actual putfield rather than the projected leaf.
        assertEquals(DEFINITION, selection.fieldSignature());
        assertEquals(DEFINITION, selection.definitionFieldSignature());
        assertEquals(LEAF, selection.leafFieldSignature());
        assertEquals(Arrays.asList("currentKey", "keyId"),
                selection.fieldPath());
        assertTrue(selection.nestedFieldWriteState());
    }

    private static OutputCaptureSpec nestedCaptureSpec() {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.current-key-id");
        capture.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputPort", "REGION.P.out.key-id");
        capture.addProperty("outputCell", LEAF);
        capture.addProperty("fieldSignature", LEAF);
        capture.addProperty("definitionFieldSignature", DEFINITION);
        capture.addProperty("leafFieldSignature", LEAF);
        capture.add("fieldPath", strings("currentKey", "keyId"));
        capture.addProperty("javaType", "int");
        capture.addProperty("definitionMethod", METHOD);
        capture.addProperty("definitionUnitIndex", 4);
        capture.addProperty("outputSiteId", METHOD + "#u4");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);

        JsonObject slice = new JsonObject();
        slice.addProperty("outputPort", "REGION.P.out.key-id");
        slice.addProperty("outputCell", LEAF);
        slice.add("inputPorts", new JsonArray());
        slice.add("sites", strings(METHOD + "#u4"));
        slice.add("staticSites", strings(METHOD + "#u4"));
        slice.add("methods", strings(METHOD));
        slice.add("causalEdgeIds", new JsonArray());
        JsonArray captures = new JsonArray();
        captures.add(capture);
        slice.add("captureBindings", captures);
        slice.add("captureBindingIssues", new JsonArray());

        OutputClosureContract closure = OutputClosureCodec.singleton(
                "REL.REGION.P", "REGION.P", "CONTRACT.TEST",
                "REGION.P.out.key-id", LEAF, "HEAP_STATE", "int", slice);
        return OutputClosureCodec.captureSpecs(closure).get(0);
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }
}
