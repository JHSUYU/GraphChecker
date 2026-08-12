package edu.uva.liftlab.graphchecker.contract;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import org.junit.Test;

import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class OutputCaptureSpecTest {
    private static final String DEFINITION =
            "<wire.Response: model.Key currentKey>";
    private static final String LEAF =
            "<model.KeyBase: int keyId>";

    @Test
    public void nestedFieldWriteSeparatesDefinitionFromPrimitiveLeaf() {
        OutputCaptureSpec spec = OutputCaptureSpec.decodeValidated(
                nestedCapture());

        assertTrue(spec.capturesFieldWriteState());
        assertTrue(spec.nestedFieldWriteState());
        assertEquals(DEFINITION, spec.definitionFieldSignature());
        assertEquals(LEAF, spec.leafFieldSignature());
        assertEquals(LEAF, spec.fieldSignature());
        assertEquals(Arrays.asList("currentKey", "keyId"),
                spec.fieldPath());
    }

    @Test(expected = IllegalArgumentException.class)
    public void nestedFieldWriteRejectsPartialProjectionContract() {
        JsonObject capture = nestedCapture();
        capture.remove("leafFieldSignature");

        OutputCaptureSpec.decodeValidated(capture);
    }

    @Test(expected = IllegalArgumentException.class)
    public void nestedFieldWriteRejectsTruncatedPath() {
        JsonObject capture = nestedCapture();
        JsonArray path = new JsonArray();
        path.add("keyId");
        capture.add("fieldPath", path);

        OutputCaptureSpec.decodeValidated(capture);
    }

    @Test(expected = IllegalArgumentException.class)
    public void nestedFieldWriteRejectsMultiHopProjection() {
        JsonObject capture = nestedCapture();
        JsonArray path = new JsonArray();
        path.add("currentKey");
        path.add("delegate");
        path.add("keyId");
        capture.add("fieldPath", path);

        OutputCaptureSpec.decodeValidated(capture);
    }

    @Test
    public void legacyDirectFieldWriteRemainsUnambiguous() {
        JsonObject capture = nestedCapture();
        capture.remove("definitionFieldSignature");
        capture.remove("leafFieldSignature");
        capture.remove("fieldPath");
        capture.addProperty("outputCell", LEAF);
        capture.addProperty("fieldSignature", LEAF);

        OutputCaptureSpec spec = OutputCaptureSpec.decodeValidated(capture);

        assertFalse(spec.nestedFieldWriteState());
        assertEquals(LEAF, spec.definitionFieldSignature());
        assertEquals(LEAF, spec.leafFieldSignature());
    }

    @Test
    public void atomicMutationSupportIsExactAndArithmeticOnly() {
        JsonObject capture = atomicMutationCapture(
                "<java.util.concurrent.atomic.AtomicInteger: int getAndDecrement()>");
        OutputCaptureSpec spec = OutputCaptureSpec.decodeValidated(capture);

        assertEquals("<java.util.concurrent.atomic.AtomicInteger: int value>",
                spec.atomicArithmeticValueFieldSignature());

        capture.addProperty("declaredCallee",
                "<java.util.concurrent.atomic.AtomicInteger: boolean compareAndSet(int,int)>");
        assertEquals("", OutputCaptureSpec.decodeValidated(capture)
                .atomicArithmeticValueFieldSignature());
    }

    private static JsonObject atomicMutationCapture(String declaredCallee) {
        JsonObject capture = new JsonObject();
        String state = "<example.Owner: java.util.concurrent.atomic.AtomicInteger state>";
        capture.addProperty("captureBindingId", "CAPTURE.atomic-state");
        capture.addProperty("captureKind", OutputCaptureSpec.MUTATION_STATE);
        capture.addProperty("outputPort", "REGION.P.out.atomic-state");
        capture.addProperty("outputCell", state);
        capture.addProperty("fieldSignature", state);
        capture.addProperty("javaType",
                "java.util.concurrent.atomic.AtomicInteger");
        capture.addProperty("definitionMethod", "<example.Owner: void run()>");
        capture.addProperty("definitionUnitIndex", 1);
        capture.addProperty("declaredCallee", declaredCallee);
        capture.addProperty("occurrenceScope",
                OutputCaptureSpec.DEFINITION_INVOCATION_SCOPE);
        capture.addProperty("outputSiteId", "<example.Owner: void run()>#u1");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        return capture;
    }

    private static JsonObject nestedCapture() {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.current-key-id");
        capture.addProperty("captureKind",
                OutputCaptureSpec.FIELD_WRITE_STATE);
        capture.addProperty("outputPort", "REGION.P.out.key-id");
        capture.addProperty("outputCell", LEAF);
        // fieldSignature remains the semantic leaf for compatibility with
        // the canonical output endpoint codec.
        capture.addProperty("fieldSignature", LEAF);
        capture.addProperty("definitionFieldSignature", DEFINITION);
        capture.addProperty("leafFieldSignature", LEAF);
        JsonArray path = new JsonArray();
        path.add("currentKey");
        path.add("keyId");
        capture.add("fieldPath", path);
        capture.addProperty("javaType", "int");
        capture.addProperty("definitionMethod", "<wire.Response: void set()>");
        capture.addProperty("definitionUnitIndex", 4);
        capture.addProperty("outputSiteId", "<wire.Response: void set()>#u4");
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        return capture;
    }
}
