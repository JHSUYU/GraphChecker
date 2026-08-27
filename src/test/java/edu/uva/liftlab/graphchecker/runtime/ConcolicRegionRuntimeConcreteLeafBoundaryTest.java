package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import org.junit.Test;

import java.lang.reflect.Method;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A handoff leaf the VM reports concrete still answers its output boundary.
 *
 * <p>HDFS-11741 campaign-takeover-21 admitted 50 balancer dispatches and
 * discarded every one of them.  The occurrence exported all three declared
 * SASL handshake leaves; two of them ({@code keyId}, {@code nonce}) carried
 * symbolic expressions and were paired with the DataNode's attach, while
 * {@code DataEncryptionKey.blockPoolId} is a constant the VM answers
 * {@code NOT_SYMBOLIC} for.  {@code exportLeaf} records that case on purpose
 * -- "a concrete leaf, not a broken symbolic handoff" -- and then the
 * completeness gate refused the row because it carried no expression, so the
 * boundary could never be complete and no dispatch could ever answer the
 * address.</p>
 */
public class ConcolicRegionRuntimeConcreteLeafBoundaryTest {
    private static final String SITE =
            "HANDOFF_BOUND_LEAF:XCH.test:HANDSHAKE/blockPoolId";

    @Test
    public void aConcreteHandoffLeafAnswersItsDemandedBoundary()
            throws Exception {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE.leaf");
        capture.addProperty("outputSiteId", SITE);
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("concreteLeaf", true);
        capture.addProperty("primitiveValue", "BP-1-127.0.0.1-1");

        assertTrue("a concrete leaf is presented evidence",
                successful(spec("HANDOFF_BOUND_LEAF"), capture));

        // The relaxation is scoped to the handoff leaf the VM answered.  A
        // heap write with no expression is still an unobserved boundary.
        assertFalse("only a handoff leaf may answer without an expression",
                successful(spec("FIELD_WRITE_STATE"), capture));

        // And a handoff leaf that recorded neither an expression nor the
        // VM's concrete answer is still unobserved.
        JsonObject silent = new JsonObject();
        silent.addProperty("captureBindingId", "CAPTURE.leaf");
        silent.addProperty("outputSiteId", SITE);
        silent.addProperty("outputOccurrence", 1);
        assertFalse("a guarded capture failure is not a boundary",
                successful(spec("HANDOFF_BOUND_LEAF"), silent));
    }

    private static OutputCaptureSpec spec(String captureKind)
            throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("captureBindingId", "CAPTURE.leaf");
        encoded.addProperty("outputPort", "XCH.test.req.blockPoolId");
        encoded.addProperty("captureKind", captureKind);
        encoded.addProperty("outputCell", "XCH.test.req.blockPoolId");
        encoded.addProperty("javaType", "java.lang.String");
        encoded.addProperty("occurrenceScope", "REGION_ACTIVATION");
        encoded.addProperty("outputSiteId", SITE);
        encoded.addProperty("outputOccurrence", 1);
        Method decode = OutputCaptureSpec.class.getDeclaredMethod(
                "decodeValidated", JsonObject.class);
        decode.setAccessible(true);
        return (OutputCaptureSpec) decode.invoke(null, encoded);
    }

    private static boolean successful(OutputCaptureSpec request,
                                      JsonObject capture) throws Exception {
        Method gate = ConcolicRegionRuntime.class.getDeclaredMethod(
                "successfulExactOutputCapture", OutputCaptureSpec.class,
                JsonObject.class);
        gate.setAccessible(true);
        return (Boolean) gate.invoke(null, request, capture);
    }
}
