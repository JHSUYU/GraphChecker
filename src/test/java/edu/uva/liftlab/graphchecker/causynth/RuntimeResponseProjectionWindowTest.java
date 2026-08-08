package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class RuntimeResponseProjectionWindowTest {
    @Test
    public void postReturnSerializerRemainsInsideResponseProjection() {
        Map<String, Object> flow = new LinkedHashMap<>();
        flow.put("producerResultEventSeq", 15L);
        flow.put("callerResultEventSeq", 30L);

        long upper = RuntimeSelectedRegionFinalizer
                .responseProjectionUpperSeq(flow);

        // Event 22 is a serializer read after the server method returned,
        // but before the client received the reconstructed response.
        assertEquals(30L, upper);
        org.junit.Assert.assertTrue(22L < upper);
    }
}
