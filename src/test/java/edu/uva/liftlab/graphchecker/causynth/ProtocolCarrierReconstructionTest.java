package edu.uva.liftlab.graphchecker.causynth;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

public class ProtocolCarrierReconstructionTest {

    @Test
    public void writeInsideDecodeWindowPenetratesToTheResponsePort() {
        ProtocolCarrierReconstruction decode = ProtocolCarrierReconstruction
                .of(Collections.singletonList(responsePort("REGION.c.in.1",
                        7L, 10L, 30L)));

        assertEquals("REGION.c.in.1", decode.responsePortFor(7L, 20L));
        assertEquals("REGION.c.in.1", decode.responsePortFor(7L, 30L));
    }

    @Test
    public void localProductionOutsideTheWindowKeepsItsOwnSlice() {
        ProtocolCarrierReconstruction decode = ProtocolCarrierReconstruction
                .of(Collections.singletonList(responsePort("REGION.c.in.1",
                        7L, 10L, 30L)));

        assertEquals("", decode.responsePortFor(7L, 10L));
        assertEquals("", decode.responsePortFor(7L, 31L));
        assertEquals("", decode.responsePortFor(8L, 20L));
    }

    @Test
    public void untrustedOrIncompleteResponseDeclaresNoWindow() {
        Map<String, Object> untrusted = responsePort("REGION.c.in.1", 7L,
                10L, 30L);
        untrusted.put("authority", "GUESSED");
        Map<String, Object> unordered = responsePort("REGION.c.in.2", 7L,
                30L, 10L);

        assertTrue(ProtocolCarrierReconstruction.of(
                Arrays.asList(untrusted, unordered)).isEmpty());
    }

    @Test
    public void overlappingDecodeWindowsFailClosed() {
        List<Map<String, Object>> ports = Arrays.asList(
                responsePort("REGION.c.in.1", 7L, 10L, 30L),
                responsePort("REGION.c.in.2", 7L, 15L, 40L));
        ProtocolCarrierReconstruction decode =
                ProtocolCarrierReconstruction.of(ports);

        try {
            decode.responsePortFor(7L, 20L);
            fail("overlapping response windows must not be resolved");
        } catch (IllegalStateException expected) {
            assertTrue(expected.getMessage().contains("overlap"));
        }
    }

    @Test
    public void markingRecordsAGapUntilAProjectionBindsTheCarrier() {
        ProtocolCarrierReconstruction decode = ProtocolCarrierReconstruction
                .of(Collections.singletonList(responsePort("REGION.c.in.1",
                        7L, 10L, 30L)));
        Map<String, Object> unprojected = new LinkedHashMap<>();
        Map<String, Object> projected = new LinkedHashMap<>();

        ProtocolCarrierReconstruction.mark(unprojected,
                decode.reconstructionOf(7L, 20L), false);
        ProtocolCarrierReconstruction.mark(projected,
                decode.reconstructionOf(7L, 20L), true);

        assertEquals("REGION.c.in.1",
                ProtocolCarrierReconstruction.responsePort(unprojected));
        assertEquals("example.response",
                unprojected.get(ProtocolCarrierReconstruction.MAPPING_ID));
        assertEquals(ProtocolCarrierReconstruction.MISSING_PROJECTION,
                unprojected.get(
                        ProtocolCarrierReconstruction.PROJECTION_GAP));
        assertEquals(null, projected.get(
                ProtocolCarrierReconstruction.PROJECTION_GAP));
    }

    private static Map<String, Object> responsePort(
            String portId, long rootCallId, long sendEventSeq,
            long callerResultEventSeq) {
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("portId", portId);
        port.put("sourceKind", "PROTOCOL_INPUT");
        port.put("protocolDirection", "RESPONSE");
        port.put("authority", "TRUSTED_CONFIGURED_RPC_MAPPING_V1");
        port.put("mappingId", "example.response");
        port.put("toRootCallId", rootCallId);
        port.put("sendEventSeq", sendEventSeq);
        port.put("callerResultEventSeq", callerResultEventSeq);
        return port;
    }
}
