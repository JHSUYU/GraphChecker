package edu.uva.liftlab.graphchecker.runtime;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A row that is not a boundary is not written as one.
 *
 * <p>The application records a named handoff gap and an exchange lifecycle
 * note on the same hook a boundary uses, and states a direction that is
 * deliberately neither {@code SEND} nor {@code RECEIVE} so that neither can
 * be read as a crossing.  The recorder used to write every non-send as
 * {@code RPC_RECEIVE}, which threw that statement away: in the measured HDFS
 * pass nineteen SASL gap rows sat in the trace as receives, kept out of the
 * delivery ledger only by the annotation they carry inside their
 * correlation.  A note now has its own row kind and no consumer can reach it
 * through the delivery stream at all.</p>
 */
public class NonDeliveryTraceRowTest {

    /** A verbatim-shaped SASL export gap of the measured pass. */
    private static final String GAP_CORRELATION =
            "3d0f2c1e:7#stage=EXPORT#reason=RPC_HANDOFF_NOT_SYMBOLIC"
                    + "#count=1#leaf=keyId";

    @Test
    public void onlyASendOrAReceiveIsWrittenAsABoundary() {
        assertEquals("RPC_SEND",
                CausynthTraceRecorder.protocolEventKind("SEND"));
        assertEquals("RPC_RECEIVE",
                CausynthTraceRecorder.protocolEventKind("RECEIVE"));
        // RPC_HANDOFF_GAP and RPC_EXCHANGE_EVENT: the two things an
        // application states when it is not naming a crossing.
        assertEquals(CausynthTraceRecorder.PROTOCOL_NOTE_EVENT,
                CausynthTraceRecorder.protocolEventKind("RPC_HANDOFF_GAP"));
        assertEquals(CausynthTraceRecorder.PROTOCOL_NOTE_EVENT,
                CausynthTraceRecorder.protocolEventKind("RPC_EXCHANGE_EVENT"));
    }

    /**
     * The note row enters no delivery stream, and the same row written the
     * old way does - which is exactly the difference the kind now states.
     */
    @Test
    public void aGapRowCannotBeReadAsADelivery() throws Exception {
        CausynthTraceRecorder.TraceData honest =
                CausynthTraceRecorder.parseTraceLinesForTests(Arrays.asList(
                        boundary(), note()));

        assertEquals(1, honest.protocol.size());
        assertEquals("SEND", honest.protocol.get(0).direction);
        assertEquals("3d0f2c1e:7", honest.protocol.get(0).correlationId);

        CausynthTraceRecorder.TraceData asWrittenBefore =
                CausynthTraceRecorder.parseTraceLinesForTests(
                        Collections.singletonList(
                                note().replace("\"RPC_NOTE\"",
                                        "\"RPC_RECEIVE\"")));
        assertEquals(1, asWrittenBefore.protocol.size());
        assertEquals("RECEIVE",
                asWrittenBefore.protocol.get(0).direction);
        // And it would have been a receive of the exchange itself but for the
        // annotation the correlation carries.
        assertTrue(asWrittenBefore.protocol.get(0).correlationId
                .startsWith("3d0f2c1e:7#"));
    }

    private static String boundary() {
        return "{\"schemaVersion\":3,\"event\":\"RPC_SEND\",\"seq\":11,"
                + "\"transport\":\"HADOOP_SASL\","
                + "\"correlationId\":\"3d0f2c1e:7\","
                + "\"half\":\"REQUEST\","
                + "\"threadName\":\"main\",\"tid\":1,\"callId\":0}";
    }

    private static String note() {
        return "{\"schemaVersion\":3,\"event\":\"RPC_NOTE\","
                + "\"noteKind\":\"RPC_HANDOFF_GAP\",\"seq\":12,"
                + "\"transport\":\"HADOOP_SASL\","
                + "\"correlationId\":\"" + GAP_CORRELATION + "\","
                + "\"half\":\"REQUEST\","
                + "\"threadName\":\"main\",\"tid\":1,\"callId\":0}";
    }
}
