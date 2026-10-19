package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;

public class ContextShapeTest {
    private static final Map<String, ContextShape.Stance> SENDERS =
            new HashMap<String, ContextShape.Stance>();
    static {
        SENDERS.put("e1", ContextShape.Stance.ofSend(
                "c/balancer#epoch0|Root:CLIENT/balance-block#3"));
        SENDERS.put("e2", ContextShape.Stance.ofSend(
                "c/balancer#epoch0|Root:CLIENT/balance-block#1"));
        SENDERS.put("e3", ContextShape.Stance.ofSend(
                "c/client#epoch0|Root:CLIENT/checksum#1"));
    }

    @Test
    public void theQuestionIsItsRegionNodeAndContextShapeAtAnyIndex() {
        OccurrenceAddress question = address("c/dn1#epoch0", "REGION.t",
                "Anchor:e2@HDFS_SASL/balance-block", "<a.B: void m()>@0");
        Object[][] rows = {
            {"another request's turn, another index", true,
                address("c/dn1#epoch0", "REGION.t",
                        "Anchor:e1@HDFS_SASL/balance-block",
                        "<a.B: void m()>@4")},
            {"another chain: a client's request", false,
                address("c/dn1#epoch0", "REGION.t",
                        "Anchor:e3@HDFS_SASL/balance-block", "")},
            {"a turn of the node's own daemon", false,
                address("c/dn1#epoch0", "REGION.t", "Root:DATA_XCEIVER#1", "")},
            {"another node", false, address("c/dn0#epoch0", "REGION.t",
                    "Anchor:e2@HDFS_SASL/balance-block", "")},
            {"another region", false, address("c/dn1#epoch0", "REGION.u",
                    "Anchor:e2@HDFS_SASL/balance-block", "")},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], ContextShape.sameQuestion(
                    (OccurrenceAddress) row[2], question,
                    context -> ContextShape.of(context, SENDERS::get)));
        }
    }

    private static OccurrenceAddress address(String node, String region,
                                             String context, String index) {
        return OccurrenceAddress.parse(node + "/region/" + region + "/ctx:"
                + context + "/idx:" + index);
    }
}
