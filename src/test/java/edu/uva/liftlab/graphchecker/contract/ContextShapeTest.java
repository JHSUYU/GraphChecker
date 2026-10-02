package edu.uva.liftlab.graphchecker.contract;

import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;

/**
 * The question {@code (r,c)} at any index: a context's shape over the
 * senders of its anchors, and when two occurrences are the same question.
 */
public class ContextShapeTest {
    private static final Map<String, ContextShape.Stance> SENDERS =
            new HashMap<String, ContextShape.Stance>();
    static {
        // dn0 served balancer's request e1, which the balancer sent under
        // its balance-block request
        SENDERS.put("e1", ContextShape.Stance.ofSend(
                "c/balancer#epoch0|Root:CLIENT/balance-block#3"));
        SENDERS.put("e2", ContextShape.Stance.ofSend(
                "c/balancer#epoch0|Root:CLIENT/balance-block#1"));
        SENDERS.put("e3", ContextShape.Stance.ofSend(
                "c/client#epoch0|Root:CLIENT/checksum#1"));
    }

    @Test
    public void aShapeIsItsAnchorsSendersAndItsRootWithoutCounts() {
        Object[][] rows = {
            {"Anchor:e1@HDFS_SASL/balance-block",
                Arrays.asList("HDFS_SASL/balance-block@c/balancer#epoch0",
                        "Root:CLIENT/balance-block")},
            {"Anchor:e9@HDFS_SASL/x", Arrays.asList(ContextShape.UNKNOWN_HOP)},
            {"Root:DATA_XCEIVER#2", Arrays.asList("Root:DATA_XCEIVER")},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], ContextShape.of(
                    CausalContext.parse((String) row[0]), SENDERS::get));
        }
    }

    @Test
    public void shapesDifferOnlyOnAKnownDifference() {
        Object[][] rows = {
            {"equal", true, Arrays.asList("RPC/a@nn0", "Root:CLIENT/mkdir"),
                Arrays.asList("RPC/a@nn0", "Root:CLIENT/mkdir")},
            {"another sender", false,
                Arrays.asList("RPC/a@nn0", "Root:CLIENT/mkdir"),
                Arrays.asList("RPC/a@nn1", "Root:CLIENT/mkdir")},
            {"an unnamed sender is unknown", true,
                Arrays.asList("RPC/a@nn0", ContextShape.UNKNOWN_HOP),
                Arrays.asList("RPC/a@nn0", "RPC/b@dn1", "Root:TICK")},
            {"a longer chain", false, Arrays.asList("Root:CLIENT"),
                Arrays.asList("RPC/a@nn0", "Root:CLIENT")},
        };
        for (Object[] row : rows) {
            assertEquals((String) row[0], row[1], ContextShape.same(
                    list(row[2]), list(row[3])));
        }
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

    @Test
    public void aRunsOccurrenceAnswersTheDeclaredOneOnAKnownEqualChain() {
        OccurrenceAddress declared = address("c/dn1#epoch0", "REGION.t",
                "Anchor:e2@HDFS_SASL/balance-block", "<a.B: void m()>@0");
        Object[][] rows = {
            {"another turn of the chain's root, another index", true,
                address("c/dn1#epoch0", "REGION.t",
                        "Anchor:e1@HDFS_SASL/balance-block",
                        "<a.B: void m()>@4"), null},
            {"a sender nothing names", false, address("c/dn1#epoch0",
                    "REGION.t", "Anchor:e9@HDFS_SASL/balance-block", ""),
                null},
            {"a declared chain nothing names", false, address(
                    "c/dn1#epoch0", "REGION.t",
                    "Anchor:e9@HDFS_SASL/balance-block", ""),
                Arrays.asList(ContextShape.UNKNOWN_HOP)},
            {"another chain", false, address("c/dn1#epoch0", "REGION.t",
                    "Anchor:e3@HDFS_SASL/balance-block", ""), null},
            {"another node", false, address("c/dn0#epoch0", "REGION.t",
                    "Anchor:e1@HDFS_SASL/balance-block", ""), null},
            {"no chain at all", false, address("c/dn1#epoch0", "REGION.t",
                    "Lost:CLIENT", ""), Arrays.asList("Lost:CLIENT")},
        };
        for (Object[] row : rows) {
            OccurrenceAddress ran = (OccurrenceAddress) row[2];
            List<String> declaredShape = row[3] == null
                    ? ContextShape.of(declared.context(), SENDERS::get)
                    : list(row[3]);
            assertEquals((String) row[0], row[1], ContextShape.answers(ran,
                    declared, ContextShape.of(ran.context(), SENDERS::get),
                    declaredShape));
        }
    }

    private static OccurrenceAddress address(String node, String region,
                                             String context, String index) {
        return OccurrenceAddress.parse(node + "/region/" + region + "/ctx:"
                + context + "/idx:" + index);
    }

    @SuppressWarnings("unchecked")
    private static List<String> list(Object value) {
        return value == null ? Collections.<String>emptyList()
                : (List<String>) value;
    }
}
