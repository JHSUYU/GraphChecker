package edu.uva.liftlab.graphchecker.plan;

import edu.uva.liftlab.graphchecker.contract.ActivationRow;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.Frame;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/** IDENTITY-IMPL D: a case declaration is resolved against the seed session. */
public class PlanTest {
    private static final String REGION = "REGION.53092d3e";
    private static final NodeId DN0 = NodeId.parse("hdfs-17897/dn0#epoch0");
    private static final NodeId DN1 = NodeId.parse("hdfs-17897/dn1#epoch0");
    private static final String CHECKSUM =
            "o.a.h.h.p.d.DataXceiver#blockChecksum#31";

    /**
     * The k-th match in SEED order, on the declared component, under the
     * declared api -- and a declaration this recording cannot satisfy is a
     * refusal that says what the seed did hold.
     */
    @Test
    public void aDeclarationNamesTheKthMatchInSeedOrder() {
        List<ActivationRow> seed = new ArrayList<ActivationRow>();
        OccurrenceAddress first = anchored(DN0, 1);
        OccurrenceAddress second = anchored(DN0, 2);
        seed.add(activation(anchored(DN1, 1)));     // another component
        seed.add(activation(tick(DN0)));            // no message started it
        seed.add(activation(first));
        seed.add(activation(second));

        String declared = DN0.render() + "/region/" + REGION
                + "@hdfs-17897/client#epoch0/striped-file-checksum#2";
        assertEquals(second, SelectorResolution.resolve(declared, seed));

        // The daemon tick and the other component are not candidates: one was
        // started by no message, the other ran somewhere else.  So the FIRST
        // match under that api is the one on dn0, not the one on dn1.
        assertEquals(first, SelectorResolution.resolve(
                DN0.render() + "/region/" + REGION
                        + "@hdfs-17897/client#epoch0/striped-file-checksum#1",
                seed));

        // A declaration with no api takes every occurrence of the region on
        // that component, tick included, still in seed order.
        assertEquals(tick(DN0), SelectorResolution.resolve(
                DN0.render() + "/region/" + REGION + "#1", seed));

        // An address that is already resolved passes through untouched, which
        // is what a re-run hands back out of a previous manifest.
        assertEquals(second,
                SelectorResolution.resolve(second.render(), seed));

        // k beyond what the seed holds is a case pointed at an execution this
        // recording does not contain.  It degrades rather than throwing, so
        // DECIDE reports DECLARATION_MISSING out of the artifact.
        OccurrenceAddress absent = SelectorResolution.resolve(
                DN0.render() + "/region/" + REGION + "#9", seed);
        assertTrue(SelectorResolution.unresolved(absent)
                || absent.context().isLost());
        assertEquals(REGION, absent.regionId());
    }

    private static ActivationRow activation(OccurrenceAddress occurrence) {
        return ActivationRow.of("s-seed", occurrence, "task", false, true,
                "main#1");
    }

    private static OccurrenceAddress anchored(NodeId node, int iteration) {
        return OccurrenceAddress.of(node, REGION,
                CausalContext.of("ep-" + node.render() + "-" + iteration,
                        "o.a.h.h.p.ClientProtocol/striped-file-checksum"),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of(CHECKSUM, iteration))));
    }

    private static OccurrenceAddress tick(NodeId node) {
        return OccurrenceAddress.of(node, REGION,
                CausalContext.of(Role.of("BP_SERVICE_ACTOR"), "", 1),
                ExecutionIndex.of(Collections.singletonList(
                        Frame.of(CHECKSUM, 0))));
    }
}
