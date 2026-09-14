package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;

import org.junit.Test;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * A capture site is declared on exactly one consumer region.
 *
 * <p>A site inside a helper lies inside every selected region whose code
 * reaches it, and each of them declared the port. The value crosses the wire
 * once, so the attach files it on one of them -- the innermost live
 * occurrence that declares it -- and every other declaring occurrence was
 * then reported at IMPORT as PLANNED_HANDOFF_NOT_REPRODUCED. On hdfs-17899
 * bug2 that is {@code resp.block-key-id} and
 * {@code resp.block-key-expiry-date}, declared both by the per-call region
 * rooted at {@code PBHelper.convert(BlockKeyProto)} and by the loop-body
 * region rooted at the enclosing {@code convert(ExportedBlockKeysProto)}:
 * 18 handoff events, every one naming the per-call region, and 12
 * not-reproduced rows, every one on the loop-body region.</p>
 *
 * <p>The plan now says what the attach does. H is (portId, consumer
 * occurrence, k-th attach, element path), so two consumers for one wire
 * value would be two variables for one value.</p>
 */
public class OneCaptureSiteOneConsumerTest {
    private static final String INNER = "<a.PBHelper: a.Key convert(a.KeyProto)>";
    private static final String OUTER =
            "<a.PBHelper: a.Keys convert(a.KeysProto)>";
    private static final String PORT = "XCH.1.resp.block-key-id";

    /** The region whose own root is the capture's method keeps it. */
    @Test
    public void onlyTheInnermostSelectedRegionDeclaresTheSite()
            throws Exception {
        List<Map<String, Object>> plans = new ArrayList<>();
        plans.add(plan("REGION.inner", INNER, PORT, "IN", INNER));
        plans.add(plan("REGION.outer", OUTER, PORT, "IN", INNER));

        retain(plans);

        assertTrue("the per-call region keeps its own site",
                plans.get(0).containsKey(CommunicationHandoffSpec.FIELD));
        assertEquals("the enclosing region declares it no longer",
                null, plans.get(1).get(CommunicationHandoffSpec.FIELD));
    }

    /** With no inner region selected, the enclosing one keeps it. */
    @Test
    public void anUncontestedSiteStaysWhereItIs() throws Exception {
        List<Map<String, Object>> plans = new ArrayList<>();
        plans.add(plan("REGION.outer", OUTER, PORT, "IN", INNER));

        retain(plans);

        assertTrue("nothing inner is selected, so nobody else owns it",
                plans.get(0).containsKey(CommunicationHandoffSpec.FIELD));
    }

    /** An OUT site is the producer's own act and is never moved. */
    @Test
    public void anOutgoingSiteIsNeverReassigned() throws Exception {
        List<Map<String, Object>> plans = new ArrayList<>();
        plans.add(plan("REGION.inner", INNER, PORT, "OUT", INNER));
        plans.add(plan("REGION.outer", OUTER, PORT, "OUT", INNER));

        retain(plans);

        assertTrue(plans.get(0).containsKey(CommunicationHandoffSpec.FIELD));
        assertTrue("an export is not a consumer declaration",
                plans.get(1).containsKey(CommunicationHandoffSpec.FIELD));
    }

    @SuppressWarnings("unchecked")
    private static void retain(List<Map<String, Object>> plans)
            throws Exception {
        Method retain = RuntimeRegionPlanner.class.getDeclaredMethod(
                "retainInnermostCommunicationConsumers", List.class);
        retain.setAccessible(true);
        retain.invoke(null, plans);
    }

    /** One region plan row with one declared communication handoff. */
    private static Map<String, Object> plan(String regionId, String rootMethod,
                                            String portId, String side,
                                            String definitionMethod) {
        Map<String, Object> plan = new LinkedHashMap<>();
        plan.put("regionId", regionId);
        Map<String, Object> selector = new LinkedHashMap<>();
        selector.put("method", rootMethod);
        plan.put("rootSelector", selector);
        Map<String, Object> site = new LinkedHashMap<>();
        site.put(CommunicationCatalogContract.PORT_ID, portId);
        site.put(CommunicationHandoffSpec.SIDE, side);
        site.put(CommunicationCatalogContract.PORT_DEFINITION_METHOD,
                definitionMethod);
        List<Map<String, Object>> sites = new ArrayList<>();
        sites.add(site);
        plan.put(CommunicationHandoffSpec.FIELD, sites);
        return plan;
    }
}
