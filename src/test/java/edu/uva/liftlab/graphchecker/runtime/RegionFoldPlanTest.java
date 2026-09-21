package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * What the plan says about a region entry the run FOLDED.
 *
 * <p>F1 (paper SS3.1.2, {@code Identity#fold}): a declared region entered
 * synchronously inside an occurrence already running opens NONE of its own.
 * The recording states that on the entry ({@code regionFolded}, no occurrence
 * address) and this plan states its consequence: no activation for the folded
 * region, one fold row naming the occurrence it folded into, and that
 * occurrence owning the calls -- so the sites executed below the folded entry
 * belong to the occurrence that performed them and to no other.</p>
 *
 * <p>The case is hdfs-11741's: a declared key-rotation method entered only
 * inside the NameNode's key-manager tick, which is the recording that killed
 * campaign #5 with DECLARED_INPUT_NEVER_ACTIVATED.</p>
 */
public class RegionFoldPlanTest {

    private static final String TICK =
            "<o.a.h.BlockTokenSecretManager: boolean updateKeys(long)>";
    private static final String DECLARED =
            "<o.a.h.BlockTokenSecretManager: boolean updateKeys()>";
    private static final String BELOW =
            "<o.a.h.BlockTokenSecretManager: void removeExpiredKeys()>";
    private static final String TICK_REGION = "REGION.tick";
    private static final String DECLARED_REGION = "REGION.declared";
    private static final String ADDRESS =
            "wl/nn0#epoch0/region/" + TICK_REGION + "/ctx:Root:TICK#1";

    /**
     * The occurrence that folded the declared region owns it: one activation,
     * no activation of the folded region, and the fold row says where it ran.
     */
    @Test
    public void aFoldedEntryBelongsToTheOccurrenceItFoldedInto() {
        RuntimeRegionPlanner.Result plan = plan();

        assertEquals("one activation: the occurrence that was running",
                1, plan.runtimeInstances.size());
        Map<String, Object> tick = plan.runtimeInstances.get(0);
        assertEquals(TICK_REGION, tick.get("regionId"));

        assertEquals("one fold row, for the declared region",
                1, plan.regionFolds.size());
        Map<String, Object> fold = plan.regionFolds.get(0);
        assertEquals(RuntimeSelectedRegionFinalizer.REGION_FOLD_KIND,
                fold.get("kind"));
        assertEquals(DECLARED_REGION, fold.get("regionId"));
        assertEquals(DECLARED, fold.get("rootMethod"));
        assertEquals("named at the occurrence it folded into",
                ADDRESS, fold.get("occurrenceAddress"));
        assertEquals(TICK_REGION, fold.get("enclosingRegionId"));
        assertEquals(tick.get("activationId"),
                fold.get("enclosingActivationId"));

        // The region -> occurrence table, published where the occurrence is.
        assertEquals(Collections.singletonList(DECLARED_REGION),
                tick.get(RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));

        // And the calls: everything executed below the folded entry is an
        // event of this occurrence, including the frames the enclosing
        // region's own method set does not name.
        Collection<?> calls = (Collection<?>) tick.get("callIds");
        assertTrue("the folded entry itself", calls.contains(20L));
        assertTrue("and what ran below it", calls.contains(30L));
        Collection<?> observed = (Collection<?>) tick.get("observedMethods");
        assertTrue(observed.contains(DECLARED));
        assertTrue(observed.contains(BELOW));
    }

    /**
     * An entry that opened an occurrence of its own is no fold: the same
     * recording without the flag plans two activations and no fold row.
     */
    @Test
    public void anUnfoldedEntryIsStillAnActivationOfItsOwnRegion() {
        RuntimeRegionPlanner.Result plan = RuntimeRegionPlanner
                .planSkeletonGraph(skeletons(), events(false),
                        Collections.<RuntimeRegionPlanner.RuntimeEvent>
                                emptyList(),
                        Collections.<RuntimeRegionPlanner.ProtocolEvent>
                                emptyList(), Collections.<String>emptySet());

        assertEquals(2, plan.runtimeInstances.size());
        assertTrue("nothing folded", plan.regionFolds.isEmpty());
        for (Map<String, Object> activation : plan.runtimeInstances) {
            assertFalse("and no region -> occurrence fold table",
                    activation.containsKey(RuntimeSelectedRegionFinalizer
                            .FOLDED_REGION_IDS));
        }
    }

    private static RuntimeRegionPlanner.Result plan() {
        return RuntimeRegionPlanner.planSkeletonGraph(skeletons(),
                events(true),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList(),
                Collections.<String>emptySet());
    }

    /**
     * The tick's region holds only its own method; the declared region holds
     * the two the tick calls.  That is the shape the fold has to carry: the
     * enclosing skeleton does not name the folded region's methods, so
     * nothing but the fold can give those frames an occurrence.
     */
    private static List<StaticProgram.RegionRow> skeletons() {
        List<Map<String, Object>> rows = new ArrayList<>();
        rows.add(skeleton(TICK_REGION, TICK,
                Collections.singletonList(TICK), false));
        rows.add(skeleton(DECLARED_REGION, DECLARED,
                Arrays.asList(DECLARED, BELOW), true));
        return StaticProgram.regionRows(rows,
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    private static Map<String, Object> skeleton(String regionId, String root,
                                                List<String> methods,
                                                boolean declared) {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
        row.put("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        row.put("regionId", regionId);
        row.put("rootMethod", root);
        row.put("rootAuthority", "STATE_WRITER_ENTRY");
        row.put("anchorMethod", root);
        row.put("anchorMethods", new ArrayList<>(methods));
        row.put("selection", "STATE_CONTEXT");
        row.put("methods", new ArrayList<>(methods));
        if (declared) {
            row.put("declaredInputRoot", true);
        }
        return row;
    }

    /**
     * One recorded tick: it opens an occurrence, calls the declared method,
     * and that call runs one more of the declared region's methods below it.
     *
     * @param folded whether the declared entry was folded -- the recording's
     *               own statement, which is the only thing that differs
     *               between the two cases this fixture serves
     */
    private static List<RuntimeRegionPlanner.MethodEvent> events(
            boolean folded) {
        List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
        methods.add(entry(10L, TICK, 0L, ADDRESS, false));
        methods.add(entry(20L, DECLARED, 10L, folded ? ""
                : "wl/nn0#epoch0/region/" + DECLARED_REGION
                + "/ctx:Root:TICK#1", folded));
        methods.add(entry(30L, BELOW, 20L, "", false));
        return methods;
    }

    private static RuntimeRegionPlanner.MethodEvent entry(
            long callId, String method, long parentCallId, String address,
            boolean folded) {
        return new RuntimeRegionPlanner.MethodEvent(callId, "test", "main",
                1L, method, 1, "o.a.h.BlockTokenSecretManager", callId,
                parentCallId, 0L, 1L, 1L, 0L,
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, true, "", "",
                address, folded);
    }
}
