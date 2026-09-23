package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
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

    /**
     * THE DECLARATION UNION: an occurrence declares what the regions folded
     * into it declare.
     *
     * <p>The hdfs-11741 shape, in miniature: the enclosing skeleton names
     * neither the folded region's method nor its cut, so before this rule
     * the consumer side of the target's own exchange was declared by a
     * region with no occurrence -- it was in no plan row at all -- and the
     * folded region's PUBLISH phase went with it.  Both belong to the
     * occurrence that RAN them, and to no other.</p>
     */
    @Test
    public void anOccurrenceDeclaresWhatFoldedIntoIt() throws Exception {
        RuntimeRegionPlanner.Result activations = RuntimeRegionPlanner
                .planSkeletonGraph(cutSkeletons(), cutEvents(), cutRuntime(),
                        Collections.<RuntimeRegionPlanner.ProtocolEvent>
                                emptyList(), Collections.<String>emptySet());
        RuntimeSelectedRegionFinalizer.Result closure =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        cutGraph(), cutSkeletons(), "test",
                        Arrays.asList(HANDLER, LEAF),
                        activations.runtimeInstances,
                        activations.regionFolds, cutObservations(),
                        StaticScopeMap.empty());

        assertEquals("the folded region has no row: it has no occurrence",
                1, closure.regions.size());
        Map<String, Object> handler = closure.regions.get(0);
        assertEquals(HANDLER_REGION, handler.get("regionId"));
        assertTrue("the methods it ran include the folded region's",
                ((Collection<?>) handler.get("methods")).contains(LEAF));
        assertTrue("the cut the folded region declared is its input",
                declares(handler, "symbolicInputs", PORT_ID));
        assertEquals("and the PUBLISH phase of a method its own skeleton "
                        + "does not name", 1,
                ((Collection<?>) handler.get(
                        "configuredSourcePhaseDeclarations")).size());

        // And both reach the occurrence's plan row, which is what the
        // replay and the composer read.  The bound is the campaign's, and
        // the plan builder refuses to invent one; this fixture declares no
        // loop, so any bound serves.
        String bound = System.getProperty("causynth.loop.default.bound");
        System.setProperty("causynth.loop.default.bound", "8");
        try {
        RuntimeRegionPlanner.Result plan = RuntimeRegionPlanner.plan(
                closure.regions, "test", activations.runtimeInstances,
                cutEvents(), cutRuntime(),
                Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                        emptyList(),
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList(),
                closure.gaps);
        assertEquals(1, plan.regionPlans.size());
        Map<String, Object> row = plan.regionPlans.get(0);
        assertTrue("the consumer side of the cut is on the occurrence that "
                        + "ran it", declares(row, "communicationHandoffs",
                PORT_ID));
        assertEquals("and so is the phase the recording executed there",
                1, ((Collection<?>) row.get("configuredSourcePhases")).size());
        } finally {
            if (bound == null) {
                System.clearProperty("causynth.loop.default.bound");
            } else {
                System.setProperty("causynth.loop.default.bound", bound);
            }
        }
    }

    /** Whether one row's named catalog states a port of this id. */
    private static boolean declares(Map<String, Object> row, String field,
                                    String portId) {
        for (Object entry : (Collection<?>) row.get(field)) {
            if (portId.equals(((Map<?, ?>) entry).get("portId"))) return true;
        }
        return false;
    }

    private static final String HANDLER =
            "<o.a.h.SaslDataTransferServer: void handle()>";
    private static final String LEAF = "<o.a.h.BlockTokenSecretManager: "
            + "byte[] retrieveDataEncryptionKey(int,byte[])>";
    private static final String HANDLER_REGION = "REGION.handler";
    private static final String LEAF_REGION = "REGION.leaf";
    private static final String EXCHANGE =
            "XCH.da84e470-fe7e-3068-b93f-caafeef64a70";
    private static final String PORT_ID = EXCHANGE + ".req.key-id";
    private static final String HANDLER_ADDRESS =
            "wl/dn1#epoch0/region/" + HANDLER_REGION + "/ctx:Root:SASL#1";
    private static final String GUARD_SITE = LEAF + "#u5";
    private static final String PHASE_SITE = LEAF + "#u7";
    private static final String OPERAND = LEAF + "::r1";

    /**
     * The handler's skeleton names its own method only -- the weave stops
     * where a region roots another one -- and the leaf declares the cut and
     * the phase.
     */
    private static List<StaticProgram.RegionRow> cutSkeletons() {
        Map<String, Object> handler = skeleton(HANDLER_REGION, HANDLER,
                Collections.singletonList(HANDLER), false);
        Map<String, Object> leaf = skeleton(LEAF_REGION, LEAF,
                Collections.singletonList(LEAF), false);
        leaf.put("selection", "EXCEPTION_CONTEXT");
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("portId", PORT_ID);
        port.put(RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN");
        port.put("sourceKind",
                RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT);
        port.put("dependencyRole", "VALUE_FRONTIER");
        port.put("name", "key-id");
        port.put("javaType", "int");
        port.put("transport", "HDFS_SASL");
        port.put("direction", "REQUEST");
        port.put("exchangeSiteKey", EXCHANGE);
        port.put("callSiteId", LEAF);
        port.put("handoffLeafPath", PORT_ID);
        port.put("definitionMethod", LEAF);
        port.put("outputCaptureKind", "METHOD_PARAMETER");
        port.put("argumentIndex", 0);
        leaf.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                Collections.singletonList(port));
        Map<String, Object> phase = new LinkedHashMap<>();
        phase.put("schemaVersion", 1);
        phase.put("kind", "CONFIGURED_SOURCE_PHASE_DECLARATION");
        phase.put("authority", "EXACT_STATIC_SOURCE_HOOK_SITE_V1");
        phase.put("phase", "PUBLISH");
        phase.put("sourceId", "SRC.key");
        phase.put("fieldSignature", "<o.a.h.BlockKey: int keyId>");
        phase.put("declarationMethod", LEAF);
        phase.put("declarationUnitIndex", 7);
        phase.put("siteId", PHASE_SITE);
        leaf.put("configuredSourcePhaseDeclarations",
                Collections.singletonList(phase));
        return StaticProgram.regionRows(Arrays.asList(handler, leaf),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    /** The handler opens an occurrence; the leaf folds into it. */
    private static List<RuntimeRegionPlanner.MethodEvent> cutEvents() {
        return Arrays.asList(
                entry(10L, HANDLER, 0L, HANDLER_ADDRESS, false),
                entry(20L, LEAF, 10L, "", true));
    }

    /** The fatal guard the leaf decided, and the hook site it executed. */
    private static List<RuntimeRegionPlanner.RuntimeEvent> cutRuntime() {
        return Arrays.asList(
                new RuntimeRegionPlanner.RuntimeEvent(5L, "BRANCH", LEAF,
                        20L, 0L, GUARD_SITE, "", -1, "", 0, "", Boolean.TRUE,
                        null, "IF", ""),
                new RuntimeRegionPlanner.RuntimeEvent(7L, "CALL_SITE_ENTER",
                        LEAF, 20L, 1L, PHASE_SITE, "<o.a.h.Key: int id()>",
                        -1, "", 0, "", null, null, "", ""));
    }

    /** One exception guard, tagged with the folded region alone. */
    private static List<Map<String, Object>> cutGraph() {
        Map<String, Object> guard = new LinkedHashMap<>();
        guard.put("schemaVersion", 3);
        guard.put("kind", "exception_guard");
        guard.put("transferKind", "GUARD");
        guard.put("fromCell", OPERAND);
        guard.put("toCell", LEAF + "#u5#exception:o.a.h.Invalid");
        guard.put("method", LEAF);
        guard.put("siteId", GUARD_SITE);
        guard.put("unitIndex", 5);
        guard.put("regionIds", Collections.singletonList(LEAF_REGION));
        return new ArrayList<>(Collections.singletonList(guard));
    }

    /** The recording's own statement that the fatal guard was decided. */
    private static List<Map<String, Object>> cutObservations() {
        Map<String, Object> branch = new LinkedHashMap<>();
        branch.put("kind", "BRANCH");
        branch.put("eventSeq", 5L);
        branch.put("method", LEAF);
        branch.put("callId", 20L);
        branch.put("siteId", GUARD_SITE);
        branch.put("outcome", Boolean.TRUE);
        return Collections.singletonList(branch);
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
