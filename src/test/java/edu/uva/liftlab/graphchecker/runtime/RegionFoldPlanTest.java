package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

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
 * <p>The fold rule (IDENTITY §1, {@code Identity#fold}): a region entered
 * synchronously inside an occurrence already running opens NONE of its own.
 * The recording states that on the entry ({@code regionFolded}, no occurrence
 * address) and this plan states its consequence: no activation for the folded
 * region, and the occurrence it folded into naming it and owning the calls --
 * so the sites executed below the folded entry belong to the occurrence that
 * performed them and to no other.</p>
 *
 * <p>The case is hdfs-11741's: a key-rotation method entered only inside the
 * NameNode's key-manager tick.</p>
 */
public class RegionFoldPlanTest {
    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();


    private static final String TICK =
            "<o.a.h.BlockTokenSecretManager: boolean updateKeys(long)>";
    private static final String NESTED =
            "<o.a.h.BlockTokenSecretManager: boolean updateKeys()>";
    private static final String BELOW =
            "<o.a.h.BlockTokenSecretManager: void removeExpiredKeys()>";
    private static final String TICK_REGION = "REGION.tick";
    private static final String NESTED_REGION = "REGION.nested";
    private static final String ADDRESS =
            "wl/nn0#epoch0/region/" + TICK_REGION + "/ctx:Root:TICK#1";

    /**
     * The occurrence that folded the nested region owns it: one activation,
     * no activation of the folded region, and the fold row says where it ran.
     * An entry that opened an occurrence of its own is no fold: the same
     * recording without the flag plans two activations and no fold row.
     */
    @Test
    public void aFoldedEntryBelongsToTheOccurrenceItFoldedInto() {
        RuntimeRegionPlanner.Result plan = plan(true);

        assertEquals("one activation: the occurrence that was running",
                1, plan.runtimeInstances.size());
        Map<String, Object> tick = plan.runtimeInstances.get(0);
        assertEquals(TICK_REGION, tick.get("regionId"));

        // The region -> occurrence table, published where the occurrence is.
        assertEquals(Collections.singletonList(NESTED_REGION),
                tick.get(RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));

        // And the calls: everything executed below the folded entry is an
        // event of this occurrence, including the frames the enclosing
        // region's own method set does not name.
        Collection<?> calls = (Collection<?>) tick.get("callIds");
        assertTrue("the folded entry itself", calls.contains(20L));
        assertTrue("and what ran below it", calls.contains(30L));
        Collection<?> observed = (Collection<?>) tick.get("observedMethods");
        assertTrue(observed.contains(NESTED));
        assertTrue(observed.contains(BELOW));

        RuntimeRegionPlanner.Result unfolded = plan(false);
        assertEquals("unfolded, each entry is an activation of its own", 2,
                unfolded.runtimeInstances.size());
        for (Map<String, Object> activation : unfolded.runtimeInstances) {
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
        List<RuntimeRegionPlanner.MethodEvent> events = cutEvents(
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, true,
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, DN1);
        RuntimeRegionPlanner.Result activations = activations(events);
        RuntimeSelectedRegionFinalizer.Result closure = closure(activations);

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
        // replay and the composer read.
        RuntimeRegionPlanner.Result plan = plan(closure, activations, events);
        assertEquals(1, plan.regionPlans.size());
        Map<String, Object> row = plan.regionPlans.get(0);
        assertTrue("the consumer side of the cut is on the occurrence that "
                        + "ran it", declares(row, "communicationHandoffs",
                PORT_ID));
        assertEquals("and so is the phase the recording executed there",
                1, ((Collection<?>) row.get("configuredSourcePhases")).size());
    }

    /**
     * A ROW NAMES THE NODE ITS ADDRESS NAMES: sourceKey, relation and causal
     * anchor, whatever the root or a frame entered later was stamped with,
     * because the replay admits an activation by that address alone.
     *
     * <p>The first row is the q13 dzup shape: an unstamped root (a raw
     * HttpClient request into SolrCore.execute), a frame below it on
     * auto0/node0, an address on workload/unregistered.  The planner once
     * took the frame's node, and the replay dropped the target at close.  A
     * row naming another node anyway is a BLOCKING PLAN gap named by its
     * occurrence, never a drop at replay.</p>
     */
    @Test
    @SuppressWarnings("unchecked")
    public void aRowNamesTheNodeItsAddressNames() throws Exception {
        SourceRef dn1 = new SourceRef("CLUSTER_NODE", "DATANODE", "wl/dn1",
                0L);
        SourceRef node0 = new SourceRef("CLUSTER_NODE", "SOLR",
                "auto0/node0", 0L);
        // The root's stamp, whether its own receiver stamped it, the folded
        // frame's stamp, the recorded address's node, the anchor kind.
        Object[][] rows = {
                {null, false, node0,
                        RuntimeRegionPlanner.UNREGISTERED_SOURCE.key(),
                        RuntimeRegionPlanner.ANCHOR_UNREGISTERED_SOURCE},
                {dn1, true, node0, DN1,
                        RuntimeRegionPlanner.ANCHOR_REGISTERED_SOURCE},
                {dn1, false, null, DN1,
                        RuntimeRegionPlanner.ANCHOR_INHERITED_CONTEXT},
        };
        for (Object[] row : rows) {
            String node = (String) row[3];
            List<RuntimeRegionPlanner.MethodEvent> events = cutEvents(
                    (SourceRef) row[0], (Boolean) row[1], (SourceRef) row[2],
                    node);
            RuntimeRegionPlanner.Result activations = activations(events);
            RuntimeRegionPlanner.Result plan = plan(closure(activations),
                    activations, events);
            Map<String, Object> planned = plan.regionPlans.get(0);
            Map<String, Object> selector =
                    (Map<String, Object>) planned.get("rootSelector");
            Map<?, ?> anchor = (Map<?, ?>) selector.get("causalAnchor");
            assertEquals(node, planned.get("sourceKey"));
            assertEquals(node, anchor.get("sourceKey"));
            assertEquals(node, row[4], anchor.get("kind"));
            assertEquals(NodeId.parse(node).node() + "/relation/"
                    + HANDLER_REGION, planned.get("relationKey"));
            assertTrue(node + ": " + plan.planGaps, plan.planGaps.isEmpty());

            // The anchor the frame-stamp rule published for the q13 target.
            Map<String, Object> offAddress = new LinkedHashMap<>(planned);
            Map<String, Object> stamped = new LinkedHashMap<>(selector);
            stamped.put("causalAnchor", RuntimeRegionPlanner.causalAnchor(
                    NodeId.parse(node0.key()), false, "", ""));
            offAddress.put("rootSelector", stamped);
            List<Map<String, Object>> gaps = new ArrayList<>();
            RuntimeRegionPlanner.stateAnchorOffAddress(offAddress, gaps);
            assertEquals(node + ": " + gaps, 1, gaps.size());
            assertEquals("TASK_UNANSWERED", gaps.get(0).get("kind"));
            assertEquals("BLOCKING", gaps.get(0).get("cls"));
            assertEquals(planned.get("occurrenceId"),
                    gaps.get(0).get("subject"));
        }
    }

    /** The activations the fixture's recording planned. */
    private static RuntimeRegionPlanner.Result activations(
            List<RuntimeRegionPlanner.MethodEvent> events) {
        return RuntimeRegionPlanner.planSkeletonGraph(cutSkeletons(), events,
                cutRuntime(),
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList(),
                Collections.<String>emptySet());
    }

    /** The fixture's finalized closure over those activations. */
    private RuntimeSelectedRegionFinalizer.Result closure(
            RuntimeRegionPlanner.Result activations) throws IOException {
        return RuntimeSelectedRegionFinalizer.finalizeRegions(cutGraph(),
                cutSkeletons(), "test", Arrays.asList(HANDLER, LEAF),
                activations.runtimeInstances, cutObservations(),
                cutScopeMap());
    }

    /**
     * The plan rows of that closure.  The bound is the campaign's and the
     * plan builder refuses to invent one; this fixture declares no loop, so
     * any bound serves.
     */
    private static RuntimeRegionPlanner.Result plan(
            RuntimeSelectedRegionFinalizer.Result closure,
            RuntimeRegionPlanner.Result activations,
            List<RuntimeRegionPlanner.MethodEvent> events) {
        String bound = System.getProperty("causynth.loop.default.bound");
        System.setProperty("causynth.loop.default.bound", "8");
        try {
            return RuntimeRegionPlanner.plan(closure.regions, "test",
                    activations.runtimeInstances, events, cutRuntime(),
                    Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                            emptyList(),
                    Collections.<RuntimeRegionPlanner.ProtocolEvent>
                            emptyList(), closure.gaps);
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
    private static final String PORT_ID = EXCHANGE + ".wire.key-id";
    private static final String DN1 = "wl/dn1#epoch0";
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
                Collections.singletonList(HANDLER));
        Map<String, Object> leaf = skeleton(LEAF_REGION, LEAF,
                Collections.singletonList(LEAF));
        leaf.put("selection", "EXCEPTION_CONTEXT");
        Map<String, Object> port = new LinkedHashMap<>();
        port.put("portId", PORT_ID);
        port.put(RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN");
        port.put("sourceKind",
                RuntimeSelectedRegionFinalizer.COMMUNICATION_SITE_PORT);
        port.put("dependencyRole", "VALUE_FRONTIER");
        port.put("name", "key-id");
        port.put("javaType", "int");
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

    /**
     * The handler opens an occurrence on {@code node}; the leaf folds into
     * it.  Each entry carries the stamp it was recorded with.
     */
    private static List<RuntimeRegionPlanner.MethodEvent> cutEvents(
            SourceRef handlerStamp, boolean receiverAttributed,
            SourceRef leafStamp, String node) {
        String address = OccurrenceAddress.of(NodeId.parse(node),
                HANDLER_REGION, CausalContext.of(Role.of("SASL"), "", 1),
                ExecutionIndex.empty()).render();
        return Arrays.asList(
                entry(10L, HANDLER, 0L, address, false, handlerStamp,
                        receiverAttributed),
                entry(20L, LEAF, 10L, "", true, leafStamp, false));
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

    /** The published scope map: the throw below {@link #GUARD_SITE}, which
     *  decides it. */
    private StaticScopeMap cutScopeMap() throws IOException {
        Map<String, Object> thrown = new LinkedHashMap<>();
        thrown.put("kind", "exception_throw");
        thrown.put("method", LEAF);
        thrown.put("unitIndex", 7);
        Map<String, Object> region = new LinkedHashMap<>();
        region.put("regionId", LEAF_REGION);
        region.put("methods", Collections.singletonList(LEAF));
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(StaticScopeMap.sites(
                Collections.singletonList(thrown),
                Collections.singletonList(region),
                Collections.<String, edu.uva.liftlab.graphchecker.contract.Clock>emptyMap(), method -> false,
                cell -> SharedFieldFlow.TrackedKind.VALUE, cell -> false),
                site -> Collections.singletonList(new StaticScopeMap.Guard(
                        GUARD_SITE, Boolean.TRUE)))) {
            text.append(row).append('\n');
        }
        Path file = folder.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
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

    private static RuntimeRegionPlanner.Result plan(boolean folded) {
        return RuntimeRegionPlanner.planSkeletonGraph(skeletons(),
                events(folded),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList(),
                Collections.<String>emptySet());
    }

    /**
     * The tick's region holds only its own method; the nested region holds
     * the two the tick calls.  That is the shape the fold has to carry: the
     * enclosing skeleton does not name the folded region's methods, so
     * nothing but the fold can give those frames an occurrence.
     */
    private static List<StaticProgram.RegionRow> skeletons() {
        List<Map<String, Object>> rows = new ArrayList<>();
        rows.add(skeleton(TICK_REGION, TICK,
                Collections.singletonList(TICK)));
        rows.add(skeleton(NESTED_REGION, NESTED,
                Arrays.asList(NESTED, BELOW)));
        return StaticProgram.regionRows(rows,
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    private static Map<String, Object> skeleton(String regionId, String root,
                                                List<String> methods) {
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
        return row;
    }

    /**
     * One recorded tick: it opens an occurrence, calls the nested method,
     * and that call runs one more of the nested region's methods below it.
     *
     * @param folded whether the nested entry was folded -- the recording's
     *               own statement, which is the only thing that differs
     *               between the two cases this fixture serves
     */
    private static List<RuntimeRegionPlanner.MethodEvent> events(
            boolean folded) {
        List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
        methods.add(entry(10L, TICK, 0L, ADDRESS, false));
        methods.add(entry(20L, NESTED, 10L, folded ? ""
                : "wl/nn0#epoch0/region/" + NESTED_REGION
                + "/ctx:Root:TICK#1", folded));
        methods.add(entry(30L, BELOW, 20L, "", false));
        return methods;
    }

    private static RuntimeRegionPlanner.MethodEvent entry(
            long callId, String method, long parentCallId, String address,
            boolean folded) {
        return entry(callId, method, parentCallId, address, folded,
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, true);
    }

    private static RuntimeRegionPlanner.MethodEvent entry(
            long callId, String method, long parentCallId, String address,
            boolean folded, SourceRef stamp, boolean receiverAttributed) {
        return new RuntimeRegionPlanner.MethodEvent(callId, "test", "main",
                1L, method, 1, "o.a.h.BlockTokenSecretManager", callId,
                parentCallId, 0L, 1L, 1L, 0L, stamp, receiverAttributed, "",
                "", address, folded);
    }
}
