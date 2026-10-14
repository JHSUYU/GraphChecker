package edu.uva.liftlab.graphchecker.runtime;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.causynth.RecordedAccesses;
import edu.uva.liftlab.graphchecker.causynth.RecordedHeap;
import edu.uva.liftlab.graphchecker.causynth.RecordedStore;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.causynth.TracedRows;
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import java.io.File;
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
import java.util.Set;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

/**
 * What PLAN states of a recording ({@link RuntimeRegionPlanner}, {@link
 * RuntimeSelectedRegionFinalizer}): the activations of a folded entry (IDENTITY
 * §1: a region entered synchronously inside a running occurrence opens none
 * of its own; the occurrence it folded into names it, owns its calls and
 * declares what it declares), the node a row names, the signature of what
 * an occurrence read, the heap the aggregation builds, and the artifacts a
 * pruned recording is aggregated over.
 */
public class RuntimeRegionPlannerTest {
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
    private static final String SERIAL =
            "<o.a.h.BlockTokenSecretManager: long serial>";

    /** A map of these keys and values, in order. */
    private static Map<String, Object> map(Object... entries) {
        Map<String, Object> map = new LinkedHashMap<>();
        for (int at = 0; at < entries.length; at += 2) {
            map.put((String) entries[at], entries[at + 1]);
        }
        return map;
    }

    /** {@code planSkeletonGraph} over these rows, nothing else recorded. */
    private static RuntimeRegionPlanner.Result graph(
            List<StaticProgram.RegionRow> skeletons,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> runtime,
            List<RuntimeRegionPlanner.FieldAccessEvent> fields,
            Map<String, Map<String, Boolean>> receiverReads) {
        return RuntimeRegionPlanner.planSkeletonGraph(skeletons, methods,
                runtime, fields,
                Collections.<RuntimeRegionPlanner.ProtocolEvent>emptyList(),
                Collections.<String>emptySet(),
                Collections.<String, String>emptyMap(), receiverReads);
    }

    /**
     * The occurrence that folded the nested region owns it: one activation,
     * no activation of the folded region, the fold row saying where it ran,
     * and every call below the folded entry -- frames the enclosing region's
     * method set does not name -- its own.  The same recording without the
     * flag plans two activations and no fold row.
     */
    @Test
    public void aFoldedEntryBelongsToTheOccurrenceItFoldedInto() {
        RuntimeRegionPlanner.Result plan = tickPlan(true);
        assertEquals("one activation: the occurrence that was running",
                1, plan.runtimeInstances.size());
        Map<String, Object> tick = plan.runtimeInstances.get(0);
        assertEquals(TICK_REGION, tick.get("regionId"));
        assertEquals(Collections.singletonList(NESTED_REGION),
                tick.get(RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));
        Collection<?> calls = (Collection<?>) tick.get("callIds");
        assertTrue("the folded entry itself", calls.contains(20L));
        assertTrue("and what ran below it", calls.contains(30L));
        Collection<?> observed = (Collection<?>) tick.get("observedMethods");
        assertTrue(observed.contains(NESTED) && observed.contains(BELOW));
        RuntimeRegionPlanner.Result unfolded = tickPlan(false);
        assertEquals("unfolded, each entry is an activation of its own", 2,
                unfolded.runtimeInstances.size());
        for (Map<String, Object> activation : unfolded.runtimeInstances) {
            assertFalse(activation.containsKey(
                    RuntimeSelectedRegionFinalizer.FOLDED_REGION_IDS));
        }
    }

    /**
     * THE WIRE'S TWO HALVES HAVE ONE SOURCE EACH: the weave captures every
     * skeleton's exports, planned or not, and a plan row declares only what
     * its occurrence attaches (hdfs-adhoc-12 HG9L: the NameNode's {@code
     * convert(NNHAStatusHeartbeat)} roots no planned region, and its {@code
     * setTxid} export was never woven).
     */
    @Test
    public void everyExportIsWovenAndAPlanDeclaresItsAttachesOnly() {
        String producer = "<o.a.h.PBHelper: o.a.h.NNHAStatusHeartbeatProto"
                + " convert(o.a.h.NNHAStatusHeartbeat)>";
        String txid = "XCH.53d59f95-3ee5-385f-a674-a07d58f5b75b"
                + ".wire.auto:NNHAStatusHeartbeatProto.Txid";
        Map<String, Object> port = map("portId", txid,
                RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "OUT",
                "sourceKind", RuntimeSelectedRegionFinalizer
                        .COMMUNICATION_SITE_PORT,
                "dependencyRole", "VALUE_FRONTIER",
                "name", "auto:NNHAStatusHeartbeatProto.Txid",
                "javaType", "long",
                "exchangeSiteKey", "XCH.53d59f95-3ee5-385f-a674-a07d58f5b75b",
                "handoffLeafPath", txid, "callSiteId", producer + "#u8",
                "definitionMethod", producer,
                "outputCaptureKind", "CALL_ARGUMENT",
                "definitionUnitIndex", 8,
                "declaredCallee", "<o.a.h.NNHAStatusHeartbeatProto$Builder:"
                        + " o.a.h.NNHAStatusHeartbeatProto$Builder"
                        + " setTxid(long)>",
                "argumentIndex", 0);
        Map<String, Object> unplanned = skeleton("REGION.b9bd09cd", producer,
                Collections.singletonList(producer));
        unplanned.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                Collections.singletonList(port));
        List<StaticProgram.RegionRow> skeletons =
                new ArrayList<>(cutSkeletons());
        skeletons.addAll(rows(unplanned));
        List<CommunicationHandoffSpec> exports =
                RuntimeRegionPlanner.exportSites(skeletons);
        assertEquals("the one export, though no region holding it is "
                + "planned; the leaf's attach is no export", 1,
                exports.size());
        assertEquals(txid, exports.get(0).portId());
        assertTrue(exports.get(0).outgoing());
        assertEquals(producer + "#u8", exports.get(0).siteId());
        Map<String, Object> region = new LinkedHashMap<>(unplanned);
        region.put("outputs", Collections.singletonList(port));
        assertTrue("a plan row of the producer declares no export",
                RuntimeRegionPlanner.attachSites(rows(region).get(0))
                        .isEmpty());
    }

    /**
     * THE DECLARATION UNION: an occurrence declares what the regions folded
     * into it declare (the hdfs-11741 shape: the consumer side of the
     * target's own exchange was once declared by a region with no
     * occurrence, its PUBLISH phase with it), and both reach its plan row.
     */
    @Test
    public void anOccurrenceDeclaresWhatFoldedIntoIt() throws Exception {
        List<RuntimeRegionPlanner.MethodEvent> events = cutEvents(
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, true,
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, DN1);
        RuntimeRegionPlanner.Result activations = activations(events);
        RuntimeSelectedRegionFinalizer.Result closure = closure(activations,
                false, false);
        assertEquals("the folded region has no row: it has no occurrence",
                1, closure.regions.size());
        Map<String, Object> handler = closure.regions.get(0);
        assertEquals(HANDLER_REGION, handler.get("regionId"));
        assertTrue("the methods it ran include the folded region's",
                ((Collection<?>) handler.get("methods")).contains(LEAF));
        assertTrue("the cut the folded region declared is its input",
                declares(handler, "symbolicInputs"));
        assertEquals("and the PUBLISH phase its own skeleton does not name",
                1, ((Collection<?>) handler.get(
                        "configuredSourcePhaseDeclarations")).size());
        RuntimeRegionPlanner.Result plan = plan(closure, activations, events);
        assertEquals(1, plan.regionPlans.size());
        Map<String, Object> row = plan.regionPlans.get(0);
        assertTrue("the consumer side of the cut is on the occurrence that "
                + "ran it", declares(row, "communicationHandoffs"));
        assertEquals(1, ((Collection<?>) row.get("configuredSourcePhases"))
                .size());
    }

    /**
     * A ROW NAMES THE NODE ITS ADDRESS NAMES: sourceKey, relation and causal
     * anchor, whatever the root or a frame entered later was stamped with,
     * because the replay admits an activation by that address alone (q13
     * dzup: an unstamped root, a frame below it on auto0/node0, an address
     * on workload/unregistered; the planner once took the frame's node).  A
     * row naming another node anyway is a BLOCKING PLAN gap.
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
            {null, false, node0, RuntimeRegionPlanner.UNREGISTERED_SOURCE
                    .key(), RuntimeRegionPlanner.ANCHOR_UNREGISTERED_SOURCE},
            {dn1, true, node0, DN1,
                RuntimeRegionPlanner.ANCHOR_REGISTERED_SOURCE},
            {dn1, false, null, DN1,
                RuntimeRegionPlanner.ANCHOR_INHERITED_CONTEXT}};
        for (Object[] row : rows) {
            String node = (String) row[3];
            List<RuntimeRegionPlanner.MethodEvent> events = cutEvents(
                    (SourceRef) row[0], (Boolean) row[1], (SourceRef) row[2],
                    node);
            RuntimeRegionPlanner.Result activations = activations(events);
            RuntimeRegionPlanner.Result plan = plan(closure(activations,
                    false, false), activations, events);
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

    /**
     * A SIGNATURE IS WHAT A FLIP QUERY OF THE OCCURRENCE READS ({@code
     * RuntimeRegionPlanner#stampSignatures}): two ticks that read one
     * version of a field digest alike; a store between the second and the
     * third gives the third's read another version, so another digest,
     * though it read the same value.  The seqs it ran between ride along.
     * A field a method reads on its own receiver alone is held, for a
     * reader, by the receiver its call was recorded with, whether or not
     * the read's row was written; a field the method also reads on another
     * object gets no such holder.
     */
    @Test
    public void aSignatureIsWhatTheOccurrenceRead() {
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = new ArrayList<>();
        for (long tick = 1; tick <= 3; tick++) {
            fields.add(new RuntimeRegionPlanner.FieldAccessEvent(10 * tick + 1,
                    "FIELD_READ", TICK, 10 * tick, 3, "", SERIAL, 5, 0, "7"));
        }
        fields.add(new RuntimeRegionPlanner.FieldAccessEvent(25L,
                "FIELD_WRITE", BELOW, 99L, 1, "", SERIAL, 5, 0, "7"));
        Map<Object, Map<String, Object>> byRoot = new LinkedHashMap<>();
        for (Map<String, Object> activation : graph(skeletons(), ticks(3),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                fields, Collections.<String, Map<String, Boolean>>emptyMap())
                .runtimeInstances) {
            byRoot.put(activation.get("rootCallId"), activation);
        }
        String signature = RuntimeSelectedRegionFinalizer.SIGNATURE;
        assertEquals(byRoot.get(10L).get(signature),
                byRoot.get(20L).get(signature));
        assertFalse(byRoot.get(20L).get(signature).equals(
                byRoot.get(30L).get(signature)));
        assertEquals(10L, byRoot.get(10L).get(
                RuntimeSelectedRegionFinalizer.FIRST_SEQ));
        assertEquals(11L, byRoot.get(10L).get(
                RuntimeSelectedRegionFinalizer.LAST_SEQ));

        String other = "<o.a.h.BlockTokenSecretManager: long "
                + "keyUpdateInterval>";
        Map<String, Boolean> reads = new LinkedHashMap<>();
        reads.put(SERIAL, true);
        reads.put(other, false);
        RuntimeRegionPlanner.Result plan = graph(skeletons(), ticks(2),
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                Collections.singletonList(new RuntimeRegionPlanner
                        .FieldAccessEvent(11L, "FIELD_READ", TICK, 10L, 3, "",
                        SERIAL, 1, 0, "7")), Collections.singletonMap(TICK,
                        reads));
        assertEquals(2, plan.runtimeInstances.size());
        for (Map<String, Object> activation : plan.runtimeInstances) {
            Object tick = activation.get("rootCallId");
            Map<?, ?> holders = (Map<?, ?>) activation.get(
                    RuntimeSelectedRegionFinalizer.RECEIVER_HOLDERS);
            assertEquals("tick " + tick, Collections.singleton(1),
                    holders.get(SERIAL));
            assertFalse(holders.containsKey(other));
            Map<?, ?> owners = (Map<?, ?>) activation.get(
                    RuntimeSelectedRegionFinalizer.FIELD_OWNERS);
            assertEquals("tick " + tick + "'s recorded owners",
                    Long.valueOf(10L).equals(tick), owners != null
                            && owners.containsKey(SERIAL));
        }
    }

    /** {@code count} ticks of the tick region, each its own occurrence. */
    private static List<RuntimeRegionPlanner.MethodEvent> ticks(int count) {
        List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
        for (long tick = 1; tick <= count; tick++) {
            methods.add(entry(10 * tick, TICK, 0L, "wl/nn0#epoch0/region/"
                    + TICK_REGION + "/ctx:Root:TICK#" + tick, false));
        }
        return methods;
    }

    /**
     * A DECLARED OCCURRENCE THE RECORDING THREW AT ASKS NOTHING: the run as
     * recorded is the failure, and a claim moving no root is never a finding
     * (owner 2026-10-04), so PLAN names the declaration, BLOCKING.  A guard
     * reaching a declared throw on both arms states no fatal arm to judge
     * the recording by: PLAN names that declaration too.
     */
    @Test
    public void aRecordingThatThrewThereIsADeclarationDefect()
            throws Exception {
        RuntimeRegionPlanner.Result activations = activations(cutEvents(
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, true,
                RuntimeRegionPlanner.UNREGISTERED_SOURCE, DN1));
        // {threw, ambiguous, the BLOCKING kind PLAN names or ""}
        Object[][] table = {
            {false, false, ""},
            {true, false, "TARGET_FATAL_IN_RECORDING"},
            {false, true, "AMBIGUOUS_FATAL_ARM"},
            {true, true, "AMBIGUOUS_FATAL_ARM"}};
        for (Object[] row : table) {
            List<Map<String, Object>> gaps = closure(activations,
                    (Boolean) row[0], (Boolean) row[1]).gaps;
            String named = "";
            for (Map<String, Object> gap : gaps) {
                if ("BLOCKING".equals(gap.get("cls"))) {
                    named = String.valueOf(gap.get("kind"));
                }
            }
            assertEquals(Arrays.toString(row) + ": " + gaps, row[2], named);
        }
    }

    /** The activations the cut fixture's recording planned. */
    private static RuntimeRegionPlanner.Result activations(
            List<RuntimeRegionPlanner.MethodEvent> events) {
        return graph(cutSkeletons(), events, cutRuntime(),
                Collections.<RuntimeRegionPlanner.FieldAccessEvent>emptyList(),
                Collections.<String, Map<String, Boolean>>emptyMap());
    }

    /** The finalized closure over those activations, the recording taking
     *  the fatal arm at the guard or not, the guard reaching a second
     *  declared throw on its other arm or not. */
    private RuntimeSelectedRegionFinalizer.Result closure(
            RuntimeRegionPlanner.Result activations, boolean threw,
            boolean ambiguous) throws IOException {
        Map<String, Object> guard = map("schemaVersion", 3, "kind",
                "exception_guard", "transferKind", "GUARD", "fromCell",
                LEAF + "::r1", "toCell", LEAF + "#u5#exception:o.a.h.Invalid",
                "method", LEAF, "siteId", GUARD_SITE, "unitIndex", 5,
                "regionIds", Collections.singletonList(LEAF_REGION));
        // The recording's own statement that the fatal guard was decided.
        Map<String, Object> branch = map("kind", "BRANCH", "eventSeq", 5L,
                "method", LEAF, "callId", 20L, "siteId", GUARD_SITE,
                "outcome", threw);
        return RuntimeSelectedRegionFinalizer.finalizeRegions(
                new ArrayList<>(Collections.singletonList(guard)),
                cutSkeletons(), "test", Arrays.asList(HANDLER, LEAF),
                activations.runtimeInstances, Collections.singletonList(
                        branch), cutScopeMap(ambiguous),
                RuntimeWorkflowDiscovery.FIRST,
                Collections.<ScheduleEvent>emptyList(),
                new RecordedStore(null), new RecordedAccesses.Builder().build(),
                new RecordedHeap.Builder().build());
    }

    /** The plan rows of that closure; this fixture declares no loop, so any
     *  bound serves the plan builder, which invents none. */
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

    /** Whether one row's named catalog states the cut's port. */
    private static boolean declares(Map<String, Object> row, String field) {
        for (Object entry : (Collection<?>) row.get(field)) {
            if (PORT_ID.equals(((Map<?, ?>) entry).get("portId"))) return true;
        }
        return false;
    }

    @SafeVarargs
    private static List<StaticProgram.RegionRow> rows(
            Map<String, Object>... skeletons) {
        return StaticProgram.regionRows(Arrays.asList(skeletons),
                RuntimeSelectedRegionFinalizer.SKELETON_KIND, "test");
    }

    /** The handler's skeleton names its own method only -- the weave stops
     *  where a region roots another one -- and the leaf declares the cut and
     *  the phase. */
    private static List<StaticProgram.RegionRow> cutSkeletons() {
        Map<String, Object> leaf = skeleton(LEAF_REGION, LEAF,
                Collections.singletonList(LEAF));
        leaf.put("selection", "EXCEPTION_CONTEXT");
        leaf.put(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS,
                Collections.singletonList(map("portId", PORT_ID,
                        RuntimeSelectedRegionFinalizer.REGION_PORT_SIDE, "IN",
                        "sourceKind", RuntimeSelectedRegionFinalizer
                                .COMMUNICATION_SITE_PORT,
                        "dependencyRole", "VALUE_FRONTIER", "name", "key-id",
                        "javaType", "int", "exchangeSiteKey", EXCHANGE,
                        "callSiteId", LEAF, "handoffLeafPath", PORT_ID,
                        "definitionMethod", LEAF,
                        "outputCaptureKind", "METHOD_PARAMETER",
                        "argumentIndex", 0)));
        leaf.put("configuredSourcePhaseDeclarations",
                Collections.singletonList(map("schemaVersion", 1, "kind",
                        "CONFIGURED_SOURCE_PHASE_DECLARATION", "authority",
                        "EXACT_STATIC_SOURCE_HOOK_SITE_V1", "phase", "PUBLISH",
                        "sourceId", "SRC.key", "fieldSignature",
                        "<o.a.h.BlockKey: int keyId>", "declarationMethod",
                        LEAF, "declarationUnitIndex", 7, "siteId",
                        PHASE_SITE)));
        return rows(skeleton(HANDLER_REGION, HANDLER,
                Collections.singletonList(HANDLER)), leaf);
    }

    /** The handler opens an occurrence on {@code node}; the leaf folds into
     *  it.  Each entry carries the stamp it was recorded with. */
    private static List<RuntimeRegionPlanner.MethodEvent> cutEvents(
            SourceRef handlerStamp, boolean receiverAttributed,
            SourceRef leafStamp, String node) {
        String address = OccurrenceAddress.of(NodeId.parse(node),
                HANDLER_REGION, CausalContext.of(Role.of("SASL"), "", 1),
                ExecutionIndex.empty()).render();
        return Arrays.asList(entry(10L, HANDLER, 0L, address, false,
                handlerStamp, receiverAttributed), entry(20L, LEAF, 10L, "",
                true, leafStamp, false));
    }

    /** The fatal guard the leaf decided -- healthy, as a declared
     *  occurrence's recording must -- and the hook site it executed. */
    private static List<RuntimeRegionPlanner.RuntimeEvent> cutRuntime() {
        return Arrays.asList(new RuntimeRegionPlanner.RuntimeEvent(5L,
                "BRANCH", LEAF, 20L, 0L, GUARD_SITE, "", -1, "", 0, "",
                Boolean.FALSE, null, "IF", ""),
                new RuntimeRegionPlanner.RuntimeEvent(7L, "CALL_SITE_ENTER",
                        LEAF, 20L, 1L, PHASE_SITE, "<o.a.h.Key: int id()>", -1,
                        "", 0, "", null, null, "", ""));
    }

    /** The published scope map: the throw below {@link #GUARD_SITE}, which
     *  decides it; {@code ambiguous}: a second declared throw (unit 9) on the
     *  guard's other arm. */
    private StaticScopeMap cutScopeMap(boolean ambiguous) throws IOException {
        List<Map<String, Object>> throwsDeclared = new ArrayList<>();
        for (int unit : ambiguous ? new int[] {7, 9} : new int[] {7}) {
            throwsDeclared.add(map("kind", "exception_throw", "method", LEAF,
                    "unitIndex", unit));
        }
        StringBuilder text = new StringBuilder();
        for (JsonObject row : StaticScopeMap.rows(StaticScopeMap.sites(
                throwsDeclared, Collections.singletonList(map("regionId",
                        LEAF_REGION, "methods", Collections.singletonList(
                                LEAF))), Collections.<String, Clock>emptyMap(),
                (m, u, c) -> null, (demandSite, demandCell) -> null,
                method -> false, cell -> SharedFieldFlow.TrackedKind.VALUE,
                cell -> false, cell -> false),
                site -> Collections.singletonList(new StaticScopeMap.Guard(
                        GUARD_SITE, SiteId.unitIndexOf(site) != 9)),
                method -> false)) {
            text.append(row).append('\n');
        }
        Path file = folder.newFolder().toPath().resolve(StaticScopeMap.FILE);
        Files.write(file, text.toString().getBytes(StandardCharsets.UTF_8));
        return StaticScopeMap.read(file);
    }

    /** The tick region holds its own method only, the nested region the
     *  two the tick calls: nothing but the fold can give those frames an
     *  occurrence.  One recorded tick, the nested entry folded or not. */
    private static RuntimeRegionPlanner.Result tickPlan(boolean folded) {
        List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
        methods.add(entry(10L, TICK, 0L, "wl/nn0#epoch0/region/" + TICK_REGION
                + "/ctx:Root:TICK#1", false));
        methods.add(entry(20L, NESTED, 10L, folded ? "" : "wl/nn0#epoch0/"
                + "region/" + NESTED_REGION + "/ctx:Root:TICK#1", folded));
        methods.add(entry(30L, BELOW, 20L, "", false));
        return graph(skeletons(), methods,
                Collections.<RuntimeRegionPlanner.RuntimeEvent>emptyList(),
                Collections.<RuntimeRegionPlanner.FieldAccessEvent>emptyList(),
                Collections.<String, Map<String, Boolean>>emptyMap());
    }

    private static List<StaticProgram.RegionRow> skeletons() {
        return rows(skeleton(TICK_REGION, TICK, Collections.singletonList(
                TICK)), skeleton(NESTED_REGION, NESTED, Arrays.asList(NESTED,
                BELOW)));
    }

    private static Map<String, Object> skeleton(String regionId, String root,
                                                List<String> methods) {
        return map("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION,
                "kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                "regionId", regionId, "rootMethod", root,
                "rootAuthority", "STATE_WRITER_ENTRY", "anchorMethod", root,
                "anchorMethods", new ArrayList<>(methods),
                "selection", "STATE_CONTEXT",
                "methods", new ArrayList<>(methods));
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
                "", address, folded, 1);
    }

    /**
     * THE RECORDED HEAP as the trace aggregation builds it ({@link
     * RuntimeRegionPlanner#recordedHeap}): a field access's receiver holds
     * its value, a static field's value is a root, a storing call's receiver
     * holds each argument, an accessor call's receiver what it returned;
     * each object is mentioned under its call's causal context (the entry's
     * requestKey in its recording window; none under a turn every window
     * counts #0), and each activation states its root call's.
     */
    @Test
    public void theAggregationStatesHoldersMentionsAndContexts() {
        String method = "<ex.Server: void handle()>";
        String store = method + "#u3";
        String accessor = method + "#u4";
        // Calls 10-21 serve request A#1 (20 on another thread); 30 is tick
        // B#1; 40 runs under no context; 50 serves C#1.  In a second window,
        // 60 serves another A#1; 70 a turn begun in an older window.
        Object[][] calls = {{1L, 1L, 10L, 0L, 0, "A#1", 1},
                {2L, 1L, 11L, 10L, 100, "A#1", 1}, {3L, 2L, 20L, 0L, 0, "A#1", 1},
                {4L, 2L, 21L, 20L, 0, "A#1", 1}, {5L, 3L, 30L, 0L, 0, "B#1", 1},
                {6L, 4L, 40L, 0L, 400, "", 1}, {7L, 1L, 50L, 0L, 0, "C#1", 1},
                {8L, 1L, 60L, 0L, 600, "A#1", 2},
                {9L, 1L, 70L, 0L, 700, "T#0", 2}};
        List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
        for (Object[] c : calls) {
            methods.add(new RuntimeRegionPlanner.MethodEvent((Long) c[0],
                    "test", "t" + c[1], (Long) c[1], method, (Integer) c[4],
                    "ex.Server", (Long) c[2], (Long) c[3], 0L, 0L, 0L, 0L,
                    null, false, (String) c[5], "", "", false,
                    (Integer) c[6]));
        }
        // A's 200 held 201; B read a static field holding 300; C read 201.
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = new ArrayList<>();
        for (long[] f : new long[][] {{8, 21, 200, 201}, {9, 30, 0, 300},
                {10, 50, 500, 201}}) {
            fields.add(new RuntimeRegionPlanner.FieldAccessEvent(f[0],
                    "FIELD_WRITE", method, f[1], 2, "",
                    "<ex.Server: java.lang.Object held>", (int) f[2],
                    (int) f[3], ""));
        }
        // A handed 202 to a store on its 100; B's accessor on 300 returned
        // 301.
        Object[][] events = {{11L, "CALL_SITE_ENTER", 11L, 5L, store, 100},
                {12L, "CALL_ARGUMENT", 11L, 5L, store, 202},
                {13L, "CALL_SITE_RETURN", 11L, 5L, store, 0},
                {14L, "CALL_SITE_ENTER", 30L, 6L, accessor, 300},
                {15L, "CALL_SITE_RETURN", 30L, 6L, accessor, 301}};
        List<RuntimeRegionPlanner.RuntimeEvent> runtime = new ArrayList<>();
        for (Object[] e : events) {
            runtime.add(new RuntimeRegionPlanner.RuntimeEvent((Long) e[0],
                    (String) e[1], method, (Long) e[2], (Long) e[3],
                    (String) e[4], "", 0, "", (Integer) e[5], "", null, null,
                    "", ""));
        }
        List<Map<String, Object>> activations = new ArrayList<>();
        for (long root : new long[] {10L, 20L, 30L, 40L, 60L, 70L}) {
            activations.add(map("rootCallId", root));
        }
        RecordedHeap heap = RuntimeRegionPlanner.recordedHeap(methods, fields,
                runtime, activations, Collections.singletonMap(store,
                        "<ex.Server: java.util.List items>"),
                Collections.singletonMap(accessor,
                        "<ex.Conf: ex.Value value>"));
        Set<Integer> fromNothing = heap.reachable(new int[0]);
        assertTrue("a static field's object and what it held",
                fromNothing.containsAll(Arrays.asList(300, 301)));
        assertFalse(fromNothing.contains(202));
        assertTrue(heap.reachable(new int[] {200}).contains(201));
        assertTrue(heap.reachable(new int[] {100}).contains(202));
        long a = heap.contextOfRoot(10L);
        long b = heap.contextOfRoot(30L);
        assertEquals("one request on two threads is one context", a,
                heap.contextOfRoot(20L));
        assertFalse(a == b);
        assertEquals("an occurrence under no context has none",
                RecordedHeap.NOWHERE, heap.contextOfRoot(40L));
        assertFalse("a request's key in another window is another context",
                a == heap.contextOfRoot(60L));
        assertEquals("a turn begun in an older window names none",
                RecordedHeap.NOWHERE, heap.contextOfRoot(70L));
        // object, the context it is confined to: 202 and its holder 100 A's;
        // 301 and 300 B's; 201, mentioned under A and C, nowhere, its holder
        // 200 A's; a call under no context or #0, an unmentioned object.
        Object[][] confined = {{202, a}, {301, b}, {201, RecordedHeap.NOWHERE},
                {200, a}, {400, RecordedHeap.NOWHERE},
                {700, RecordedHeap.NOWHERE}, {600, heap.contextOfRoot(60L)},
                {999, RecordedHeap.NOWHERE}};
        for (Object[] row : confined) {
            assertEquals("object " + row[0], row[1],
                    heap.confinement((Integer) row[0]));
        }
    }

    /**
     * A recording whose rows the weave pruned is aggregated only over the
     * static artifacts the weave decided them on, and by the row rule it
     * traced by: over others, a site or port they add would find no rows,
     * and an older rule's recording lacks rows the aggregation reads.
     */
    @Test
    public void aPrunedRecordingIsAggregatedOverItsOwnArtifactsOnly()
            throws IOException {
        File scopeMap = file("static_scope_map.jsonl", "{\"kind\":\"A\"}\n");
        File graph = file("candidate_dataflow_edges.jsonl.gz", "g");
        File skeletons = file("region_skeletons.jsonl.gz", "s");
        String own = TracedRows.inputsDigest(scopeMap, graph, skeletons);
        String others = TracedRows.inputsDigest(file("other_scope_map.jsonl",
                "{\"kind\":\"B\"}\n"), graph, skeletons);
        assertFalse("another scope map is another digest", own.equals(others));
        // Traced before the rule was part of the digest: its artifacts alone.
        String unruled = ArtifactIO.sha256(ArtifactIO.sha256(
                scopeMap.toPath()) + "\n" + ArtifactIO.sha256(graph.toPath())
                + "\n" + ArtifactIO.sha256(skeletons.toPath()));
        Object[][] rows = {
            // manifest schema, its tracedRows, refused
            {1, null, false}, // a recording that wrote every row
            {2, own, false},
            {2, others, true},
            {2, "", true},    // a pruned recording stating no digest
            {2, unruled, true}}; // traced by an older row rule
        for (Object[] row : rows) {
            JsonObject manifest = new JsonObject();
            manifest.addProperty("schemaVersion", (Integer) row[0]);
            if (row[1] != null) {
                manifest.addProperty("tracedRows", (String) row[1]);
            }
            try {
                CausynthTraceRecorder.requireTracedOver(manifest, scopeMap,
                        graph, skeletons);
                assertEquals(manifest.toString(), false, row[2]);
            } catch (IOException refused) {
                assertTrue(manifest + ": " + refused.getMessage(),
                        (Boolean) row[2] && refused.getMessage()
                                .startsWith("TRACED_ROWS_MISMATCH"));
            }
        }
    }

    private File file(String name, String text) throws IOException {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), text.getBytes(StandardCharsets.UTF_8));
        return file;
    }
}
