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
import edu.uva.liftlab.graphchecker.contract.CausalContext;
import edu.uva.liftlab.graphchecker.contract.Clock;
import edu.uva.liftlab.graphchecker.contract.ExecutionIndex;
import edu.uva.liftlab.graphchecker.contract.NodeId;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.Role;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.SharedFieldFlow;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
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

    private File file(String name, String text) throws IOException {
        File file = new File(folder.getRoot(), name);
        Files.write(file.toPath(), text.getBytes(StandardCharsets.UTF_8));
        return file;
    }
}
