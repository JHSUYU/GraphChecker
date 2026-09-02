package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * A bounded region's occurrence set is addressed by its selected causal
 * anchor, never by the polling prefix.
 *
 * <p>A raw polling ordinal is not replay identity.  The DN {@code
 * offerService} region is bounded to K_L=8 turns of a loop that heartbeats
 * for the whole workload; taking the first eight turns took eight heartbeats
 * that carried no {@code KeyUpdateCommand}, so the region contributed no
 * rotation evidence at all.  The budget is unchanged -- what changes is
 * which K_L turns fill it: the turns that carried the exchange the plan
 * selected this region for.</p>
 */
public class ConcolicRegionRuntimeCausalAnchorOccurrenceTest {
    private static final String TASK = "TASK.anchored-loop";
    private static final String SOURCE_KEY = "test/anchor#epoch0";
    private static final String OCCURRENCE =
            SOURCE_KEY + "/region/POLLER#1";
    private static final String ROOT = "<example.Poller: void poll()>";
    private static final String CALLEE = "<example.Peer: long fetch()>";
    private static final String ANCHOR_PORT = "XCH.anchor.resp.keys";
    private static final String OTHER_PORT = "XCH.other.resp.keys";
    /** The root loop's own K_L, as the DN heartbeat loop declares it. */
    private static final int K_L = 8;
    /** An inner loop bound; it must never cap the outer anchor search. */
    private static final int REGION_MAX = 24;
    private static final String ROOT_LOOP_SITE = "L(" + ROOT + "#u1)";
    /** An inner walk, exactly as the DN region's {@code allKeys} loops do. */
    private static final String INNER_LOOP_SITE = ROOT + "#u17";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    private String previousPlan;
    private String previousTasks;
    private String previousResults;
    private Path results;

    @Before
    public void rememberProperties() {
        previousPlan = System.getProperty("causynth.concolic.task.plan");
        previousTasks = System.getProperty("causynth.concolic.task.id");
        previousResults = System.getProperty("causynth.concolic.results");
        ConcolicRegionRuntime.resetForTests();
    }

    @After
    public void restoreProperties() {
        ConcolicRegionRuntime.resetForTests();
        restore("causynth.concolic.task.plan", previousPlan);
        restore("causynth.concolic.task.id", previousTasks);
        restore("causynth.concolic.results", previousResults);
    }

    /**
     * The turn that carried the selected anchor is kept even though it lands
     * past the polling prefix, and the kept set is still exactly K_L rows.
     */
    @Test
    public void anAnchoredTurnPastThePrefixTakesAReservedSlot()
            throws Exception {
        load(true, true);

        boolean[] turns = new boolean[56];
        turns[48] = true;

        assertEquals("the anchored 49th turn replaces the 8th unanchored one",
                Arrays.asList(1, 2, 3, 4, 5, 6, 7, 49),
                ConcolicRegionRuntime.simulateAnchoredTurnsForTests(
                        TASK, turns));

        JsonObject marker = onlyMarker();
        assertEquals(K_L, marker.get("boundedAt").getAsInt());
        assertEquals(1, marker.get("anchoredOccurrences").getAsInt());
        assertEquals(41,
                marker.get("unanchoredTurnsReleased").getAsInt());
        assertEquals(49, marker.get("turnsAdmitted").getAsInt());
        assertFalse(marker.toString(), marker.has("anchorProbeCeiling"));
        assertFalse(marker.toString(), marker.has("anchorReservationReleased"));
        assertEquals(ANCHOR_PORT, marker.getAsJsonArray("causalAnchorPorts")
                .get(0).getAsString());
    }

    /**
     * An anchor carried by a turn inside the prefix changes nothing: the kept
     * set is the first K_L turns, exactly as it is without an anchor.
     */
    @Test
    public void anAnchorInsideThePrefixKeepsThePrefix() throws Exception {
        load(true, true);

        boolean[] turns = new boolean[14];
        turns[2] = true;

        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8),
                ConcolicRegionRuntime.simulateAnchoredTurnsForTests(
                        TASK, turns));
        assertEquals(0,
                onlyMarker().get("unanchoredTurnsReleased").getAsInt());
    }

    /** Source publications are semantic anchors just like selected RPCs. */
    @Test
    public void configuredSourceTurnsReplacePollingStutters() throws Exception {
        load(true, false, K_L);

        boolean[] turns = new boolean[K_L + 3];
        for (int turn = 2; turn < K_L + 2; turn++) {
            turns[turn] = true;
        }

        assertEquals(Arrays.asList(3, 4, 5, 6, 7, 8, 9, 10),
                ConcolicRegionRuntime.simulateAnchoredTurnsForTests(
                        TASK, turns));
        JsonObject marker = onlyMarker();
        assertEquals(K_L, marker.get("boundedAt").getAsInt());
        assertEquals(K_L, marker.get("anchoredOccurrences").getAsInt());
        assertEquals(2,
                marker.get("unanchoredTurnsReleased").getAsInt());
        assertTrue(marker.getAsJsonArray("causalAnchorPorts").isEmpty());
        assertEquals(K_L, marker.getAsJsonArray(
                "configuredSourceAnchorPhases").size());
    }

    /** Repeating one exact exchange cannot stand in for a missing phase. */
    @Test
    public void repeatedResponseAnchorDoesNotSatisfyAMissingSourcePhase()
            throws Exception {
        load(true, true, 2);
        String firstPhase = sourcePhaseId(1);
        String secondPhase = sourcePhaseId(2);
        String[][] phases = new String[16][];
        String[][] responses = new String[16][];
        phases[0] = new String[]{firstPhase};
        responses[1] = new String[]{ANCHOR_PORT};
        responses[2] = new String[]{ANCHOR_PORT};

        ConcolicRegionRuntime.simulateSemanticAnchorTurnsForTests(
                TASK, phases, responses);
        ConcolicRegionRuntime.publishRunTotals();

        JsonObject gap = onlySkip("CAUSAL_ANCHOR_NOT_OBSERVED");
        JsonArray missing = gap.getAsJsonArray(
                "missingConfiguredSourcePhaseIds");
        assertEquals(1, missing.size());
        assertEquals(secondPhase, missing.get(0).getAsString());
        assertTrue(gap.getAsJsonArray("missingResponseExchanges").isEmpty());
    }

    /** One retained turn may discharge several exact identities at once. */
    @Test
    public void colocatedPhaseAndResponseDoNotCreateAFalseMissingGap()
            throws Exception {
        load(true, true, 1);
        String[][] phases = new String[16][];
        String[][] responses = new String[16][];
        phases[0] = new String[]{sourcePhaseId(1)};
        responses[0] = new String[]{ANCHOR_PORT};

        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8),
                ConcolicRegionRuntime.simulateSemanticAnchorTurnsForTests(
                        TASK, phases, responses));
        ConcolicRegionRuntime.publishRunTotals();

        assertTrue(skipRows("CAUSAL_ANCHOR_NOT_OBSERVED").isEmpty());
        JsonObject marker = onlyMarker();
        assertEquals(1, marker.get("anchoredOccurrences").getAsInt());
        assertEquals(K_L, marker.get("boundedAt").getAsInt());
    }

    /** A released candidate cannot consume the next task-scoped phase. */
    @Test
    public void sourcePhaseOrdinalCommitsOnlyWithAPublishedActivation()
            throws Exception {
        load(true, false, 3);
        String key = "PUBLISH\nSOURCE.test\n" + ROOT + "#u7";

        assertEquals(1, ConcolicRegionRuntime
                .configuredSourcePhaseOrdinalForTests(TASK, key, 1));
        assertEquals("an abandoned activation leaves phase one available",
                1, ConcolicRegionRuntime
                        .configuredSourcePhaseOrdinalForTests(TASK, key, 1));
        ConcolicRegionRuntime.commitConfiguredSourcePhaseOrdinalsForTests(
                TASK, key, 1);
        assertEquals(2, ConcolicRegionRuntime
                .configuredSourcePhaseOrdinalForTests(TASK, key, 1));
    }

    /** An ordinary root's phase catalog is activation-local. */
    @Test
    public void nonLoopSourcePhaseOrdinalRestartsForEveryActivation()
            throws Exception {
        load(false, false, 2);
        String key = "PUBLISH\nSOURCE.test\n" + ROOT + "#u7";

        assertEquals(1, ConcolicRegionRuntime
                .configuredSourcePhaseOrdinalForTests(TASK, key, 1));
        ConcolicRegionRuntime.commitConfiguredSourcePhaseOrdinalsForTests(
                TASK, key, 1);
        assertEquals("a second RPC/root activation starts its own catalog",
                1, ConcolicRegionRuntime
                        .configuredSourcePhaseOrdinalForTests(TASK, key, 1));
    }

    /**
     * FAIL-CLOSED: an anchor that never arrives never substitutes an unrelated
     * polling turn.  K_L still bounds the kept cases and shutdown names the
     * missing selected exchange.
     */
    @Test
    public void anAnchorThatNeverArrivesPublishesANamedGap()
            throws Exception {
        load(true, true);

        List<Integer> kept = ConcolicRegionRuntime
                .simulateAnchoredTurnsForTests(TASK, new boolean[64]);

        assertEquals("one slot stays reserved for the selected exchange",
                Arrays.asList(1, 2, 3, 4, 5, 6, 7), kept);
        ConcolicRegionRuntime.publishRunTotals();

        assertTrue("no bounded marker may pretend the anchor was answered",
                markerRows().isEmpty());
        JsonObject gap = onlySkip("CAUSAL_ANCHOR_NOT_OBSERVED");
        assertEquals(0, gap.get("anchoredOccurrences").getAsInt());
        assertEquals(57,
                gap.get("unanchoredTurnsReleased").getAsInt());
        assertEquals(64, gap.get("turnsAdmitted").getAsInt());
    }

    /**
     * A region the plan bound to no exchange has no anchor to be addressed
     * by, and its bounded occurrence set is byte-identical to today's: the
     * first K_L turns, and a marker that says nothing about an anchor.
     */
    @Test
    public void anAnchorlessRegionIsUnchanged() throws Exception {
        load(true, false);

        boolean[] turns = new boolean[14];
        // Even a turn the VM would have called anchored cannot move a region
        // whose plan named no producer for any port it attaches.
        turns[10] = true;

        assertEquals(Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8),
                ConcolicRegionRuntime.simulateAnchoredTurnsForTests(
                        TASK, turns));

        JsonObject marker = onlyMarker();
        assertEquals(K_L, marker.get("boundedAt").getAsInt());
        assertFalse(marker.toString(), marker.has("causalAnchorPorts"));
        assertFalse(marker.toString(), marker.has("anchoredOccurrences"));
        assertEquals("loop-body region occurrence set bounded at K_L=" + K_L
                        + "; further iterations run concretely without capture",
                marker.get("reason").getAsString());
    }

    /**
     * A port the plan declares but binds to no producer occurrence is not a
     * selected anchor: only the exchange an edge selected this region for is.
     */
    @Test
    public void anUnboundPortIsNotASelectedAnchor() throws Exception {
        load(true, true);

        // The unbound port is declared on the same task; the anchored turn
        // below carries the bound one, and only that one reserves a slot.
        assertEquals(Arrays.asList(ANCHOR_PORT),
                anchorPortsOfMarkerAfterExhaustion());
    }

    /** A non-loop-body region stays uncapped whatever it attaches. */
    @Test
    public void aNonLoopBodyRegionIsStillUncapped() throws Exception {
        load(false, true);

        assertEquals(K_L + 5, ConcolicRegionRuntime
                .simulateAdmissionsForTests(TASK, K_L + 5));
        assertTrue(markerRows().toString(), markerRows().isEmpty());
    }

    private List<String> anchorPortsOfMarkerAfterExhaustion()
            throws Exception {
        boolean[] turns = new boolean[14];
        turns[10] = true;
        ConcolicRegionRuntime.simulateAnchoredTurnsForTests(TASK, turns);
        JsonArray declared = onlyMarker().getAsJsonArray("causalAnchorPorts");
        List<String> ports = new ArrayList<>();
        for (int index = 0; index < declared.size(); index++) {
            ports.add(declared.get(index).getAsString());
        }
        return ports;
    }

    private JsonObject onlyMarker() throws Exception {
        List<JsonObject> markers = markerRows();
        assertEquals(markers.toString(), 1, markers.size());
        return markers.get(0);
    }

    private JsonObject onlySkip(String kind) throws Exception {
        List<JsonObject> rows = skipRows(kind);
        assertEquals(rows.toString(), 1, rows.size());
        return rows.get(0);
    }

    private List<JsonObject> markerRows() throws Exception {
        return skipRows("LOOP_OCCURRENCES_BOUNDED");
    }

    private List<JsonObject> skipRows(String kind) throws Exception {
        List<JsonObject> rows = new ArrayList<>();
        if (!Files.exists(results)) return rows;
        for (String line : Files.readAllLines(results,
                StandardCharsets.UTF_8)) {
            if (line.trim().isEmpty()) continue;
            JsonObject row = new JsonParser().parse(line).getAsJsonObject();
            if ("CONCOLIC_REGION_SKIPPED".equals(
                    row.get("event").getAsString())
                    && kind.equals(
                    row.get("skipKind").getAsString())) {
                rows.add(row);
            }
        }
        return rows;
    }

    private void load(boolean loopBody, boolean boundAnchor)
            throws Exception {
        load(loopBody, boundAnchor, 0);
    }

    private void load(boolean loopBody, boolean boundAnchor,
                      int sourcePhases) throws Exception {
        String name = (loopBody ? "loop" : "flat")
                + (boundAnchor ? "-anchored" : "-anchorless")
                + "-sources-" + sourcePhases;
        Path plan = folder.newFile(name + "-plan.jsonl").toPath();
        Files.write(plan, (task(loopBody, boundAnchor, sourcePhases) + "\n")
                .getBytes(StandardCharsets.UTF_8));
        results = folder.getRoot().toPath().resolve(name + "-results.jsonl");
        System.setProperty("causynth.concolic.task.plan", plan.toString());
        System.setProperty("causynth.concolic.task.id", TASK);
        System.setProperty("causynth.concolic.results", results.toString());
        assertEquals(1,
                ConcolicRegionRuntime.campaignTaskIdsForTests().size());
    }

    private static JsonObject task(boolean loopBody, boolean boundAnchor) {
        return task(loopBody, boundAnchor, 0);
    }

    private static JsonObject task(boolean loopBody, boolean boundAnchor,
                                   int sourcePhases) {
        JsonObject task = new JsonObject();
        task.addProperty("taskId", TASK);
        task.addProperty("goalId", "GOAL." + TASK);
        task.addProperty("sourceKey", SOURCE_KEY);
        task.addProperty("occurrenceId", OCCURRENCE);
        task.addProperty("relationKey", "RELATION.POLLER");
        task.addProperty("regionId", "POLLER");
        task.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", ROOT);
        selector.addProperty("receiverClass", Object.class.getName());
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", SOURCE_KEY);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        task.add("rootSelector", selector);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());

        if (sourcePhases > 0) {
            JsonObject declaration =
                    ConfiguredSourcePhaseContract.declaration(
                            ConfiguredSourcePhaseContract.Phase.PUBLISH,
                            "SOURCE.test", "<example.State: long value>",
                            ROOT, 7);
            JsonArray phases = new JsonArray();
            for (int ordinal = 1; ordinal <= sourcePhases; ordinal++) {
                phases.add(ConfiguredSourcePhaseContract.occurrence(
                        ConfiguredSourcePhaseContract.declarationsOf(
                                singleton(declaration)).get(0),
                        OCCURRENCE, ordinal, 100L + ordinal,
                        200L + ordinal, 300L + ordinal,
                        "<example.Hook: boolean symbolize(java.lang.String,"
                                + "java.lang.Object,java.lang.String)>",
                        Arrays.asList(200L + ordinal, 20L)));
            }
            task.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);
        }

        JsonArray handoffs = new JsonArray();
        handoffs.add(attachPort(ANCHOR_PORT, 9));
        handoffs.add(attachPort(OTHER_PORT, 11));
        task.add("communicationHandoffs", handoffs);

        JsonArray bindings = new JsonArray();
        if (boundAnchor) {
            JsonObject binding = new JsonObject();
            binding.addProperty("kind", "RUNTIME_PROTOCOL_FLOW");
            binding.addProperty("toInputPort", ANCHOR_PORT);
            binding.addProperty("toOccurrenceId", OCCURRENCE);
            binding.addProperty("fromOccurrenceId",
                    "test/peer#epoch0/region/PRODUCER#1");
            bindings.add(binding);
        }
        task.add("edgeBindings", bindings);

        if (loopBody) {
            task.addProperty("rootAuthority", "LOOP_BODY_ROOT");
            JsonObject rootLoop = new JsonObject();
            rootLoop.addProperty("rootLoopMethod", ROOT);
            rootLoop.addProperty("headerUnitIndex", 1);
            rootLoop.addProperty("loopSiteId", ROOT_LOOP_SITE);
            task.add("rootLoop", rootLoop);
        }
        // The root loop declares K_L while an inner walk declares more, so
        // the region's derived ceiling sits above its occurrence budget --
        // exactly the shape of the DN heartbeat region.
        Map<String, Integer> declared = new LinkedHashMap<>();
        declared.put(ROOT_LOOP_SITE, K_L);
        declared.put(INNER_LOOP_SITE, REGION_MAX);
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS, declared)
                .writeTo(task);

        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        task.add("admission", admission);
        return task;
    }

    private static JsonArray singleton(JsonObject value) {
        JsonArray values = new JsonArray();
        values.add(value);
        return values;
    }

    private static String sourcePhaseId(int ordinal) {
        return ConfiguredSourcePhaseContract.phaseId(OCCURRENCE,
                ROOT + "#u7",
                ConfiguredSourcePhaseContract.Phase.PUBLISH, ordinal);
    }

    private static JsonObject attachPort(String portId, int unitIndex) {
        JsonObject port = new JsonObject();
        port.addProperty(CommunicationHandoffSpec.SIDE,
                CommunicationHandoffSpec.IN);
        port.addProperty(CommunicationHandoffSpec.CAPTURE_KIND,
                CommunicationCatalogContract.CAPTURE_CALL_RETURN);
        port.addProperty("portId", portId);
        port.addProperty("handoffLeafPath", "resp/keys");
        port.addProperty("direction", "RESPONSE");
        port.addProperty("javaType", "long");
        port.addProperty("definitionMethod", ROOT);
        port.addProperty("definitionUnitIndex", unitIndex);
        port.addProperty("declaredCallee", CALLEE);
        return port;
    }

    private static void restore(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }
}
