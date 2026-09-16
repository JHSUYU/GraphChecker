package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ObligationDir;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.GapRow;
import edu.uva.liftlab.graphchecker.contract.RowCodec;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import org.junit.After;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The mint is the unit: what it publishes, and what it owes.
 *
 * <p>A manual mint published no {@code recordedValue}, so lane VM12's
 * {@code DelegationKey.expiryDate} was refused RECORDED_ROOT_VALUE_UNSTATED.
 * The other half of the unit is the occurrence a mint can be placed at: a
 * model rewrites the recorded execution, so it applies only where the
 * registry can place this mint at the address the plan named.</p>
 */
public class ManualMintStatesItsValueTest {
    @Rule
    public final TemporaryFolder session = new TemporaryFolder();

    private static final String METHOD = "<a.B: void run()>";
    private static final String MANUAL_REGION = "REGION.aaa1cfd7";
    private static final String MANUAL_SOURCE = "hdfs-17899/nn0#epoch0";
    private static final String MINT_PHASE = "SOURCE_PHASE.0b2b2a3d";
    private static final String NODE = "hdfs/nn0";
    private static final String SOURCE_ID = "CFG.ORDERED";
    private static final String FIELD =
            "<a.Manager: boolean snapshotDeletionOrdered>";
    private static final String PHASE_METHOD =
            "<a.Manager: boolean isSnapshotDeletionOrdered()>";
    private static final int UNIT = 1;
    private static final String REGION = "REGION.9492ec77";
    private static final String PLANNED =
            NODE + "#epoch1/region/" + REGION + "#1";

    private final List<Long> opened = new ArrayList<>();
    private String occurrenceId = PLANNED;

    @Before
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
        RowRuntime.resetForTests();
    }

    @After
    public void releaseRegions() {
        opened.forEach(ConcolicRegionRuntime.ACTIVE::remove);
        opened.clear();
        RuntimeTraceContext.resetForTests();
        System.clearProperty(FocusedReplay.PLAN_PROPERTY);
        RowRuntime.resetForTests();
    }

    /**
     * A mint publishes the value it read -- and only a value it read.
     *
     * <p>A clock is no exception.  The seed replay IS the reference
     * execution the composer's clock deltas are relative to, so the instant
     * THIS run read is what both members state; the row used to publish the
     * PLAN's instant as {@code recordedValue}, which made every delta
     * relative to an execution nobody ran.  A replay that wrote a model read
     * it back and states neither: calling that "recorded" makes a
     * counterfactual the recording.</p>
     */
    @Test
    public void aMintStatesTheValueItRead() throws Exception {
        JsonObject recorded = manualRow(action("PORT.now"), "1789358343989");
        assertEquals("MANUAL_SYMBOLIC_INPUT_OBSERVATION",
                recorded.get("kind").getAsString());
        assertTrue("the mint states what it read",
                recorded.has("recordedValue"));
        assertEquals("1789358343989",
                recorded.get("recordedValue").getAsString());
        assertEquals("J", recorded.get("javaType").getAsString());
        assertTrue(recorded.get("minted").getAsBoolean());

        JsonObject modelled = manualRow(action("PORT.now"), "");
        assertFalse("a counterfactual is not a recording",
                modelled.has("recordedValue"));
        assertEquals("J", modelled.get("javaType").getAsString());

        JsonObject clock = manualRow(clockAction(), "1789358344655");
        assertTrue("the mint states the clock the case declared",
                clock.get("clock").getAsBoolean());
        assertEquals("this execution's own instant, which the window is "
                        + "centred on", "1789358344655",
                clock.get("observedValue").getAsString());
        assertEquals("and the same instant as what this run recorded: the "
                        + "seed replay is the reference execution",
                clock.get("observedValue").getAsString(),
                clock.get("recordedValue").getAsString());
        assertEquals("the plan's instant is stated by nothing here",
                7L, clock.get("eventSeq").getAsLong());

        JsonObject plantedClock = manualRow(clockAction(), "");
        assertTrue("still a declared clock",
                plantedClock.get("clock").getAsBoolean());
        assertFalse("a planted instant is not a recording",
                plantedClock.has("recordedValue"));
        assertFalse("and states no observation either",
                plantedClock.has("observedValue"));

        // What the wave asks of a clock is a SKEW, and the mint applies it
        // to the instant THIS run read: a model is an instant of the
        // recording's window, and writing it absolutely would rewind the
        // clock to an epoch no replay reads.  An ordinary root keeps its
        // absolute value, and both come out of one decision.
        focusRow("{\"taskId\":\"TASK.1\",\"obligationId\":\"OBL.1\","
                + "\"pathId\":\"PATH.1\",\"seedSessionId\":\"s-seed\","
                + "\"focused\":\"" + PLANNED_ADDRESS + "\","
                + "\"flip\":{\"siteId\":\"Arrival#u8\",\"ordinal\":1,"
                + "\"outcome\":true},"
                + "\"rootAssignments\":{\"CASE.SERIAL\":\"12\"},"
                + "\"clockDeltas\":{\"CASE.NOW\":\"-4200\"},"
                + "\"rootMints\":{\"CASE.SERIAL\":\"" + MINT_ADDRESS
                + "\"},"
                + "\"answers\":{},\"unproducible\":[]}");
        ConcolicRegionRuntime.ActiveRegion focused = manualRegion();
        focused.d3Address = edu.uva.liftlab.graphchecker.contract
                .OccurrenceAddress.parse(PLANNED_ADDRESS);
        assertEquals("the skew moves this replay's own reading",
                "1789358340455",
                focusedRootValue(focused, "CASE.NOW",
                        Long.valueOf(1789358344655L)));
        assertEquals("a value is a value", "12",
                focusedRootValue(focused, "CASE.SERIAL", Long.valueOf(7L)));
        assertEquals("nothing was asked of this root", "",
                focusedRootValue(focused, "CASE.OTHER", Long.valueOf(7L)));

        // THE FOCUSED SET holds the MINT of every root the obligation
        // assigns, not only the occurrence the flip is about: an assignment
        // is planted where the run mints it, and 11741's SERIAL_NO is
        // minted in nn0's rotation while the flip is the balancer's.  A
        // focused replay is one run of the whole workload, so both run
        // symbolic in it.
        ConcolicRegionRuntime.ActiveRegion minting = manualRegion();
        minting.d3Address = edu.uva.liftlab.graphchecker.contract
                .OccurrenceAddress.parse(MINT_ADDRESS);
        assertEquals("the value is planted at the mint the row names", "12",
                focusedRootValue(minting, "CASE.SERIAL", Long.valueOf(7L)));
        ConcolicRegionRuntime.ActiveRegion alongside = manualRegion();
        alongside.d3Address = edu.uva.liftlab.graphchecker.contract
                .OccurrenceAddress.parse(ALONGSIDE_ADDRESS);
        assertEquals("and nowhere else: a region that merely runs alongside "
                        + "would make the run state what the obligation "
                        + "never asked", "",
                focusedRootValue(alongside, "CASE.SERIAL",
                        Long.valueOf(7L)));

        // A FIELD mint asks the same one decision.  It did not: a declared
        // INTEGRAL cell minted through symbolizeField/materializeField
        // published what the recording read, whatever the obligation
        // assigned, and 11741 session 869a1f0e285913ad-6f59cb84 states
        // SERIAL_NO = 182907 under an obligation assigning 182910.
        KeyManager keys = new KeyManager();
        keys.serialNo = 182907;
        // A model rewrites the recorded execution, so it is written only at
        // a mint this run can place at the node and epoch the plan names --
        // the same rule the configured source's assignment goes through.
        RuntimeTraceContext.registerSource(keys,
                new SourceRef("CLUSTER_NODE", "NAMENODE", "hdfs-17899/nn0",
                        0L));
        assertEquals("the wave's value is unplanted until a mint plants it",
                Collections.singletonMap("CASE.SERIAL", "12"),
                FocusedReplay.unplantedAssignments());
        assertEquals("a field mint that planted states no recordedValue", "",
                ConcolicRegionRuntime.fieldMintRecordedValue(focused,
                        new ConcolicRegionRuntime.SymbolizeAction(
                                action("CASE.SERIAL")),
                        keys, SERIAL_FIELD, "I", Integer.valueOf(182907)));
        assertEquals("and the region reads the wave's value back",
                12, keys.serialNo);
        assertTrue("so the replay owes no ASSIGNMENT_UNPLANTED refusal",
                FocusedReplay.unplantedAssignments().isEmpty());

        // A root the wave said nothing about keeps its reading, and states
        // it: the recording is what every delta is relative to.
        keys.serialNo = 182907;
        assertEquals("a mint that planted nothing states what it read",
                "182907", ConcolicRegionRuntime.fieldMintRecordedValue(
                        focused, new ConcolicRegionRuntime.SymbolizeAction(
                                action("CASE.OTHER")),
                        keys, SERIAL_FIELD, "I", Integer.valueOf(182907)));
        assertEquals("and reads its own value back", 182907, keys.serialNo);
    }

    /** One declared INTEGRAL cell, as 11741's SERIAL_NO is minted. */
    private static final class KeyManager {
        private int serialNo;
    }

    private static final String SERIAL_FIELD =
            "<edu.uva.liftlab.graphchecker.runtime.ManualMintStatesItsValue"
                    + "Test$KeyManager: int serialNo>";

    /** The rendered v3 address the focus row names and the region carries. */
    private static final String PLANNED_ADDRESS =
            "hdfs/nn0#epoch1/region/" + MANUAL_REGION
                    + "/ctx:Root:CLIENT#1/idx:";
    /**
     * Another occurrence entirely: where the recording mints the root the
     * flip depends on.
     *
     * <p>11741's shape -- {@code HDFS.BLOCK_KEY.SERIAL_NO} is minted in
     * nn0's key rotation and read by the balancer, so the occurrence the
     * flip is about mints nothing.</p>
     */
    private static final String MINT_ADDRESS =
            "hdfs/dn1#epoch0/region/REGION.53092d3e/ctx:Root:CLIENT#1/idx:";
    /** And one the wave named nowhere, which merely runs alongside. */
    private static final String ALONGSIDE_ADDRESS =
            "hdfs/dn0#epoch0/region/REGION.094a8e3d/ctx:Root:CLIENT#1/idx:";

    /** Writes one focus row where this replay looks for it. */
    private void focusRow(String row) throws Exception {
        java.nio.file.Path dir = java.nio.file.Files.createTempDirectory(
                "causynth-focus");
        java.nio.file.Files.write(dir.resolve(ObligationDir.FOCUSED_TASK),
                (row + System.lineSeparator()).getBytes("UTF-8"));
        System.setProperty(FocusedReplay.PLAN_PROPERTY,
                dir.resolve("execution_task_plan.jsonl").toString());
        FocusedReplay.resetForTests();
    }

    /** The one decision every mint takes about the wave's value. */
    private static String focusedRootValue(
            ConcolicRegionRuntime.ActiveRegion active, String rootId,
            Object observed) throws Exception {
        Method value = ConcolicRegionRuntime.class.getDeclaredMethod(
                "focusedRootValue",
                ConcolicRegionRuntime.ActiveRegion.class, String.class,
                Object.class);
        value.setAccessible(true);
        return (String) value.invoke(null, active, rootId, observed);
    }

    /**
     * The wave's value is written only at a mint this run can place.
     *
     * <p>A configured source names one mint SITE reached once per node
     * lifecycle, so the epoch tells two mints of it apart and an assignment
     * at the wrong epoch rewrites a value the wave said nothing about.  A
     * write demands positive evidence, so an unattributed mint keeps the
     * recorded value with a named gap.</p>
     */
    @Test
    public void aModelIsAppliedOnlyAtAMintThisRunCanPlace() throws Exception {
        openSession();
        ConcolicRegionRuntime.ActiveRegion active =
                phaseRegion(NODE + "#epoch1", PLANNED);
        Object manager = new Object();
        // Epoch 0 is registered and nothing restarted yet, so the registry
        // places this mint at epoch 0 -- not the epoch the plan addresses.
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));
        assertFalse("a mint of another epoch is not written",
                placeable(active, manager));
        assertEquals(GapKind.EPOCH_UNMATCHED, gap().kind());
        assertTrue("a mint the wave's value was not written at blocks",
                gap().blocking());

        // The restart advances the same logical source.
        RuntimeTraceContext.restartSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));
        assertTrue("the epoch-1 mint is placeable",
                placeable(active, manager));
        ConcolicRegionRuntime.ActiveRegion orphan =
                phaseRegion(NODE + "#epoch1", PLANNED);
        assertFalse("nothing places this mint, so nothing rewrites it",
                placeable(orphan, new Object()));
        assertEquals(GapKind.MINT_UNATTRIBUTED, gap().kind());
        String detail = gap().detail();
        assertTrue(detail, detail.contains("attributes this mint to no node"));
        assertTrue(detail, detail.contains("recorded value stands"));

        ConcolicRegionRuntime.ActiveRegion epochless =
                phaseRegion("workload/unregistered",
                        "workload/unregistered/region/" + REGION + "#1");
        assertTrue("nothing to place, nothing to refuse",
                placeable(epochless, new Object()));
        assertEquals("and files nothing", GapKind.MINT_UNATTRIBUTED,
                gap().kind());
    }

    /**
     * One site is one variable: every occurrence that reaches it is modelled.
     *
     * <p>A site reached by six regions twice each has twelve identities;
     * applying a flip at one of them leaves every other execution on the
     * recorded value.  A configured source is declared by site, so a flip
     * of it is a flip everywhere it is read.</p>
     *
     * <p>And the catalog is not a budget.  It used to be: the plan listed the
     * executions the RECORDING made, the runtime counted the reads a REPLAY
     * made against that size, and read n+1 was refused
     * {@code DECLARATION_MISSING ... exceeds the frozen phase catalog size n}
     * -- two of them on the hdfs-17960 flip replays, whose second read of
     * the marker was the wave's own re-read of the value it had just
     * written.  So the published occurrence row states no ordinal at all,
     * and a row set of any size names one variable.</p>
     */
    @Test
    public void everyOccurrenceOfOneSiteAnswersOneValuation()
            throws Exception {
        Object manager = new Object();
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

        String second = NODE + "#epoch1/region/" + REGION + "#2";
        assertEquals("one site, one variable, whatever reached it",
                phaseId(PLANNED), phaseId(second));

        assertTrue("the first occurrence is placeable",
                placeable(phaseRegion(NODE + "#epoch1", PLANNED), manager));
        assertTrue("and so is the second, on the same valuation",
                placeable(phaseRegion(NODE + "#epoch1", second), manager));

        // The row says WHERE the recording observed the site, and nothing
        // about which read of it a replay is making.
        JsonObject row = phaseTask(NODE + "#epoch1", PLANNED)
                .getAsJsonArray(ConfiguredSourcePhaseContract.PLAN_FIELD)
                .get(0).getAsJsonObject();
        assertFalse("no per-occurrence ordinal is published",
                row.has("baselineOrdinal"));
        assertEquals("and the symbol is the site's", 1,
                oneSymbolPerSite(row).size());
    }

    /** Every VM label a catalog of one site asks for: exactly one. */
    private static java.util.Set<String> oneSymbolPerSite(JsonObject row) {
        JsonArray catalog = new JsonArray();
        catalog.add(row.deepCopy());
        JsonObject later = row.deepCopy();
        // A second execution of the SAME site, as the plan records it.
        later.addProperty("eventSeq", row.get("eventSeq").getAsLong() + 1L);
        later.addProperty("invocationId",
                row.get("invocationId").getAsLong() + 1L);
        catalog.add(later);
        java.util.Set<String> labels = new java.util.LinkedHashSet<String>();
        for (ConfiguredSourcePhaseContract.Occurrence phase
                : ConfiguredSourcePhaseContract.occurrencesOf(catalog)) {
            labels.add(ConfiguredSourcePhaseContract.engineLabelForPhase(
                    phase.phaseId(), phase.sourceId()));
        }
        return labels;
    }

    /** The published row, as the runtime writes it for one manual mint. */
    private JsonObject manualRow(JsonObject encoded, String recordedValue)
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = manualRegion();
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "J");
        expression.addProperty("_exp",
                "M_J_field_REGION.aaa1cfd7.in.f30dbb22_java/lang/Long");

        Method record = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("recordManualSymbolization",
                        ConcolicRegionRuntime.SymbolizeAction.class,
                        String.class, List.class, String.class,
                        com.google.gson.JsonElement.class, boolean.class,
                        boolean.class, String.class);
        record.setAccessible(true);
        record.invoke(active,
                new ConcolicRegionRuntime.SymbolizeAction(encoded),
                "PORT.now", Collections.emptyList(),
                "<org.apache.hadoop.security.token.delegation.DelegationKey:"
                        + " long expiryDate>", expression, true, false,
                recordedValue);

        List<JsonObject> published = symbolizedRows(active);
        assertEquals(1, published.size());
        return published.get(0);
    }

    /** Whether an activation that minted (or reused) the root owes it. */
    @SuppressWarnings("unchecked")
    private static List<JsonObject> symbolizedRows(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        Field rows = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("symbolizedRows");
        rows.setAccessible(true);
        return (List<JsonObject>) rows.get(active);
    }

    /** The same action, as the plan carries a declared clock read. */
    private static JsonObject clockAction() {
        JsonObject encoded = action("REGION.aaa1cfd7.in.f30dbb22");
        encoded.addProperty("rootKind", "CALL_RETURN");
        encoded.addProperty("clock", true);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", "1789358343989");
        encoded.addProperty("eventSeq", 7L);
        return encoded;
    }

    /** One frozen SYMBOLIC action, as the plan carries it. */
    private static JsonObject action(String symbol) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", symbol);
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("cell", "<org.apache.hadoop.util.Timer: long "
                + "now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        return encoded;
    }

    private ConcolicRegionRuntime.ActiveRegion manualRegion() throws Exception {
        return open(task(MANUAL_REGION, MANUAL_SOURCE,
                MANUAL_SOURCE + "/region/" + MANUAL_REGION + "#1"));
    }

    private ConcolicRegionRuntime.ActiveRegion phaseRegion(String sourceKey,
                                                           String occurrence)
            throws Exception {
        this.occurrenceId = occurrence;
        return open(phaseTask(sourceKey, occurrence));
    }

    private ConcolicRegionRuntime.ActiveRegion open(JsonObject encoded)
            throws Exception {
        ConcolicTaskPlan.RuntimeTask runtime =
                new ConcolicTaskPlan.RuntimeTask(ExecutionTask.decode(encoded));
        long token = 970001L + opened.size();
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token, runtime, null,
                        Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        opened.add(token);
        return active;
    }

    /** Whether this run can place this mint where the plan addresses it. */
    private static boolean placeable(
            ConcolicRegionRuntime.ActiveRegion active, Object mintOwner)
            throws Exception {
        Method method = active.getClass().getDeclaredMethod(
                "mintIsPlaceable", Object.class);
        method.setAccessible(true);
        return (Boolean) method.invoke(active, mintOwner);
    }

    /** The last gap ROW this session published: one gap vocabulary. */
    private GapRow gap() throws Exception {
        List<GapRow> rows = RowCodec.readAll(SessionDir.of(
                        session.getRoot().toPath().resolve("iteration-0000"),
                        RowRuntime.sessionId()).gaps(),
                RowCodec::readGap);
        return rows.isEmpty() ? null : rows.get(rows.size() - 1);
    }

    /** Opens the session the refusals are published into. */
    private void openSession() throws Exception {
        java.nio.file.Path results = session.getRoot().toPath()
                .resolve("iteration-0000").resolve("seed-result")
                .resolve("concolic_region_results.jsonl");
        java.nio.file.Files.createDirectories(results.getParent());
        RowRuntime.configure(results);
    }

    private static String phaseId(String occurrenceId) {
        return ConfiguredSourcePhaseContract.phaseId(SOURCE_ID,
                SiteId.of(PHASE_METHOD, UNIT),
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
    }

    /** One executable task row, as the plan carries it. */
    private static JsonObject task(String regionId, String sourceKey,
                                   String occurrenceId) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", regionId);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", sourceKey);
        encoded.addProperty("occurrenceId", occurrenceId);
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        selector.addProperty("method", METHOD);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", sourceKey);
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branchMethods", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        loopBound.addProperty("defaultBackedgeTraversals", 8);
        encoded.add("loopBound", loopBound);
        return encoded;
    }

    /** The same row, declaring one configured-source phase and its model. */
    private static JsonObject phaseTask(String sourceKey, String occurrence) {
        JsonObject encoded = task(REGION, sourceKey, occurrence);
        JsonArray declarations = new JsonArray();
        declarations.add(ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH, SOURCE_ID,
                FIELD, PHASE_METHOD, UNIT));
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0),
                occurrence, 11L, 7L, 3L, PHASE_METHOD,
                Arrays.asList(7L, 5L)));
        encoded.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);

        JsonObject model = new JsonObject();
        model.addProperty("modelAssignmentKey", "MODEL.1");
        model.addProperty("inputSymbol",
                "SOURCE_PHASE:" + phaseId(occurrence));
        model.addProperty("valueType", "BOOLEAN");
        model.addProperty("value", "false");
        model.addProperty("configuredSourcePhaseId", phaseId(occurrence));
        model.addProperty("configuredSourceId", SOURCE_ID);
        model.addProperty("configuredSourceFieldSignature", FIELD);
        JsonArray models = new JsonArray();
        models.add(model);
        encoded.add("modelAssignments", models);
        return encoded;
    }
}
