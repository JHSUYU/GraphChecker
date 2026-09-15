package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

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
    }

    @After
    public void releaseRegions() {
        opened.forEach(ConcolicRegionRuntime.ACTIVE::remove);
        opened.clear();
        RuntimeTraceContext.resetForTests();
    }

    /**
     * A mint publishes the value it read -- and only a value it read.
     *
     * <p>A clock is the one root every execution reads differently:
     * {@code recordedValue} is the seed's reading, {@code observedValue}
     * this run's instant.  A replay that wrote a model read it back, and
     * calling that "recorded" makes a counterfactual the recording.</p>
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
        assertEquals("<org.apache.hadoop.util.Timer: long now()>",
                clock.get("declaredCallee").getAsString());
        assertEquals("the seed's reading, which the window is centred on",
                "1789358343989", clock.get("recordedValue").getAsString());
        assertEquals("and this execution's own instant, beside it",
                "1789358344655", clock.get("observedValue").getAsString());
    }

    /**
     * A model for a mint site is owed by the activation that minted it.
     *
     * <p>A model is written into the value the mint is about to symbolize,
     * so an activation that never reached the site has nothing to write it
     * into -- and neither has a reuse of an already symbolic root.</p>
     */
    @Test
    public void theModelIsOwedOnlyByTheActivationThatMintedIt()
            throws Exception {
        assertFalse("nothing was minted for this phase here",
                owesModel(false, false));
        assertTrue("this activation minted it, so the model is its own",
                owesModel(true, false));
        assertFalse("a reuse is not a mint",
                owesModel(true, true));
    }

    /**
     * A model is applied only at a mint this run can place.
     *
     * <p>A configured source names one mint SITE reached once per node
     * lifecycle, so the epoch tells two mints of it apart and a model at
     * the wrong epoch rewrites a value the solver said nothing about.  A
     * model demands positive evidence, so an unattributed mint keeps the
     * recorded value with a named gap.</p>
     */
    @Test
    public void aModelIsAppliedOnlyAtAMintThisRunCanPlace() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active =
                phaseRegion(NODE + "#epoch1", PLANNED);
        Object manager = new Object();
        // Epoch 0 is registered and nothing restarted yet, so the registry
        // places this mint at epoch 0 -- not the epoch the plan addresses.
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));
        assertNull("a mint of another epoch is not modelled",
                assignment(active, manager));
        assertEquals("EPOCH_UNMATCHED", gap(active, "gapKind"));

        // The restart advances the same logical source.
        RuntimeTraceContext.restartSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));
        assertNotNull("the epoch-1 mint is modelled",
                assignment(active, manager));
        ConcolicRegionRuntime.ActiveRegion orphan =
                phaseRegion(NODE + "#epoch1", PLANNED);
        assertNull("nothing places this mint, so nothing rewrites it",
                assignment(orphan, new Object()));
        assertEquals("MINT_UNATTRIBUTED", gap(orphan, "gapKind"));
        String detail = gap(orphan, "detail");
        assertTrue(detail, detail.contains("attributes this mint to no node"));
        assertTrue(detail, detail.contains("recorded value stands"));

        ConcolicRegionRuntime.ActiveRegion epochless =
                phaseRegion("workload/unregistered",
                        "workload/unregistered/region/" + REGION + "#1");
        assertNotNull("nothing to place, nothing to refuse",
                assignment(epochless, new Object()));
    }

    /**
     * One site is one variable: every occurrence that reaches it is modelled.
     *
     * <p>A site reached by six regions twice each has twelve identities;
     * applying a flip at one of them leaves every other execution on the
     * recorded value.  A configured source is declared by site, so a flip
     * of it is a flip everywhere it is read.</p>
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

        assertNotNull("the first occurrence is modelled",
                assignment(phaseRegion(NODE + "#epoch1", PLANNED), manager));
        assertNotNull("and so is the second, on the same valuation",
                assignment(phaseRegion(NODE + "#epoch1", second), manager));
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
    private boolean owesModel(boolean minted, boolean reused)
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = manualRegion();
        if (minted) {
            JsonObject mint = new JsonObject();
            mint.addProperty("sourcePhaseId", MINT_PHASE);
            mint.addProperty("reused", reused);
            symbolizedRows(active).add(mint);
        }
        Method owes = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("owesConfiguredSourceModel", String.class);
        owes.setAccessible(true);
        return (Boolean) owes.invoke(active, MINT_PHASE);
    }

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
        encoded.addProperty("declaredCallee",
                "<org.apache.hadoop.util.Timer: long now()>");
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", "1789358343989");
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

    private Object assignment(ConcolicRegionRuntime.ActiveRegion active,
                              Object mintOwner) throws Exception {
        Method method = active.getClass().getDeclaredMethod(
                "configuredSourceAssignment", String.class, String.class,
                String.class, Object.class);
        method.setAccessible(true);
        return method.invoke(active, phaseId(occurrenceId), SOURCE_ID, FIELD,
                mintOwner);
    }

    /** One member of the last gap this activation filed, or "". */
    @SuppressWarnings("unchecked")
    private static String gap(ConcolicRegionRuntime.ActiveRegion active,
                              String member) throws Exception {
        Field field = active.getClass().getDeclaredField(
                "configuredSourcePhaseGaps");
        field.setAccessible(true);
        List<JsonObject> gaps = (List<JsonObject>) field.get(active);
        JsonObject last = gaps.isEmpty() ? new JsonObject()
                : gaps.get(gaps.size() - 1);
        return last.has(member) ? last.get(member).getAsString() : "";
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
        encoded.add("branches", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
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
                occurrence, 1, 11L, 7L, 3L, PHASE_METHOD,
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
