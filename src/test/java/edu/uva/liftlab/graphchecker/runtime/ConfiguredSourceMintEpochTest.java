package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * A model is applied only at a mint this run can place.
 *
 * <p>An occurrence is (node, epoch, region, k-th activation).  A configured
 * source names one mint SITE, and the site is reached once per node
 * lifecycle, so the epoch is the whole of what tells two mints of that site
 * apart.  On hdfs-17960 {@code root=false} landed on the epoch-0 mint --
 * the one the recording made before the NameNode restart -- and rewrote a
 * value the solver had said nothing about.</p>
 *
 * <p>Root admission admits an activation nothing attributed, because absence
 * of evidence is not evidence of another occurrence.  A model is different in
 * kind: it rewrites the recorded execution, so it demands positive evidence
 * and an unattributed mint keeps the recorded value with a named gap.</p>
 */
public class ConfiguredSourceMintEpochTest {
    private static final String NODE = "hdfs/nn0";
    private static final String SOURCE_ID = "CFG.ORDERED";
    private static final String FIELD =
            "<a.Manager: boolean snapshotDeletionOrdered>";
    private static final String METHOD =
            "<a.Manager: boolean isSnapshotDeletionOrdered()>";
    private static final String CALLEE =
            "<a.Manager: boolean isSnapshotDeletionOrdered()>";
    private static final int UNIT = 1;
    private static final String REGION = "REGION.9492ec77";
    private static final String PLANNED =
            NODE + "#epoch1/region/" + REGION + "#1";

    private long token;
    private String occurrenceId = PLANNED;

    @After
    public void releaseRegion() {
        ConcolicRegionRuntime.ACTIVE.remove(token);
        RuntimeTraceContext.resetForTests();
    }

    /**
     * The mint before the restart is refused; the one after it is applied.
     *
     * <p>Same run, same site, same model: what changes is whether the
     * registry can place the mint in the epoch the plan addresses.</p>
     */
    @Test
    public void aMintIsModelledOnlyInTheEpochThePlanAddresses()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        Object manager = new Object();

        // Epoch 0 is registered and the workload has not restarted yet: the
        // registry places this mint at epoch 0, which is not the address.
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 0L));
        assertNull("a mint of another epoch is not modelled",
                assignment(active, manager));
        assertEquals("EPOCH_UNMATCHED", lastGapKind(active));

        // The restart advances the same logical source; the mint that
        // follows it is the one the plan addresses.
        RuntimeTraceContext.restartSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));
        assertNotNull("the epoch-1 mint is modelled",
                assignment(active, manager));
    }

    /** A mint the registry cannot place keeps the value the recording made. */
    @Test
    public void anUnattributedMintRefusesTheModelWithAGap() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();

        assertNull("nothing places this mint, so nothing rewrites it",
                assignment(active, new Object()));

        assertEquals("MINT_UNATTRIBUTED", lastGapKind(active));
        assertTrue(lastGapDetail(active),
                lastGapDetail(active).contains("attributes this mint to no "
                        + "node"));
        assertTrue(lastGapDetail(active),
                lastGapDetail(active).contains("recorded value stands"));
    }

    /** The refusal is diagnostic: the activation says it, not just skips. */
    @Test
    public void theRefusalIsPublishedAsAnUnresolvedInput() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();

        assignment(active, new Object());

        assertTrue(unresolved(active).toString(),
                unresolved(active).toString().contains(
                        "CONFIGURED_SOURCE_PHASE_MINT_UNATTRIBUTED"));
    }

    /** An address that names no epoch is not asked the question at all. */
    @Test
    public void anEpochlessAddressIsUnaffected() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active =
                region("workload/unregistered",
                        "workload/unregistered/region/" + REGION + "#1");

        assertNotNull("nothing to place, nothing to refuse",
                assignment(active, new Object()));
    }


    /**
     * One site is one variable: every occurrence that reaches it is modelled.
     *
     * <p>Lane BG's shape.  {@code SnapshotManager.isSnapshotDeletionOrdered()
     * #u1} is reached by six regions, twice each; the solver flipped it to
     * {@code false} and the replay applied that at exactly one of the twelve
     * identities the site had -- {@code SOURCE_PHASE.f2395415…}, occurrence
     * {@code REGION.9492ec77…#1} -- so every other execution kept the
     * recorded {@code true}, the target region ran under the recorded root
     * and published {@code targetReach.outcome:false}, and COMPOSE refused
     * both target occurrences with TARGET_NOT_REACHED.</p>
     *
     * <p>A configured source is declared by site, so it is one variable per
     * replay and a flip of it is a flip everywhere it is read.</p>
     */
    @Test
    public void everyOccurrenceOfOneSiteAnswersOneValuation()
            throws Exception {
        RuntimeTraceContext.resetForTests();
        Object manager = new Object();
        RuntimeTraceContext.registerSource(manager,
                new SourceRef("CLUSTER_NODE", "NAMENODE", NODE, 1L));

        String first = NODE + "#epoch1/region/" + REGION + "#1";
        String second = NODE + "#epoch1/region/" + REGION + "#2";
        assertEquals("one site, one variable, whatever reached it",
                phaseId(first), phaseId(second));

        ConcolicRegionRuntime.ActiveRegion one =
                region(NODE + "#epoch1", first);
        assertNotNull("the first occurrence is modelled",
                assignment(one, manager));

        ConcolicRegionRuntime.ActiveRegion two =
                region(NODE + "#epoch1", second);
        assertNotNull("and so is the second, on the same valuation",
                assignment(two, manager));
    }

    // ---------- harness ----------

    private ConcolicRegionRuntime.ActiveRegion region() throws Exception {
        return region(NODE + "#epoch1", PLANNED);
    }

    private ConcolicRegionRuntime.ActiveRegion region(String sourceKey,
                                                      String occurrenceId)
            throws Exception {
        this.occurrenceId = occurrenceId;
        ConcolicTaskPlan.RuntimeTask runtime =
                new ConcolicTaskPlan.RuntimeTask(
                        ExecutionTask.decode(task(sourceKey, occurrenceId)));
        token = 970000L + occurrenceId.hashCode() % 1000L;
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token, runtime, null,
                        Thread.currentThread(), false);
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        return active;
    }

    private Object assignment(
            ConcolicRegionRuntime.ActiveRegion active, Object mintOwner)
            throws Exception {
        Method method = active.getClass().getDeclaredMethod(
                "configuredSourceAssignment", String.class, String.class,
                String.class, Object.class);
        method.setAccessible(true);
        return method.invoke(active, phaseId(occurrenceId),
                SOURCE_ID, FIELD, mintOwner);
    }

    @SuppressWarnings("unchecked")
    private static JsonObject lastGap(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        Field field = active.getClass().getDeclaredField(
                "configuredSourcePhaseGaps");
        field.setAccessible(true);
        List<JsonObject> gaps = (List<JsonObject>) field.get(active);
        return gaps.isEmpty() ? new JsonObject()
                : gaps.get(gaps.size() - 1);
    }

    private static String lastGapKind(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        return lastGap(active).has("gapKind")
                ? lastGap(active).get("gapKind").getAsString() : "";
    }

    private static String lastGapDetail(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        return lastGap(active).has("detail")
                ? lastGap(active).get("detail").getAsString() : "";
    }

    @SuppressWarnings("unchecked")
    private static Collection<String> unresolved(
            ConcolicRegionRuntime.ActiveRegion active) throws Exception {
        Field field = active.getClass().getDeclaredField("unresolved");
        field.setAccessible(true);
        return (Collection<String>) field.get(active);
    }

    private static String phaseId(String occurrenceId) {
        return ConfiguredSourcePhaseContract.phaseId(SOURCE_ID,
                edu.uva.liftlab.graphchecker.contract.SiteId.of(METHOD, UNIT),
                ConfiguredSourcePhaseContract.Phase.PUBLISH);
    }

    private static JsonObject task(String sourceKey, String occurrenceId) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", REGION);
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", sourceKey);
        encoded.addProperty("occurrenceId", occurrenceId);
        encoded.addProperty("rootMethod", "<a.B: void run()>");
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
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

        JsonObject declaration = ConfiguredSourcePhaseContract.declaration(
                ConfiguredSourcePhaseContract.Phase.PUBLISH, SOURCE_ID,
                FIELD, METHOD, UNIT);
        JsonArray declarations = new JsonArray();
        declarations.add(declaration);
        JsonArray phases = new JsonArray();
        phases.add(ConfiguredSourcePhaseContract.occurrence(
                ConfiguredSourcePhaseContract.declarationsOf(declarations)
                        .get(0),
                occurrenceId, 1, 11L, 7L, 3L, CALLEE, Arrays.asList(7L, 5L)));
        encoded.add(ConfiguredSourcePhaseContract.PLAN_FIELD, phases);

        JsonObject model = new JsonObject();
        model.addProperty("modelAssignmentKey", "MODEL.1");
        model.addProperty("inputSymbol",
                "SOURCE_PHASE:" + phaseId(occurrenceId));
        model.addProperty("valueType", "BOOLEAN");
        model.addProperty("value", "false");
        model.addProperty("configuredSourcePhaseId",
                phaseId(occurrenceId));
        model.addProperty("configuredSourceId", SOURCE_ID);
        model.addProperty("configuredSourceFieldSignature", FIELD);
        JsonArray models = new JsonArray();
        models.add(model);
        encoded.add("modelAssignments", models);
        return encoded;
    }
}
