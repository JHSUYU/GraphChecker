package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * The mint is the unit: what it publishes, and what it owes.
 *
 * <p>A configured-source mint publishes {@code recordedValue} on its
 * evidence row; a manual one published none, so a root the composer met
 * through a manual input had no recorded value to lower. On lane VM12 that
 * is {@code DelegationKey.expiryDate}, minted as
 * {@code M_J_field_REGION.aaa1cfd7...}, and RECORDED_ROOT_VALUE_UNSTATED was
 * the anchor's last refusal on a bug3 corpus whose twelve paths were
 * otherwise composed.</p>
 *
 * <p>The suppression rule is the configured source's too, and is what the
 * second case pins: a replay that wrote a model into the value read the
 * model back, and publishing that as "recorded" is how a counterfactual
 * becomes the recording.</p>
 */
public class ManualMintStatesItsValueTest {
    private static final String METHOD = "<a.B: void run()>";

    @After
    public void clearRegistry() {
        RuntimeTraceContext.resetForTests();
    }

    /** A manual mint publishes the value it read. */
    @Test
    public void aManualMintStatesItsRecordedValue() throws Exception {
        JsonObject row = manualRow("1789358343989");

        assertEquals("MANUAL_SYMBOLIC_INPUT_OBSERVATION",
                row.get("kind").getAsString());
        assertTrue("the mint states what it read",
                row.has("recordedValue"));
        assertEquals("1789358343989",
                row.get("recordedValue").getAsString());
        assertEquals("J", row.get("javaType").getAsString());
        assertTrue(row.get("minted").getAsBoolean());
    }

    /**
     * A clock mint states both readings: the recording's and this one's.
     *
     * <p>A clock is the one root every execution genuinely reads
     * differently.  {@code recordedValue} is the seed's reading, because
     * that is the centre of the window the case's declared skew allows;
     * {@code observedValue} is this execution's own instant, which the
     * per-path window is centred on instead.  Publishing only one of them
     * makes one of those two windows unstatable.</p>
     */
    @Test
    public void aClockMintStatesTheRecordingsReadingAndItsOwn()
            throws Exception {
        JsonObject row = manualRow(clockAction(), "1789358344655");

        assertEquals("<org.apache.hadoop.util.Timer: long now()>",
                row.get("declaredCallee").getAsString());
        assertEquals("the seed's reading, which the window is centred on",
                "1789358343989", row.get("recordedValue").getAsString());
        assertEquals("and this execution's own instant, beside it",
                "1789358344655", row.get("observedValue").getAsString());
    }

    /** A mint that returned a model value states no recorded value. */
    @Test
    public void aModelledMintStatesNoRecordedValue() throws Exception {
        JsonObject row = manualRow("");

        assertFalse("a counterfactual is not a recording",
                row.has("recordedValue"));
        assertEquals("J", row.get("javaType").getAsString());
    }

    /**
     * A model for a mint site is owed by the activation that reaches it.
     *
     * <p>Lane VM12: six companions addressed at REGION.08ab84c9 carried the
     * serialNo model whose mint site is in {@code updateKeys()} --
     * REGION.aaa1cfd7, another member of the same linked group -- and were
     * refused at their terminal for not applying a model that was never
     * theirs to apply. The site is reached by whichever activation runs it;
     * one that did not reach it minted nothing to write the model into.</p>
     */
    @Test
    public void anActivationThatNeverMintedThePhaseOwesNothing()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();

        assertFalse("nothing was minted for this phase here",
                owesModel(active, "SOURCE_PHASE.0b2b2a3d"));
    }

    /** An activation that minted it fresh is asked for the model. */
    @Test
    public void anActivationThatMintedThePhaseStillOwesTheModel()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        mintRow(active, "SOURCE_PHASE.0b2b2a3d", false);

        assertTrue("this activation minted it, so the model is its own",
                owesModel(active, "SOURCE_PHASE.0b2b2a3d"));
    }

    /**
     * An activation that found the root already symbolic owes nothing.
     *
     * <p>Lane VM14's remaining two: companions addressed at
     * REGION.08ab84c9#2, the second activation of a site activation #1 had
     * already minted. A model is written into the value the mint is about
     * to symbolize; a reuse has nothing to write it into, and "one variable
     * per phase" is exactly why there is nothing to mint the second
     * time.</p>
     */
    @Test
    public void anActivationThatReusedTheRootOwesNothing()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        mintRow(active, "SOURCE_PHASE.0b2b2a3d", true);

        assertFalse("a reuse is not a mint",
                owesModel(active, "SOURCE_PHASE.0b2b2a3d"));
    }

    private static void mintRow(ConcolicRegionRuntime.ActiveRegion active,
                                String phaseId, boolean reused)
            throws Exception {
        JsonObject mint = new JsonObject();
        mint.addProperty("sourcePhaseId", phaseId);
        mint.addProperty("reused", reused);
        Field rows = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("symbolizedRows");
        rows.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<JsonObject> published = (List<JsonObject>) rows.get(active);
        published.add(mint);
    }

    private static boolean owesModel(
            ConcolicRegionRuntime.ActiveRegion active, String phaseId)
            throws Exception {
        Method owes = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("owesConfiguredSourceModel",
                        String.class);
        owes.setAccessible(true);
        return (Boolean) owes.invoke(active, phaseId);
    }

    /** The published row, as the runtime writes it for one manual mint. */
    private static JsonObject manualRow(String recordedValue)
            throws Exception {
        return manualRow(symbolizeAction(), recordedValue);
    }

    private static JsonObject manualRow(Object action, String recordedValue)
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region();
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "SymbolExpression");
        expression.addProperty("_java_type", "J");
        expression.addProperty("_exp",
                "M_J_field_REGION.aaa1cfd7.in.f30dbb22_java/lang/Long");

        Method record = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredMethod("recordManualSymbolization",
                        action.getClass(), String.class, List.class,
                        String.class, com.google.gson.JsonElement.class,
                        boolean.class, boolean.class, String.class);
        record.setAccessible(true);
        record.invoke(active, action, "PORT.now", Collections.emptyList(),
                "<org.apache.hadoop.security.token.delegation.DelegationKey:"
                        + " long expiryDate>", expression, true, false,
                recordedValue);

        Field rows = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("symbolizedRows");
        rows.setAccessible(true);
        @SuppressWarnings("unchecked")
        List<JsonObject> published = (List<JsonObject>) rows.get(active);
        assertEquals(1, published.size());
        return published.get(0);
    }

    /** The same action, as the plan carries a declared clock read. */
    private static Object clockAction() throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", "REGION.aaa1cfd7.in.f30dbb22");
        encoded.addProperty("actionDigest", "DIGEST.2");
        encoded.addProperty("cell", "<org.apache.hadoop.util.Timer: long "
                + "now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        encoded.addProperty("rootKind", "CALL_RETURN");
        encoded.addProperty("declaredCallee",
                "<org.apache.hadoop.util.Timer: long now()>");
        encoded.addProperty("siteId",
                "<a.B: void updateKeys()>#u12");
        encoded.addProperty("eventSeq", 4211L);
        encoded.addProperty("observed", true);
        encoded.addProperty("primitiveValue", "1789358343989");
        return action(encoded);
    }

    /** One frozen SYMBOLIC action, as the plan carries it. */
    private static Object symbolizeAction() throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("symbol", "PORT.now");
        encoded.addProperty("actionDigest", "DIGEST.1");
        encoded.addProperty("cell", "<org.apache.hadoop.util.Timer: long "
                + "now()>.return");
        encoded.addProperty("mode", "SYMBOLIC");
        encoded.addProperty("javaType", "J");
        return action(encoded);
    }

    private static Object action(JsonObject encoded) throws Exception {
        Class<?> type = Class.forName(
                "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                        + "$SymbolizeAction");
        java.lang.reflect.Constructor<?> constructor =
                type.getDeclaredConstructor(JsonObject.class);
        constructor.setAccessible(true);
        return constructor.newInstance(encoded);
    }

    /** One live region, as BranchDecisionRecordingTest opens one. */
    private static ConcolicRegionRuntime.ActiveRegion region()
            throws Exception {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.SEED.manual");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "REGION_PATH_CLOSURE");
        encoded.addProperty("regionId", "REGION.aaa1cfd7");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "hdfs-17899/nn0#epoch0");
        encoded.addProperty("occurrenceId",
                "hdfs-17899/nn0#epoch0/region/REGION.aaa1cfd7#1");
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
        anchor.addProperty("sourceKey", "hdfs-17899/nn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        encoded.add("branches", new JsonArray());
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        ConcolicTaskPlan.RuntimeTask task =
                new ConcolicTaskPlan.RuntimeTask(
                        ExecutionTask.decode(encoded));

        java.lang.reflect.Constructor<?> constructor =
                ConcolicRegionRuntime.ActiveRegion.class
                        .getDeclaredConstructors()[0];
        constructor.setAccessible(true);
        Object[] arguments =
                new Object[constructor.getParameterTypes().length];
        Class<?>[] types = constructor.getParameterTypes();
        for (int index = 0; index < types.length; index++) {
            if (types[index] == ConcolicTaskPlan.RuntimeTask.class) {
                arguments[index] = task;
            } else if (types[index] == long.class) {
                arguments[index] = 900001L;
            } else if (types[index] == int.class) {
                arguments[index] = 1;
            } else if (types[index] == boolean.class) {
                arguments[index] = false;
            } else {
                arguments[index] = null;
            }
        }
        return (ConcolicRegionRuntime.ActiveRegion)
                constructor.newInstance(arguments);
    }
}
