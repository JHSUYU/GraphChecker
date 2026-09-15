package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.plan.ExecutionTask;
import org.junit.After;
import org.junit.Test;

import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.Deque;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

/**
 * The replay invents no chain element.
 *
 * <p>A link the recording does not supply is not a licence to supply one:
 * the engine keeps the value it holds, and may never mint a root, pin a
 * polarity, or accept a site as the target because some site was reached.</p>
 */
public class NoFabricatedChainElementTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String SITE = METHOD + "#u4";
    private static final String MARKER = "hadoopIpcRequestFails";
    private final Deque<Long> opened = new ArrayDeque<>();

    @After
    public void releaseRegions() throws Exception {
        opened.forEach(ConcolicRegionRuntime.ACTIVE::remove);
        opened.clear();
        currentTokens().clear();
    }

    /** A well-formed envelope that simply carries no expression still does. */
    @Test
    public void anAbsentExpressionIsStillTheHonestNothing() throws Exception {
        region(false);
        assertNull(ConcolicRegionRuntime.engineExpression("{}"));
    }

    /**
     * A marker is answered from the recording or a model, or is a named gap.
     *
     * <p>A seed has no model, so "no model assignment" is not "unanswered":
     * the recorded polarity is {@code primitiveValue} gated on {@code
     * observed}, and a flip answers from its model.</p>
     */
    @Test
    public void aControlledMarkerIsAnsweredOrNamedUnanswered()
            throws Exception {
        for (String recorded : new String[] {"false", "true"}) {
            region(false, faultAction(MARKER, recorded));
            assertEquals("the recording's polarity is read, not assumed",
                    recorded, String.valueOf(ConcolicRegionRuntime
                            .materializeSymbolicBoolean(MARKER)));
        }
        // No recorded value is the unanswered case: the idle polarity of a
        // marker this plan controls is not an answer to it.
        region(false, faultAction(MARKER, null));
        assertFalse(ConcolicRegionRuntime.materializeSymbolicBoolean(MARKER));
    }

    /**
     * A throw is not a target reach; the declared occurrence still is.
     *
     * <p>With no target occurrence declared there is no link to check.</p>
     */
    @Test
    public void anyThrowIsNoLongerATargetReach() throws Exception {
        ConcolicRegionRuntime.ActiveRegion undeclared = region(false);
        undeclared.exitKind = "THROW";
        undeclared.exceptionType = "java.lang.IllegalStateException";
        assertFalse("an undeclared target cannot have been reached",
                ConcolicResultPublisher.targetReachedByActivation(undeclared));
        ConcolicRegionRuntime.ActiveRegion declared = region(true);
        declared.exitKind = "THROW";
        declared.exceptionType = "java.lang.IllegalStateException";
        recordReach(declared);
        assertTrue(ConcolicResultPublisher.targetReachedByActivation(declared));
    }

    /** The declared target occurrence, decided at its required outcome. */
    private static void recordReach(ConcolicRegionRuntime.ActiveRegion active)
            throws Exception {
        Field field = ConcolicRegionRuntime.ActiveRegion.class
                .getDeclaredField("targetReach");
        field.setAccessible(true);
        field.set(active, new JsonParser().parse(
                "{'kind':'TARGET_REACH_EVENT','siteId':'" + SITE
                + "','occurrence':1,'outcome':true}"));
    }

    /** One declared fault marker, with the polarity the recording saw. */
    private static JsonObject faultAction(String name, String recorded) {
        JsonObject json = new JsonParser().parse("{'symbol':'REGION.ipc.in."
                + name + ".1','javaType':'boolean','location':'CALL_RETURN',"
                + "'rootKind':'ACTIVATION_LOCAL','symbolicName':'" + name
                + "','replayOccurrence':1,'mode':'SYMBOLIC','sourceKind':'"
                + RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                + "'}").getAsJsonObject();
        if (recorded != null) {
            json.addProperty("observed", true);
            json.addProperty("primitiveValue", recorded);
        }
        return json;
    }
    private static ExecutionTask task(boolean target, JsonObject... acts) {
        JsonObject encoded = new JsonParser().parse(
                "{'taskId':'TASK.1','goalId':'GOAL.1','regionId':'REGION.1',"
                + "'goalKind':'TARGET_REACH_CLOSURE','relationKey':'REL.1',"
                + "'sourceKey':'dn0#epoch0','rootMethod':'" + METHOD + "',"
                + "'occurrenceId':'REGION.1@dn0#epoch0#1','loopBound':"
                + "{'schemaVersion':1,'defaultBackedgeTraversals':8},"
                + "'instrumentationSelector':'sel',"
                + "'admission':{'state':'EXECUTABLE'},'rootSelector':{'kind':"
                + "'GLOBAL_INVOCATION','invocationOrdinal':1,'causalAnchor':"
                + "{'sourceKey':'dn0#epoch0','kind':'REGISTERED_SOURCE'}},"
                + "'branches':[{'siteId':'" + SITE + "',"
                + "'selectedOccurrence':1}]}")
                .getAsJsonObject();
        JsonArray inputActions = new JsonArray();
        for (JsonObject action : acts) inputActions.add(action);
        encoded.add("inputActions", inputActions);
        if (target) {
            encoded.add("targetBranch", new JsonParser().parse(
                    "{'siteId':'" + SITE + "','occurrence':1,"
                            + "'requiredOutcome':true}"));
        }
        return ExecutionTask.decode(encoded);
    }

    private ConcolicRegionRuntime.ActiveRegion region(boolean target,
            JsonObject... actions) throws Exception {
        return open(task(target, actions));
    }

    private ConcolicRegionRuntime.ActiveRegion open(ExecutionTask encoded)
            throws Exception {
        long token = 910000L + opened.size() + 1;
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token,
                        new ConcolicTaskPlan.RuntimeTask(encoded), null,
                        Thread.currentThread());
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
        return active;
    }

    @SuppressWarnings("unchecked")
    private static Deque<Long> currentTokens() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }
}
