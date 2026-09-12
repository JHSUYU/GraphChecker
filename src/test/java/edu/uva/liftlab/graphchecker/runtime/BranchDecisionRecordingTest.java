package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import static org.junit.Assert.assertEquals;

/**
 * Characterization of the branch-observation machinery a region runs for one
 * decision: every row, witness, unresolved note, target reach and diagnostic
 * line it writes down, for a binary branch and for the multiway switch that
 * answers the same five questions.  The two kinds share one implementation, so
 * these transcripts are what "the same, parameterised by the decision" means.
 */
public class BranchDecisionRecordingTest {
    private static final String METHOD = "<a.B: void run(int)>";
    private static final String DECLARED = METHOD + "#u4";
    private static final String BOUNDARY = METHOD + "#u12";

    private final Deque<Long> opened = new ArrayDeque<>();
    private final ByteArrayOutputStream diagnostics =
            new ByteArrayOutputStream();
    private PrintStream systemError;

    @Before
    public void captureDiagnostics() throws Exception {
        System.setProperty(ConcolicRegionRuntime.DIAGNOSTICS_PROPERTY,
                "true");
        Field cached = ConcolicRegionRuntime.class
                .getDeclaredField("diagnostics");
        cached.setAccessible(true);
        cached.set(null, null);
        systemError = System.err;
        System.setErr(new PrintStream(diagnostics, true, "UTF-8"));
    }

    @After
    public void releaseRegions() throws Exception {
        System.setErr(systemError);
        System.clearProperty(ConcolicRegionRuntime.DIAGNOSTICS_PROPERTY);
        Field cached = ConcolicRegionRuntime.class
                .getDeclaredField("diagnostics");
        cached.setAccessible(true);
        cached.set(null, null);
        while (!opened.isEmpty()) {
            ConcolicRegionRuntime.ACTIVE.remove(opened.pop());
        }
        currentTokens().clear();
    }

    // ---------- activation harness ----------

    @SuppressWarnings("unchecked")
    private static Deque<Long> currentTokens() throws Exception {
        Field field = ConcolicRegionRuntime.class
                .getDeclaredField("CURRENT_TOKENS");
        field.setAccessible(true);
        return ((ThreadLocal<Deque<Long>>) field.get(null)).get();
    }

    private static JsonObject declaredBranch() {
        JsonObject branch = new JsonObject();
        branch.addProperty("siteId", DECLARED);
        branch.addProperty("policy", "EXPLORE");
        branch.addProperty("selectedOccurrence", 1);
        branch.addProperty("requiredOutcome", true);
        return branch;
    }

    private static ExecutionTask task(boolean addressesTarget) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("taskId", "TASK.1");
        encoded.addProperty("goalId", "GOAL.1");
        encoded.addProperty("goalKind", "TARGET_REACH_CLOSURE");
        encoded.addProperty("regionId", "REGION.1");
        encoded.addProperty("relationKey", "REL.1");
        encoded.addProperty("sourceKey", "dn0#epoch0");
        encoded.addProperty("occurrenceId", "REGION.1@dn0#epoch0#1");
        encoded.addProperty("rootMethod", METHOD);
        encoded.addProperty("instrumentationSelector", "sel");
        JsonObject admission = new JsonObject();
        admission.addProperty("state", "EXECUTABLE");
        encoded.add("admission", admission);
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "GLOBAL_INVOCATION");
        selector.addProperty("invocationOrdinal", 1);
        JsonObject anchor = new JsonObject();
        anchor.addProperty("sourceKey", "dn0#epoch0");
        anchor.addProperty("kind", "REGISTERED_SOURCE");
        selector.add("causalAnchor", anchor);
        encoded.add("rootSelector", selector);
        JsonArray branches = new JsonArray();
        branches.add(declaredBranch());
        encoded.add("branches", branches);
        encoded.add("inputActions", new JsonArray());
        JsonObject loopBound = new JsonObject();
        loopBound.addProperty("schemaVersion", 1);
        encoded.add("loopBound", loopBound);
        JsonObject exit = new JsonObject();
        exit.addProperty("siteId", BOUNDARY);
        JsonArray exits = new JsonArray();
        exits.add(exit);
        JsonObject loop = new JsonObject();
        loop.add("loopExitDecisions", exits);
        JsonArray retained = new JsonArray();
        retained.add(loop);
        encoded.add("retainedLoops", retained);
        if (addressesTarget) {
            JsonObject target = new JsonObject();
            target.addProperty("siteId", DECLARED);
            target.addProperty("occurrence", 1);
            encoded.add("targetBranch", target);
        }
        return ExecutionTask.decode(encoded);
    }

    private ConcolicRegionRuntime.ActiveRegion region(boolean addressesTarget,
                                                      boolean recording)
            throws Exception {
        ConcolicTaskPlan.RuntimeTask runtime =
                new ConcolicTaskPlan.RuntimeTask(task(addressesTarget));
        long token = 900000L + opened.size() + 1;
        ConcolicRegionRuntime.ActiveRegion active =
                new ConcolicRegionRuntime.ActiveRegion(token, runtime, null,
                        Thread.currentThread(), false);
        active.pathRecordingStarted = recording;
        ConcolicRegionRuntime.ACTIVE.put(token, active);
        currentTokens().push(token);
        opened.push(token);
        return active;
    }

    // ---------- reflection into the observation machinery ----------

    private static Class<?> switchType() throws Exception {
        return Class.forName("edu.uva.liftlab.graphchecker.runtime"
                + ".ConcolicRegionRuntime$SwitchExpectation");
    }

    private static Class<?> decisionType() throws Exception {
        return Class.forName("edu.uva.liftlab.graphchecker.runtime"
                + ".ConcolicRegionRuntime$BranchDecision");
    }

    private static Object binary(boolean outcome) throws Exception {
        Method factory = decisionType().getDeclaredMethod("binary",
                boolean.class);
        factory.setAccessible(true);
        return factory.invoke(null, outcome);
    }

    private static Object multiway(String kind, String keys, int successor)
            throws Exception {
        Method parse = switchType().getDeclaredMethod("parse", String.class,
                String.class, int.class);
        parse.setAccessible(true);
        Method factory = decisionType().getDeclaredMethod("multiway",
                switchType());
        factory.setAccessible(true);
        return factory.invoke(null, parse.invoke(null, kind, keys,
                successor));
    }

    private static Object call(Object target, String name, Class<?>[] types,
                               Object... arguments) throws Exception {
        Method method = target.getClass().getDeclaredMethod(name, types);
        method.setAccessible(true);
        return method.invoke(target, arguments);
    }

    // ---------- transcript ----------

    private String transcript(ConcolicRegionRuntime.ActiveRegion active,
                              Object returned) throws Exception {
        StringBuilder text = new StringBuilder();
        JsonArray rows = new JsonArray();
        for (JsonObject row : active.branchMappings) rows.add(row);
        JsonArray witnesses = new JsonArray();
        for (JsonObject row : active.concreteBranchWitnesses) {
            witnesses.add(row);
        }
        text.append("rows=").append(CanonicalJson.render(rows)).append('\n');
        text.append("witnesses=").append(CanonicalJson.render(witnesses))
                .append('\n');
        text.append("unresolved=").append(field(active, "unresolved"))
                .append('\n');
        Object reach = rawField(active, "targetReach");
        text.append("targetReach=").append(reach == null ? "none"
                : CanonicalJson.render((JsonObject) reach)).append('\n');
        text.append("returned=").append(returned == null ? "null"
                : returned instanceof Boolean || returned instanceof Integer
                ? returned.toString() : "observation").append('\n');
        for (String line : diagnostic()) {
            text.append("diag=").append(line).append('\n');
        }
        return text.toString();
    }

    private static Object rawField(Object owner, String name)
            throws Exception {
        Field field = owner.getClass().getDeclaredField(name);
        field.setAccessible(true);
        return field.get(owner);
    }

    @SuppressWarnings("unchecked")
    private static String field(Object owner, String name) throws Exception {
        return ((Collection<String>) rawField(owner, name)).toString();
    }

    /** The diagnostic lines this scenario emitted, without their clocks. */
    private String[] diagnostic() throws Exception {
        String text = new String(diagnostics.toByteArray(), "UTF-8");
        diagnostics.reset();
        if (text.isEmpty()) return new String[0];
        String[] lines = text.split("\n");
        String[] events = new String[lines.length];
        for (int index = 0; index < lines.length; index++) {
            // CAUSYNTH-DIAG|clock|thread|heap|EVENT|detail
            String[] parts = lines[index].split("\\|", 6);
            events[index] = parts.length < 6 ? lines[index]
                    : parts[4] + "|" + parts[5];
        }
        return events;
    }

    // ---------- the two kinds, stage by stage ----------

    @Test
    public void concreteDecisionAtADeclaredSiteRecordsOneRowAndTheReach()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(true, false);
        Object observation = call(binary, "recordConcreteDecision",
                new Class<?>[] {String.class, int.class, decisionType()},
                METHOD, 4, binary(true));
        assertEquals("rows=[{\"concreteObservation\":{\"kind\":"
                + "\"EXACT_CONCRETE_BINARY_BRANCH_OBSERVATION\","
                + "\"schemaVersion\":1,\"site\":{\"method\":\"" + METHOD
                + "\",\"occurrence\":1,\"siteId\":\"" + DECLARED
                + "\",\"unitIndex\":4},\"sourceTakenOutcome\":true},"
                + "\"method\":\"" + METHOD + "\",\"occurrence\":1,"
                + "\"rawPathConditionBaseline\":0,"
                + "\"rawPathConditionSize\":0,\"siteId\":\"" + DECLARED
                + "\",\"unitIndex\":4}]\n"
                + "witnesses=[]\n"
                + "unresolved=[]\n"
                + "targetReach={\"kind\":\"TARGET_REACH_EVENT\","
                + "\"occurrence\":1,\"outcome\":true,\"siteId\":\""
                + DECLARED + "\"}\n"
                + "returned=observation\n"
                + "diag=TARGET_REACHED|token=900001 site=" + DECLARED
                + "#1\n", transcript(binary, observation));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        observation = call(multiway, "recordConcreteDecision",
                new Class<?>[] {String.class, int.class, decisionType()},
                METHOD, 4, multiway("TABLE_SWITCH", "0,1,2", 1));
        assertEquals("rows=[{\"concreteObservation\":{\"branchKind\":"
                + "\"TABLE_SWITCH\",\"caseKeys\":[0,1,2],\"kind\":"
                + "\"EXACT_CONCRETE_SWITCH_BRANCH_OBSERVATION\","
                + "\"observedSuccessorIndex\":1,\"schemaVersion\":1,"
                + "\"site\":{\"method\":\"" + METHOD + "\",\"occurrence\":1,"
                + "\"siteId\":\"" + DECLARED + "\",\"unitIndex\":4},"
                + "\"sourceTakenOutcome\":true},\"method\":\"" + METHOD
                + "\",\"occurrence\":1,\"rawPathConditionBaseline\":0,"
                + "\"rawPathConditionSize\":0,\"siteId\":\"" + DECLARED
                + "\",\"unitIndex\":4}]\n"
                + "witnesses=[]\n"
                + "unresolved=[]\n"
                + "targetReach={\"kind\":\"TARGET_REACH_EVENT\","
                + "\"occurrence\":1,\"outcome\":true,\"siteId\":\""
                + DECLARED + "\"}\n"
                + "returned=observation\n"
                + "diag=TARGET_REACHED|token=900002 site=" + DECLARED
                + "#1\n", transcript(multiway, observation));
    }

    @Test
    public void concreteDecisionAtAnUndeclaredSiteRecordsOnlyItsWitness()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(true, false);
        Object observation = call(binary, "recordConcreteDecision",
                new Class<?>[] {String.class, int.class, decisionType()},
                METHOD, 9, binary(false));
        assertEquals("rows=[]\n"
                + "witnesses=[{\"kind\":"
                + "\"CONCRETE_BRANCH_EXECUTION_WITNESS_V1\",\"method\":\""
                + METHOD + "\",\"schemaVersion\":1,\"siteId\":\"" + METHOD
                + "#u9\",\"sourceTakenOutcome\":false,\"unitIndex\":9}]\n"
                + "unresolved=[]\n"
                + "targetReach=none\n"
                + "returned=null\n", transcript(binary, observation));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        observation = call(multiway, "recordConcreteDecision",
                new Class<?>[] {String.class, int.class, decisionType()},
                METHOD, 9, multiway("LOOKUP_SWITCH", "7,9", 2));
        assertEquals("rows=[]\n"
                + "witnesses=[{\"branchKind\":\"LOOKUP_SWITCH\","
                + "\"caseKeys\":[7,9],\"kind\":"
                + "\"CONCRETE_BRANCH_EXECUTION_WITNESS_V1\",\"method\":\""
                + METHOD + "\",\"observedSuccessorIndex\":2,"
                + "\"schemaVersion\":1,\"siteId\":\"" + METHOD
                + "#u9\",\"sourceTakenOutcome\":false,\"unitIndex\":9}]\n"
                + "unresolved=[]\n"
                + "targetReach=none\n"
                + "returned=null\n", transcript(multiway, observation));
    }

    @Test
    public void replayBoundaryRecordsTheDecisionWithoutAPathCondition()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(false, false);
        Object observation = call(binary, "recordReplayBoundary",
                new Class<?>[] {String.class, int.class, int.class,
                        decisionType()}, METHOD, 12, 3, binary(true));
        assertEquals("rows=[{\"concreteObservation\":{\"kind\":"
                + "\"EXACT_CONCRETE_BINARY_BRANCH_OBSERVATION\","
                + "\"schemaVersion\":1,\"site\":{\"method\":\"" + METHOD
                + "\",\"occurrence\":3,\"siteId\":\"" + BOUNDARY
                + "\",\"unitIndex\":12},\"sourceTakenOutcome\":true},"
                + "\"method\":\"" + METHOD + "\",\"occurrence\":3,"
                + "\"rawPathConditionBaseline\":0,"
                + "\"rawPathConditionSize\":0,\"siteId\":\"" + BOUNDARY
                + "\",\"unitIndex\":12}]\n"
                + "witnesses=[]\n"
                + "unresolved=[]\n"
                + "targetReach=none\n"
                + "returned=observation\n", transcript(binary, observation));

        ConcolicRegionRuntime.ActiveRegion multiway = region(false, false);
        observation = call(multiway, "recordReplayBoundary",
                new Class<?>[] {String.class, int.class, int.class,
                        decisionType()}, METHOD, 12, 3,
                multiway("TABLE_SWITCH", "0,1,2", 3));
        assertEquals("rows=[{\"concreteObservation\":{\"branchKind\":"
                + "\"TABLE_SWITCH\",\"caseKeys\":[0,1,2],\"kind\":"
                + "\"EXACT_CONCRETE_SWITCH_BRANCH_OBSERVATION\","
                + "\"observedSuccessorIndex\":3,\"schemaVersion\":1,"
                + "\"site\":{\"method\":\"" + METHOD + "\",\"occurrence\":3,"
                + "\"siteId\":\"" + BOUNDARY + "\",\"unitIndex\":12},"
                + "\"sourceTakenOutcome\":false},\"method\":\"" + METHOD
                + "\",\"occurrence\":3,\"rawPathConditionBaseline\":0,"
                + "\"rawPathConditionSize\":0,\"siteId\":\"" + BOUNDARY
                + "\",\"unitIndex\":12}]\n"
                + "witnesses=[]\n"
                + "unresolved=[]\n"
                + "targetReach=none\n"
                + "returned=observation\n",
                transcript(multiway, observation));
    }

    @Test
    public void replayObservationTracesItsOwnDecisionVocabulary()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(false, false);
        Object matched = call(binary, "observeReplayDecision",
                new Class<?>[] {String.class, int.class, decisionType(),
                        String.class}, DECLARED, 2, binary(true), "DIGEST");
        assertEquals("rows=[]\n"
                + "witnesses=[]\n"
                + "unresolved=[]\n"
                + "targetReach=none\n"
                + "returned=true\n"
                + "diag=REPLAY_OBSERVE|" + DECLARED + " occ=2 outcome=true"
                + " matched=true complete=true failed=false\n",
                transcript(binary, matched));

        ConcolicRegionRuntime.ActiveRegion multiway = region(false, false);
        Object observed = call(multiway, "observeReplayDecision",
                new Class<?>[] {String.class, int.class, decisionType(),
                        String.class}, DECLARED, 2,
                multiway("TABLE_SWITCH", "0,1,2", 1), "");
        assertEquals("rows=[]\n"
                + "witnesses=[]\n"
                + "unresolved=[]\n"
                + "targetReach=none\n"
                // The successor is the replay authority itself, so a
                // multiway decision always matches what it observes.
                + "returned=true\n"
                + "diag=REPLAY_OBSERVE|" + DECLARED + " occ=2 successor=1"
                + " complete=true failed=false\n",
                transcript(multiway, observed));
    }

    @Test
    public void anUndeclaredSiteThatIsNoBoundaryIsTransparent()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(true, false);
        boolean outcome = ConcolicRegionRuntime.resolveBranch(0L, 0L, METHOD,
                99, "x > 0", true);
        assertEquals("rows=[]\nwitnesses=[]\nunresolved=[]\n"
                + "targetReach=none\nreturned=true\n",
                transcript(binary, outcome));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        int successor = ConcolicRegionRuntime.resolveSwitchBranch(0L, 0L,
                METHOD, 99, "x", "TABLE_SWITCH", "0,1", 0);
        assertEquals("rows=[]\nwitnesses=[]\nunresolved=[]\n"
                + "targetReach=none\nreturned=0\n",
                transcript(multiway, successor));
    }

    @Test
    public void aGateClosedDeclaredSiteRecordsItsDecisionAndObservesReplay()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(true, false);
        boolean outcome = ConcolicRegionRuntime.resolveBranch(0L, 0L, METHOD,
                4, "x > 0", true);
        assertEquals("returned=true\n"
                + "diag=TARGET_REACHED|token=900001 site=" + DECLARED + "#1\n"
                + "diag=REPLAY_OBSERVE|" + DECLARED + " occ=1 outcome=true"
                + " matched=true complete=true failed=false\n",
                tail(transcript(binary, outcome)));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        int successor = ConcolicRegionRuntime.resolveSwitchBranch(0L, 0L,
                METHOD, 4, "x", "TABLE_SWITCH", "0,1,2", 1);
        assertEquals("returned=1\n"
                + "diag=TARGET_REACHED|token=900002 site=" + DECLARED + "#1\n"
                + "diag=REPLAY_OBSERVE|" + DECLARED + " occ=1 successor=1"
                + " complete=true failed=false\n",
                tail(transcript(multiway, successor)));
    }

    @Test
    public void aReplayBoundaryAdvancesItsOwnOccurrenceBeforeRecording()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(true, false);
        boolean outcome = ConcolicRegionRuntime.resolveBranch(0L, 0L, METHOD,
                12, "x > 0", true);
        assertEquals("returned=true\n"
                + "diag=REPLAY_OBSERVE|" + BOUNDARY + " occ=1 outcome=true"
                + " matched=true complete=true failed=false\n",
                tail(transcript(binary, outcome)));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        int successor = ConcolicRegionRuntime.resolveSwitchBranch(0L, 0L,
                METHOD, 12, "x", "LOOKUP_SWITCH", "7,9", 0);
        assertEquals("returned=0\n"
                + "diag=REPLAY_OBSERVE|" + BOUNDARY + " occ=1 successor=0"
                + " complete=true failed=false\n",
                tail(transcript(multiway, successor)));
    }

    @Test
    public void anAbsentPreparedHandleIsNamedByTheDecisionItBelongsTo()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binaryBoundary =
                region(true, true);
        boolean outcome = ConcolicRegionRuntime.resolveBranch(77L, 0L, METHOD,
                12, "x > 0", true);
        assertEquals("rows=[]\nwitnesses=[]\n"
                + "unresolved=[missing or mismatched replay loop boundary 77"
                + " for " + BOUNDARY + "]\n"
                + "targetReach=none\nreturned=true\n",
                transcript(binaryBoundary, outcome));

        ConcolicRegionRuntime.ActiveRegion switchBoundary = region(true, true);
        int successor = ConcolicRegionRuntime.resolveSwitchBranch(77L, 0L,
                METHOD, 12, "x", "TABLE_SWITCH", "0,1", 0);
        assertEquals("rows=[]\nwitnesses=[]\n"
                + "unresolved=[missing or mismatched replay loop switch"
                + " boundary 77 for " + BOUNDARY + "]\n"
                + "targetReach=none\nreturned=0\n",
                transcript(switchBoundary, successor));

        ConcolicRegionRuntime.ActiveRegion binary = region(true, true);
        outcome = ConcolicRegionRuntime.resolveBranch(77L, 0L, METHOD, 4,
                "x > 0", true);
        assertEquals("rows=[]\nwitnesses=[]\n"
                + "unresolved=[missing or mismatched prepared branch 77 for "
                + DECLARED + "]\n"
                + "targetReach=none\nreturned=true\n",
                transcript(binary, outcome));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, true);
        successor = ConcolicRegionRuntime.resolveSwitchBranch(77L, 0L, METHOD,
                4, "x", "TABLE_SWITCH", "0,1", 0);
        assertEquals("rows=[]\nwitnesses=[]\n"
                + "unresolved=[missing or mismatched prepared switch 77 for "
                + DECLARED + "]\n"
                + "targetReach=none\nreturned=0\n",
                transcript(multiway, successor));
    }

    @Test
    public void aMalformedStaticSwitchContractIsRefusedBeforeAnyRecording()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        int successor = ConcolicRegionRuntime.resolveSwitchBranch(0L, 0L,
                METHOD, 4, "x", "BAD_SWITCH", "0,1", 0);
        assertEquals("rows=[]\nwitnesses=[]\n"
                + "unresolved=[" + DECLARED + ": invalid static switch"
                + " contract: java.lang.IllegalArgumentException: unsupported"
                + " branch kind BAD_SWITCH]\n"
                + "targetReach=none\nreturned=0\n",
                transcript(multiway, successor));
    }

    /** The transcript from {@code returned=} on: its rows are asserted by the
     *  concrete-decision tests, and repeating them here adds no evidence. */
    private static String tail(String transcript) {
        return transcript.substring(transcript.indexOf("returned="));
    }
}
