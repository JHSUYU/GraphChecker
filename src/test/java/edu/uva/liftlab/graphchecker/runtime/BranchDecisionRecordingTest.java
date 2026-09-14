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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import edu.uva.liftlab.graphchecker.contract.GapLedger;

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
        JsonArray inputActions = new JsonArray();
        JsonObject fieldAccess = new JsonObject();
        fieldAccess.addProperty("symbol", "sym.f");
        fieldAccess.addProperty("mode", "SYMBOLIC");
        fieldAccess.addProperty("bindingMode", "FIELD_ACCESS");
        fieldAccess.addProperty("accessFieldSignature", "<a.B: int f>");
        JsonArray accessSites = new JsonArray();
        accessSites.add(DECLARED);
        fieldAccess.add("accessSites", accessSites);
        inputActions.add(fieldAccess);
        encoded.add("inputActions", inputActions);
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
        text.append("rows=").append(CanonicalJson.render(rows)).append('\n');
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
    public void branchDecisionRecordingRules() throws Exception {
        concreteDecisionAtADeclaredSiteRecordsOneRowAndTheReach();
        replayObservationTracesItsOwnDecisionVocabulary();
        anUndeclaredSiteThatIsNoBoundaryIsTransparent();
        decisionsOfTwoActivationsOrderByTheVmEventId();
        theTargetAnchorCarriesTheSameClock();
        aDecisionWithoutAVmEventStatesNoId();
        theClockIsPublishedWhateverItsScale();
        writeLogVersionsCarryTheVersionClock();
        ConcreteTargetDecisionIsAReachTest t0 =
                new ConcreteTargetDecisionIsAReachTest();
        t0.concreteTargetDecisionIsAReachRules();
    }

    private void concreteDecisionAtADeclaredSiteRecordsOneRowAndTheReach()
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
                + "unresolved=[]\n"
                + "targetReach={\"kind\":\"TARGET_REACH_EVENT\","
                + "\"occurrence\":1,\"outcome\":true,\"siteId\":\""
                + DECLARED + "\"}\n"
                + "returned=observation\n"
                + "diag=TARGET_REACHED|token=900002 site=" + DECLARED
                + "#1\n", transcript(multiway, observation));
    }

    private void replayObservationTracesItsOwnDecisionVocabulary()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(false, false);
        Object matched = call(binary, "observeReplayDecision",
                new Class<?>[] {String.class, int.class, decisionType(),
                        String.class}, DECLARED, 2, binary(true), "DIGEST");
        assertEquals("rows=[]\n"
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
                + "unresolved=[]\n"
                + "targetReach=none\n"
                // The successor is the replay authority itself, so a
                // multiway decision always matches what it observes.
                + "returned=true\n"
                + "diag=REPLAY_OBSERVE|" + DECLARED + " occ=2 successor=1"
                + " complete=true failed=false\n",
                transcript(multiway, observed));
    }

    /**
     * A site the plan did not name records nothing at all.
     *
     * <p>This is also why there is no pre-gate witness list any more: {@code
     * observeDecision} returns here, before {@code recordConcreteDecision}
     * can be reached, so the arm that filed those witnesses was unreachable
     * and the seed-mismatch excuse the importer read them for was
     * permanently empty.</p>
     */
    private void anUndeclaredSiteThatIsNoBoundaryIsTransparent()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion binary = region(true, false);
        boolean outcome = ConcolicRegionRuntime.resolveBranch(0L, 0L, METHOD,
                99, "x > 0", true);
        assertEquals("rows=[]\nunresolved=[]\n"
                + "targetReach=none\nreturned=true\n",
                transcript(binary, outcome));

        ConcolicRegionRuntime.ActiveRegion multiway = region(true, false);
        int successor = ConcolicRegionRuntime.resolveSwitchBranch(0L, 0L,
                METHOD, 99, "x", "TABLE_SWITCH", "0,1", 0);
        assertEquals("rows=[]\nunresolved=[]\n"
                + "targetReach=none\nreturned=0\n",
                transcript(multiway, successor));
    }


    // ---------- the published monotone clock ----------

    /** One published decision row, as the runtime writes it. */
    private static JsonObject row(int unitIndex, int occurrence,
                                  long vmEventId) throws Exception {
        Method mapping = ConcolicRegionRuntime.class.getDeclaredMethod(
                "branchMapping", String.class, int.class, int.class,
                long.class);
        mapping.setAccessible(true);
        return (JsonObject) mapping.invoke(null, METHOD, unitIndex,
                occurrence, vmEventId);
    }

    private static long eventId(JsonObject row) {
        return row.has("vmEventId")
                ? row.get("vmEventId").getAsLong() : -1L;
    }

    /**
     * Two activations' decisions order by the VM event id.
     *
     * <p>A composer building pi_p has to say which decisions were taken
     * before the anchor and in what order two activations' decisions
     * interleave.  Nothing else published answers that: {@code unitIndex} is
     * a position inside a method and {@code occurrence} counts within one
     * activation, so both repeat across activations -- the two decisions at
     * {@code u4#1} below are different events with identical local indices.
     * The VM's event sequence number is assigned once per event in the
     * process, so it orders them.</p>
     */
    private void decisionsOfTwoActivationsOrderByTheVmEventId()
            throws Exception {
        ConcolicRegionRuntime.ActiveRegion first = region(true, true);
        ConcolicRegionRuntime.ActiveRegion second = region(true, true);

        // The two activations interleave: first, second, first again.
        first.branchMappings.add(row(4, 1, 41L));
        second.branchMappings.add(row(4, 1, 42L));
        first.branchMappings.add(row(12, 1, 43L));

        assertEquals("the local indices repeat across activations",
                first.branchMappings.get(0).get("siteId"),
                second.branchMappings.get(0).get("siteId"));
        assertEquals(41L, eventId(first.branchMappings.get(0)));
        assertEquals(42L, eventId(second.branchMappings.get(0)));
        assertEquals(43L, eventId(first.branchMappings.get(1)));
        assertTrue("one activation's decisions are ordered among themselves",
                eventId(first.branchMappings.get(0))
                        < eventId(first.branchMappings.get(1)));
        assertTrue("and against the other activation's",
                eventId(second.branchMappings.get(0))
                        < eventId(first.branchMappings.get(1)));
    }

    /** The anchor is read on the same clock, so pi_p can exclude what follows. */
    private void theTargetAnchorCarriesTheSameClock() throws Exception {
        ConcolicRegionRuntime.ActiveRegion active = region(true, true);
        active.branchMappings.add(row(4, 1, 41L));
        active.branchMappings.add(row(12, 1, 43L));

        call(active, "recordTargetReach", new Class<?>[] {String.class,
                        int.class, boolean.class, long.class},
                DECLARED, 1, true, 42L);

        JsonObject reach = (JsonObject) rawField(active, "targetReach");
        assertEquals(42L, reach.get("vmEventId").getAsLong());
        assertTrue("the first decision precedes the anchor",
                eventId(active.branchMappings.get(0))
                        < reach.get("vmEventId").getAsLong());
        assertTrue("the second follows it",
                eventId(active.branchMappings.get(1))
                        > reach.get("vmEventId").getAsLong());
    }

    /** A decision the VM assigned no event states no id rather than zero. */
    private void aDecisionWithoutAVmEventStatesNoId() throws Exception {
        assertFalse(row(4, 1, 0L).has("vmEventId"));
    }

    /**
     * The publication does not read the clock's scale.
     *
     * <p>The branch id was a per-ThreadContext counter -- small, dense, one
     * per context -- and the VM now draws it from the session-global event
     * counter shared with fieldVersionId and readEventId, so the values stop
     * starting at 1 and start interleaving with the write log's.  A published
     * row states whatever the VM handed over, on either scale.</p>
     */
    private void theClockIsPublishedWhateverItsScale() throws Exception {
        assertEquals(3L, eventId(row(4, 1, 3L)));
        assertEquals(2305843009213693976L,
                eventId(row(4, 1, 2305843009213693976L)));
        assertTrue("ordering is by value, not by magnitude",
                eventId(row(4, 1, 3L)) < eventId(row(4, 1, 461L)));
    }


    /**
     * The write log keeps the version clock, and nothing beside it.
     *
     * <p>{@code fieldVersionId} is drawn from the VM's session-global event
     * counter at the moment of publish, which is the counter the branch
     * decisions' {@code vmEventId} is on, so "the latest write whose event
     * precedes this access" is a comparison between the two -- within one
     * {@code sessionId}, which the envelope states because the counter
     * restarts at session teardown.  The reduction therefore keeps the
     * version id, its kind, its expression and the session, and drops every
     * other per-version member the VM states.</p>
     */
    private void writeLogVersionsCarryTheVersionClock() throws Exception {
        JsonObject published = SharedStateCapture.reduceWriteLogForTest(
                writeLog(new int[] {39, 41, 44}));

        assertEquals("the session the clock belongs to is stated", 1,
                published.getAsJsonObject("envelope")
                        .get("sessionId").getAsInt());
        JsonArray versions = published.getAsJsonObject("envelope")
                .getAsJsonArray("versions");
        assertEquals(3, versions.size());
        long previous = -1L;
        for (int index = 0; index < versions.size(); index++) {
            JsonObject version = versions.get(index).getAsJsonObject();
            assertEquals("version id, kind and expression, and no more", 3,
                    version.size());
            long clock = version.get("fieldVersionId").getAsLong();
            assertTrue("the clock increases with the writes",
                    clock > previous);
            previous = clock;
        }
    }

    private static JsonObject writeLog(int[] fieldVersionIds) {
        JsonArray versions = new JsonArray();
        for (int index = 0; index < fieldVersionIds.length; index++) {
            JsonObject version = new JsonObject();
            version.addProperty("fieldVersionId", fieldVersionIds[index]);
            version.addProperty("versionKind",
                    index == 0 ? "INITIAL" : "WRITE");
            version.addProperty("regionEnterEventId", 2);
            version.addProperty("writerSourceKey", "dn0#epoch0");
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("value", index);
            version.add("expression", expression);
            versions.add(version);
        }
        JsonObject envelope = new JsonObject();
        envelope.addProperty("kind", "SHARED_FIELD_VERSIONS");
        envelope.addProperty("schemaVersion", 1);
        envelope.addProperty("sessionId", 1);
        envelope.add("versions", versions);
        JsonObject record = new JsonObject();
        record.addProperty("kind", "VM_SHARED_FIELD_VERSIONS_V1");
        record.addProperty("authority", "VM_SHARED_STATE_EVIDENCE_V1");
        record.addProperty("locationKey", "INSTANCE_FIELD/9#56");
        record.add("envelope", envelope);
        return record;
    }

    /** The transcript from {@code returned=} on: its rows are asserted by the
     *  concrete-decision tests, and repeating them here adds no evidence. */
    private static String tail(String transcript) {
        return transcript.substring(transcript.indexOf("returned="));
    }

    /**
     * An activation that decides the target site has reached the target.
     *
     * <p>Whether the predicate there was symbolic is evidence about the anchor,
     * not a condition on publishing it: the reach carries the expression when
     * the branch has one and the concrete outcome when it has not, and the
     * composer reads which of the two it is from the branch row beside it.</p>
     *
     * <p>hdfs-17960's target branch is {@code i != sm.getNumSnapshots()} over
     * two concrete ints; the root reaches it by control dependence, because the
     * flip skips a decrement. Gated on a solver witness, that activation
     * recorded the decision AND was named by {@code nameUnreachedTargetBranch}
     * as never having decided it -- two statements about one activation that
     * cannot both be true, and the reason MARKER_FLIPPED had no reach to read on
     * lanes BJ, BK and BL.</p>
     */
    static final class ConcreteTargetDecisionIsAReachTest {
        private static final String TARGET =
                "<org.apache.hadoop.hdfs.server.namenode.snapshot."
                        + "SnapshotManager: void deleteSnapshot()>#u61";
        private static final String ELSEWHERE =
                "<org.apache.hadoop.hdfs.server.namenode.snapshot."
                        + "SnapshotManager: void deleteSnapshot()>#u44";

        /** A concrete decision at the addressed occurrence states the reach. */
        public void concreteTargetDecisionIsAReachRules() throws Exception {
            aConcreteDecisionAtTheTargetStatesTheReach();
            aSymbolicDecisionAtTheTargetStatesTheSameReach();
            anotherOccurrenceOfTheTargetSiteIsNotTheAddressedOne();
            aPermutedLoopOccurrenceStillStatesTheReach();
            anotherSiteIsNotTheTarget();
            aDecisionWithNoRecordedRowStatesNoReach();
            everySkipKindIsClassedUnderItsPublishedCode();
            theFlipWaveCodesAreRegisteredAndFailClosed();
        }

        private void aConcreteDecisionAtTheTargetStatesTheReach() {
            assertTrue("the site executed and the outcome is this run's own",
                    ConcolicRegionRuntime.statesTargetReach(true, false,
                            TARGET, 1, TARGET, 1));
        }

        /** A symbolic one states it in exactly the same way. */
        private void aSymbolicDecisionAtTheTargetStatesTheSameReach() {
            assertTrue(ConcolicRegionRuntime.statesTargetReach(true, false,
                    TARGET, 1, TARGET, 1));
        }

        /** Another activation of the site is another occurrence. */
        private void anotherOccurrenceOfTheTargetSiteIsNotTheAddressedOne() {
            assertFalse(ConcolicRegionRuntime.statesTargetReach(true, false,
                    TARGET, 1, TARGET, 2));
        }

        /** A bounded loop may run the planned occurrence at another k. */
        private void aPermutedLoopOccurrenceStillStatesTheReach() {
            assertTrue(ConcolicRegionRuntime.statesTargetReach(true, true,
                    TARGET, 1, TARGET, 3));
        }

        /** Another site is not the target, however it decided. */
        private void anotherSiteIsNotTheTarget() {
            assertFalse(ConcolicRegionRuntime.statesTargetReach(true, false,
                    TARGET, 1, ELSEWHERE, 1));
            assertFalse("and a task naming no target reaches none",
                    ConcolicRegionRuntime.statesTargetReach(true, false,
                            "", 1, ELSEWHERE, 1));
        }

        /**
         * A decision the VM emitted no event for states nothing.
         *
         * <p>There is no branch row beside which the reach could be read, so
         * this is the one case that is still silent -- and it is the case
         * {@code TARGET_BRANCH_NOT_REACHED} is for.</p>
         */
        private void aDecisionWithNoRecordedRowStatesNoReach() {
            assertFalse(ConcolicRegionRuntime.statesTargetReach(false, false,
                    TARGET, 1, TARGET, 1));
        }

        /**
         * Every skip kind the runtime publishes is classed under the code the
         * importer actually spells.
         *
         * <p>A region skip reaches the ledger as {@code "REGION_" + skipKind}
         * ({@code ConcolicSummaryImporter.skippedEventCode}). Two entries were
         * written under the bare skip kind and matched no row at all, so
         * {@code REGION_ROOT_NEVER_EXECUTED} took the blocking default on lanes
         * VM9 and VM10 with the slice-conditional scope written for it deciding
         * nothing.</p>
         */
        private void everySkipKindIsClassedUnderItsPublishedCode()
                throws Exception {
            for (java.lang.reflect.Field field
                    : ConcolicRegionRuntime.class.getDeclaredFields()) {
                if (!field.getName().startsWith("SKIP_")) continue;
                field.setAccessible(true);
                String code = "REGION_" + field.get(null);
                assertTrue(code + " is not registered in the gap ledger",
                        GapLedger.blockingCodes().contains(code)
                                || GapLedger.diagnosticCodes().contains(code));
            }
        }

        /**
         * The flip wave is classed apart, and only where the campaign can name
         * the row as one.
         */
        private void theFlipWaveCodesAreRegisteredAndFailClosed() {
            for (String code : new String[]{"REGION_ROOT_NEVER_EXECUTED",
                    "REGION_REPLAY_PREFIX_UNMATCHED",
                    "PUBLICATION_TASK_ANSWERED_BY_NO_RUN"}) {
                assertTrue(code, GapLedger.flipWaveDiagnostic(code));
                assertFalse(code + " states no reason",
                        GapLedger.flipWaveReason(code).isEmpty());
                assertTrue(code + " must still block a reader that cannot see"
                                + " the wave", GapLedger.blocking(code));
            }
            assertFalse("a seed-wave code carries no flip-wave qualifier",
                    GapLedger.flipWaveDiagnostic("PUBLICATION_TASK_SILENT"));
        }
    }

}
