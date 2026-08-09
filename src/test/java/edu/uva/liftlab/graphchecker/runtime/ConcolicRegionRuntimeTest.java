package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.ClosureGoalKind;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureCodec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ConcolicSummaryImporter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

public class ConcolicRegionRuntimeTest {
    private static final String RESULT_FIELD =
            "<test.State: int result>";
    private static final String OTHER_FIELD =
            "<test.State: int other>";

    @Rule
    public final TemporaryFolder folder = new TemporaryFolder();

    @Test
    public void compatibleRootSelectionDoesNotDependOnInvocationOrder() {
        String method = "<test.Worker: void run()>";
        JsonObject selector = new JsonObject();
        selector.addProperty("kind", "RECEIVER_CONTEXT");
        selector.addProperty("method", method);
        selector.addProperty("receiverClass", Object.class.getName());

        Object discoveredFirst = new Object();
        Object discoveredSecond = new Object();
        // Replay may encounter the same compatible receiver family in the
        // opposite order.  Neither object identity nor activation ordinal is
        // a replay address.
        assertTrue(ConcolicRegionRuntime.compatibleRootForTests(
                selector, method, method, discoveredSecond,
                new Object[0], "worker-2"));
        assertTrue(ConcolicRegionRuntime.compatibleRootForTests(
                selector, method, method, discoveredFirst,
                new Object[0], "worker-1"));
        assertFalse(ConcolicRegionRuntime.compatibleRootForTests(
                selector, method, "<test.Other: void run()>",
                discoveredFirst, new Object[0], "worker-1"));
    }

    @Test
    public void replayMatchesStableBranchPrefixInsideAnyCompatibleRoot() {
        BranchReplayContract contract = BranchReplayContract.flip(
                Collections.singletonList(replayWitness(
                        "ROOT#u1", 1, true)),
                replayWitness("ROOT#u7", 1, true));
        ConcolicRegionRuntime.ReplayProgress progress =
                new ConcolicRegionRuntime.ReplayProgress(contract);

        assertFalse(progress.observe("UNRELATED#u2", 1, false));
        assertFalse(progress.observe("ROOT#u1", 1, true));
        // The solver requests the opposite source outcome.
        assertTrue(progress.observe("ROOT#u7", 1, false));
        assertTrue(progress.complete());

        ConcolicRegionRuntime.ReplayProgress wrongOrder =
                new ConcolicRegionRuntime.ReplayProgress(contract);
        assertFalse(wrongOrder.observe("ROOT#u7", 1, false));
        assertTrue(wrongOrder.failed());
    }

    @Test
    public void seedReplaySkipsOnlyTheActivationThatContradictsARecording() {
        Map<String, Set<Boolean>> recorded = new LinkedHashMap<>();
        recorded.put("ROOT#u5", outcomes(false));
        recorded.put("ROOT#u9", outcomes(true));

        // The winning activation drove a recorded site the other way, so it
        // can never attest this seed and must let a later one compete.
        Map<String, Set<Boolean>> contradicting = new LinkedHashMap<>();
        contradicting.put("ROOT#u5", outcomes(true));
        assertTrue(ConcolicRegionRuntime.seedOutcomeConflict(
                recorded, contradicting).startsWith("ROOT#u5:"));

        // A wider environment revisits a site both ways.  The recorded
        // outcome is still witnessed, so this is the same decision.
        Map<String, Set<Boolean>> wider = new LinkedHashMap<>();
        wider.put("ROOT#u5", outcomes(true, false));
        wider.put("ROOT#u9", outcomes(true));
        assertEquals("", ConcolicRegionRuntime.seedOutcomeConflict(
                recorded, wider));

        // Sites this activation never decided, and sites the recording never
        // planned, are judged over the whole summary rather than here.
        Map<String, Set<Boolean>> partial = new LinkedHashMap<>();
        partial.put("ROOT#u9", outcomes(true));
        partial.put("UNPLANNED#u2", outcomes(false));
        assertEquals("", ConcolicRegionRuntime.seedOutcomeConflict(
                recorded, partial));
    }

    private static Set<Boolean> outcomes(Boolean... values) {
        return new LinkedHashSet<>(Arrays.asList(values));
    }

    @Test
    public void outputCaptureOccurrencesAreActivationLocalAndSiteScoped() {
        ConcolicRegionRuntime.OutputCaptureOccurrenceCounter first =
                new ConcolicRegionRuntime.OutputCaptureOccurrenceCounter();

        assertEquals(1, first.observe("CAPTURE.A", "METHOD#u7"));
        assertEquals(2, first.observe("CAPTURE.A", "METHOD#u7"));
        assertEquals(1, first.observe("CAPTURE.A", "METHOD#u9"));
        assertEquals(1, first.observe("CAPTURE.B", "METHOD#u7"));
        assertEquals(2, first.observed("CAPTURE.A", "METHOD#u7"));

        // A repeated logical region activation must not inherit the prior
        // activation's hook count.
        ConcolicRegionRuntime.OutputCaptureOccurrenceCounter second =
                new ConcolicRegionRuntime.OutputCaptureOccurrenceCounter();
        assertEquals(1, second.observe("CAPTURE.A", "METHOD#u7"));
    }

    @Test
    public void helperArgumentOccurrencesAreActivationLocalAndSlotScoped() {
        String constructor = "<test.Key: void <init>(int,long)>";
        ConcolicRegionRuntime.MaterializationOccurrenceCounter first =
                new ConcolicRegionRuntime
                        .MaterializationOccurrenceCounter();

        for (int occurrence = 1; occurrence <= 25; occurrence++) {
            assertEquals(occurrence,
                    first.methodArgument(constructor, 0));
        }
        assertEquals(25,
                first.observedMethodArgument(constructor, 0));
        assertEquals(1, first.methodArgument(constructor, 1));
        assertEquals(1,
                first.observedMethodArgument(constructor, 1));
        assertEquals(1, first.local(constructor, 6, "i0"));

        // A later compatible region activation starts its own replay-stable
        // helper ordinal instead of inheriting the earlier activation.
        ConcolicRegionRuntime.MaterializationOccurrenceCounter second =
                new ConcolicRegionRuntime
                        .MaterializationOccurrenceCounter();
        assertEquals(0,
                second.observedMethodArgument(constructor, 0));
        assertEquals(1, second.methodArgument(constructor, 0));
    }

    /** Selection index for a capture whose version ordinal is irrelevant. */
    private static ConcolicRegionRuntime.MutationCaptureIndex index(
            int selection) {
        return new ConcolicRegionRuntime.MutationCaptureIndex(
                selection, selection);
    }

    @Test
    public void repeatedMutationOfOneContainerFoldsIntoTheExitSnapshot() {
        ConcolicRegionRuntime.MutationMethodScope scope =
                new ConcolicRegionRuntime.MutationMethodScope();
        Object keys = new Object();

        // addKeys puts every key on one receiver inside one invocation; the
        // relation is that receiver's state at the invocation's normal exit.
        ConcolicRegionRuntime.PendingMutationCapture anchor =
                new ConcolicRegionRuntime.PendingMutationCapture(null, keys,
                        index(1));
        assertEquals(ConcolicRegionRuntime.MutationMethodScope
                        .Selection.ANCHORED, scope.offer(anchor));
        for (int occurrence = 2; occurrence <= 8; occurrence++) {
            assertEquals(ConcolicRegionRuntime.MutationMethodScope
                            .Selection.FOLDED,
                    scope.offer(new ConcolicRegionRuntime
                            .PendingMutationCapture(null, keys,
                                    index(occurrence))));
        }
        assertSame(anchor, scope.pendingForTests());
    }

    @Test
    public void mutationOfASecondContainerPoisonsTheInvocation() {
        ConcolicRegionRuntime.MutationMethodScope scope =
                new ConcolicRegionRuntime.MutationMethodScope();
        Object keys = new Object();
        Object other = new Object();

        assertEquals(ConcolicRegionRuntime.MutationMethodScope
                        .Selection.ANCHORED,
                scope.offer(new ConcolicRegionRuntime
                        .PendingMutationCapture(null, keys, index(1))));
        // A different receiver makes the exit snapshot ambiguous.
        assertEquals(ConcolicRegionRuntime.MutationMethodScope
                        .Selection.AMBIGUOUS,
                scope.offer(new ConcolicRegionRuntime
                        .PendingMutationCapture(null, other, index(2))));
        assertNull(scope.pendingForTests());

        // A later mutation must not re-anchor the poisoned invocation.
        assertEquals(ConcolicRegionRuntime.MutationMethodScope
                        .Selection.IGNORED,
                scope.offer(new ConcolicRegionRuntime
                        .PendingMutationCapture(null, keys, index(3))));
        assertNull(scope.pendingForTests());
    }

    @Test
    public void singleExactOutputCompletesBoundaryOnlyAfterCapture() {
        JsonObject task = exactOutputTask(1);
        JsonArray captures = new JsonArray();

        assertFalse(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
        captures.add(exactOutputCapture(0));
        assertTrue(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
    }

    @Test
    public void multipleExactOutputsWaitForTheLastBinding() {
        JsonObject task = exactOutputTask(2);
        JsonArray captures = new JsonArray();
        captures.add(exactOutputCapture(0));

        assertFalse(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
        captures.add(exactOutputCapture(1));
        assertTrue(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));

        // Observing the same site again is another version of the same
        // relation, not a second relation, so it is not a contradiction.
        captures.add(exactOutputCapture(1));
        assertTrue(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
    }

    @Test
    public void resourceCutCompletionIsPerCapturedDemandedPort() {
        JsonObject task = exactOutputTask(2);
        JsonArray captures = new JsonArray();

        // With no VM capture the cap is only a gap.
        assertFalse(ConcolicRegionRuntime
                .resourceCutCapturedOutputForTests(task, captures));
        // Once one demanded port was captured, preserve that port from this
        // VM path.  The other port remains an explicit incomplete-relation
        // gap; the resource cut cannot manufacture it.
        captures.add(exactOutputCapture(0));
        assertTrue(ConcolicRegionRuntime
                .resourceCutCapturedOutputForTests(task, captures));
        assertFalse(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
        captures.add(exactOutputCapture(1));
        assertTrue(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
    }

    @Test
    public void anObservationAtAnotherOccurrenceStillCompletesTheBoundary() {
        // The goal states the relation without an invocation ordinal, so a
        // bounded replay that reaches the site a different number of times
        // than the recording did has still observed the relation.
        JsonObject task = exactOutputTask(1);
        JsonArray captures = new JsonArray();
        JsonObject later = exactOutputCapture(0);
        later.addProperty("outputOccurrence", 3);
        captures.add(later);

        assertTrue(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
    }

    @Test
    public void anObservationPastTheLoopBoundOrdinalIsStillAdmitted() {
        // The per-site occurrence counts every activation-local execution,
        // nested calls and multiple loop nests included.  A replay whose
        // loops all stay within the CFG bound can still reach one capture
        // site past the per-loop ordinal; that observation is the same
        // relation, not a bound violation, so it completes the boundary.
        JsonObject task = exactOutputTask(1);
        JsonArray captures = new JsonArray();
        JsonObject beyond = exactOutputCapture(0);
        beyond.addProperty("outputOccurrence",
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS + 18);
        captures.add(beyond);

        assertTrue(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
    }

    @Test
    public void anObservationAtAnotherSiteIsNotAdmitted() {
        JsonObject task = exactOutputTask(1);
        JsonArray captures = new JsonArray();
        JsonObject elsewhere = exactOutputCapture(0);
        elsewhere.addProperty("outputSiteId", "<test.Worker: void run()>#u99");
        captures.add(elsewhere);

        assertFalse(ConcolicRegionRuntime
                .exactOutputBoundaryReachedForTests(task, captures));
    }

    @Test
    public void anUnobservedDemandedBranchSiteKeepsTheReplayOpen() {
        String addKeys = "<test.Keys: void addKeys()>#u16";
        String expiry = "<test.Keys: void removeExpired()>#u14";
        List<String> demanded = Arrays.asList(addKeys, expiry);
        Set<String> observed = new LinkedHashSet<>();
        observed.add(addKeys);

        // The plan replays the expiry guard, so capturing the output
        // relation while that site has never executed is not the end of the
        // work the plan demands.
        assertFalse(ConcolicRegionRuntime.demandedBranchSitesObserved(
                demanded, observed));

        observed.add(expiry);
        assertTrue(ConcolicRegionRuntime.demandedBranchSitesObserved(
                demanded, observed));

        // A task whose demanded sites were all observed - or that demands
        // none - keeps the original exact boundary.
        assertTrue(ConcolicRegionRuntime.demandedBranchSitesObserved(
                Collections.<String>emptyList(),
                Collections.<String>emptySet()));
    }

    @Test
    public void witnessingAReplaysSourceSiteDoesNotConsumeItsContract() {
        String expiry = "<test.Keys: void removeExpired()>#u14";
        BranchReplayContract contract = BranchReplayContract.flip(
                Collections.<BranchWitness>emptyList(),
                replayWitness(expiry, 1, true));
        ConcolicRegionRuntime.ReplayProgress progress =
                new ConcolicRegionRuntime.ReplayProgress(contract);

        // The site has executed, so every demanded branch site is observed
        // and the pre-replay half of the boundary is satisfied.  The replay
        // itself has consumed nothing yet, so the window must stay open.
        assertTrue(ConcolicRegionRuntime.demandedBranchSitesObserved(
                Collections.singletonList(expiry),
                Collections.singleton(expiry)));
        assertFalse(progress.complete());

        // Only the demanded outcome closes it.
        assertTrue(progress.observe(expiry, 1, false));
        assertTrue(progress.complete());
    }

    @Test
    public void onlyASymbolicallyGuardedLoopSpendsTheUnrollBudget() {
        String method = "<test.Keys: void addKeys()>";
        String loop = method + "#loop:u13";
        String guard = method + "#u16";

        // A concrete array walk repeats as often as its data says.
        assertTrue(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, guard, true));
        // A guard the VM decided symbolically is a real path branch.
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, guard, false));
        // A decision from another method, or none at all, answers nothing
        // about this header and is charged.
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true,
                "<test.Keys: void removeExpired()>#u16", true));
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, "", true));

        // A released traversal leaves the budget where it was, so a long
        // concrete loop never starves the symbolic loops beside it.
        int bound = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
        ConcolicRegionRuntime.LoopBackedgeBudget budget =
                new ConcolicRegionRuntime.LoopBackedgeBudget(
                        LoopBoundPolicy.cfgBackedges(bound));
        for (int traversal = 0; traversal < 2 * bound; traversal++) {
            budget.recordGuardedTraversal(loop);
            budget.releaseTraversal(loop);
            assertTrue(budget.canEnterBody(loop));
        }
        for (int traversal = 0; traversal < bound; traversal++) {
            budget.recordGuardedTraversal(loop);
        }
        assertFalse(budget.canEnterBody(loop));
    }

    @Test
    public void theResourceCapCountsEveryBodyTheUnrollBoundIgnores() {
        String method = "<test.Keys: void addKeys()>";
        String loop = method + "#loop:u13";
        int bound = LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS;
        ConcolicRegionRuntime.LoopBackedgeBudget budget =
                new ConcolicRegionRuntime.LoopBackedgeBudget(
                        LoopBoundPolicy.cfgBackedges(bound));

        // A concrete guard releases the unroll traversal it was charged, but
        // the body it entered still spent replay resource.  The two ledgers
        // are independent: one caps the path space, the other caps the work.
        for (int body = 1; body <= 3 * bound; body++) {
            budget.recordGuardedTraversal(loop);
            budget.releaseTraversal(loop);
            assertEquals(body, budget.recordBody(loop));
            assertTrue(budget.canEnterBody(loop));
        }
        assertEquals(3 * bound,
                budget.bodiesToJson().get(loop).getAsInt());
        // The unroll ledger is untouched by all that work.
        assertEquals(0, budget.completed(loop));
    }

    @Test
    public void aServiceLoopIsCappedTighterThanASliceLoop() {
        // A loop the output closure names walks the data the slice is stated
        // over; every other loop on the replay path is a service loop whose
        // every turn is a heartbeat of unrelated symbolic work.
        assertEquals(LoopBoundPolicy.MAX_EXECUTION_SCOPE_LOOP_BODIES,
                LoopBoundPolicy.maxLoopBodies(true));
        assertEquals(LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES,
                LoopBoundPolicy.maxLoopBodies(false));
        assertTrue(LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES
                < LoopBoundPolicy.MAX_EXECUTION_SCOPE_LOOP_BODIES);
        // Both caps stay clear of the unroll bound, which they must never
        // stand in for.
        assertTrue(LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS
                < LoopBoundPolicy.MAX_REPLAY_PATH_LOOP_BODIES);
    }

    @Test
    public void aSpentResourceCapNamesItselfInsteadOfTruncating() {
        ConcolicRegionRuntime.ReplayLoopResourceCut cut =
                new ConcolicRegionRuntime.ReplayLoopResourceCut(
                        "<test.Actor: void offerService()>#loop:u7", 32, 33L);
        JsonObject encoded = cut.toJson();
        assertEquals("REPLAY_LOOP_RESOURCE_CAP",
                encoded.get("kind").getAsString());
        assertEquals("REPLAY_LOOP_RESOURCE_CAP",
                encoded.get("reason").getAsString());
        assertEquals(32, encoded.get("maxLoopBodies").getAsInt());
        assertEquals(33L, encoded.get("attemptedBody").getAsLong());
        assertTrue(cut.detail().startsWith("REPLAY_LOOP_RESOURCE_CAP:"));
        assertTrue(cut.detail().endsWith(":33/32"));
    }

    @Test
    public void readingOnePathConditionAgreesWithParsingAllOfIt() {
        // One document, both readers.  The shapes are the ones a serialized
        // path condition actually carries: nested expression trees, code
        // positions holding the punctuation that delimits JSON, escapes, and
        // every primitive form.
        String document = pathConditionDocument();
        JsonArray parsed = new JsonParser().parse(document).getAsJsonArray();
        ConcolicRegionRuntime.PathConditionElements scanned =
                ConcolicRegionRuntime.PathConditionElements.of(document);

        assertEquals("SCAN", scanned.mode());
        assertEquals(parsed.size(), scanned.size());
        for (int index = 0; index < parsed.size(); index++) {
            assertEquals(parsed.get(index), scanned.get(index));
        }

        // Whitespace between elements is not part of any element.
        String pretty = new com.google.gson.GsonBuilder().setPrettyPrinting()
                .create().toJson(parsed);
        ConcolicRegionRuntime.PathConditionElements indented =
                ConcolicRegionRuntime.PathConditionElements.of(pretty);
        assertEquals("SCAN", indented.mode());
        assertEquals(parsed.size(), indented.size());
        for (int index = 0; index < parsed.size(); index++) {
            assertEquals(parsed.get(index), indented.get(index));
        }

        // An empty path condition is an empty array, not an absent one.
        assertEquals(0,
                ConcolicRegionRuntime.PathConditionElements.of("[]").size());
        assertEquals("SCAN",
                ConcolicRegionRuntime.PathConditionElements.of("  [ ] ")
                        .mode());

        // Documents the scanner cannot split with certainty are handed to the
        // tree parser, so every document reads exactly as it did before.
        for (String other : new String[] {null, "", "   ", "{\"a\":1}",
                "[1,2", "[1,]", "[\"unterminated]", "[1 2]", "not json",
                "[]", document}) {
            JsonArray expected = treeConditions(other);
            ConcolicRegionRuntime.PathConditionElements actual =
                    ConcolicRegionRuntime.PathConditionElements.of(other);
            assertEquals(other + " condition count",
                    expected.size(), actual.size());
            for (int index = 0; index < expected.size(); index++) {
                assertEquals(other + " condition " + index,
                        expected.get(index), actual.get(index));
            }
        }
    }

    /** The path-condition reading this replaced: parse it all, keep an array. */
    private static JsonArray treeConditions(String raw) {
        if (raw == null || raw.trim().isEmpty()) return new JsonArray();
        final com.google.gson.JsonElement parsed;
        try {
            parsed = new JsonParser().parse(raw);
        } catch (RuntimeException malformed) {
            return new JsonArray();
        }
        return parsed.isJsonArray() ? parsed.getAsJsonArray() : new JsonArray();
    }

    /** A document shaped like the VM's serialized path condition. */
    private static String pathConditionDocument() {
        JsonArray conditions = new JsonArray();
        String[] operators = {"==", "<", ">=", "!="};
        for (int index = 0; index < operators.length; index++) {
            JsonObject left = new JsonObject();
            left.addProperty("_type", "SymbolExpression");
            left.addProperty("_exp", "environment__currentTimeMills_" + index);
            JsonObject right = new JsonObject();
            right.addProperty("_type", "ConstExpr");
            right.addProperty("_value", -1L - index);
            JsonObject condition = new JsonObject();
            // Punctuation and escapes inside a string must not split it.
            condition.addProperty("_code_position",
                    "virtual jlong java.util.Date.getTimeImpl(),[{\"}]:"
                            + index + "\\");
            condition.addProperty("_type", "BinaryExpression");
            condition.add("_left", left);
            condition.addProperty("_op", operators[index]);
            condition.add("_right", right);
            JsonArray operands = new JsonArray();
            operands.add(left);
            operands.add(right);
            condition.add("_operands", operands);
            conditions.add(condition);
        }
        // Primitive elements are values of the array too.
        conditions.add(new JsonParser().parse("true"));
        conditions.add(new JsonParser().parse("false"));
        conditions.add(com.google.gson.JsonNull.INSTANCE);
        conditions.add(new JsonParser().parse("-12.5e3"));
        conditions.add(new JsonParser().parse("\"[a,b]\""));
        conditions.add(new JsonParser().parse("[]"));
        conditions.add(new JsonParser().parse("{}"));
        return conditions.toString();
    }

    @Test
    public void onlyTheLoopsOwnGuardAnswersForItsBody() {
        // A guard that is a branch site of the symbolic slice decides every
        // body of its loop, so it is the only witness accepted for one.
        String method = "<test.Keys: void removeExpiredKeys()>";
        String loop = method + "#loop:u5";
        String guard = method + "#u6";
        String bodyBranch = method + "#u14";

        assertTrue(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, guard, true));
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, guard, false));
        // A branch of the body can no longer stand in for a guard that did
        // decide.  It runs between two body entries and shares the loop's
        // method, so this is what a "most recent decision" rule mistook for
        // the header - releasing a loop the solver chooses, or charging one
        // the replay merely walks.
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, bodyBranch, true));
        // A decision from another method answers nothing about this loop.
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, true, "<test.Keys: void addKeys()>#u6", true));
        // A guard outside the slice never decides, and no witness for it can
        // be produced.  The loop keeps the evidence this replay does have,
        // its own method's attested decision, rather than spending the unroll
        // bound on every concrete walk over recorded data.  Its bodies are
        // still charged to the replay resource cap.
        assertTrue(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, false, bodyBranch, true));
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, guard, false, bodyBranch, false));
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, "", false, "", true));
        // Even without a guard, only this loop's own method can answer.
        assertFalse(ConcolicRegionRuntime.concreteGuardEnteredBody(
                loop, "", false, "<test.Keys: void addKeys()>#u6", true));

        // The body-entry edge carries both facts; the ledger stays keyed by
        // the loop, so the latch hooks and this hook spend one budget.
        String encoded = loop + "@guard:u6";
        assertEquals(loop, ConcolicRegionRuntime.loopIdentity(encoded));
        assertEquals(guard, ConcolicRegionRuntime.bodyEntryGuardSite(encoded));

        // An edge instrumented before guards were named, or one whose guard
        // is malformed, names no guard and is charged.
        assertEquals(loop, ConcolicRegionRuntime.loopIdentity(loop));
        assertEquals("", ConcolicRegionRuntime.bodyEntryGuardSite(loop));
        assertEquals("", ConcolicRegionRuntime.bodyEntryGuardSite(
                loop + "@guard:u"));
        assertEquals("", ConcolicRegionRuntime.bodyEntryGuardSite(
                loop + "@guard:ux6"));
    }

    @Test
    public void eachBoundedAccessorOccurrenceKeepsItsOwnSymbol() {
        // The replay counts its accessor calls from one, so the demanded
        // occurrence is the one bounded to a single helper activation.
        // Every occurrence still stands on its own - the second key's
        // accessor must not answer for the first key's.
        assertTrue(ConcolicRegionRuntime
                .acceptsBoundedAccessorOccurrence(1, 1));
        assertTrue(ConcolicRegionRuntime
                .acceptsBoundedAccessorOccurrence(7, 7));
        assertFalse(ConcolicRegionRuntime
                .acceptsBoundedAccessorOccurrence(2, 1));

        // A recording-wide ordinal such as 12 counts calls this replay's
        // activation never made, so demanding it would leave the input
        // concrete for every occurrence the replay does reach.
        assertFalse(ConcolicRegionRuntime
                .acceptsBoundedAccessorOccurrence(12, 1));

        // An action that names no occurrence stays unconstrained.
        assertTrue(ConcolicRegionRuntime
                .acceptsBoundedAccessorOccurrence(-1, 3));
    }

    private static JsonObject exactOutputTask(int outputCount) {
        String region = "REGION.BOUNDARY";
        String instance = region + "@test#call1";
        String method = "<test.Worker: void run()>";
        List<OutputClosureContract> members = new ArrayList<>();
        for (int index = 0; index < outputCount; index++) {
            String port = region + ".out." + index;
            String cell = "<test.State: int value" + index + ">";
            String site = method + "#u" + (index + 1);
            JsonObject capture = new JsonObject();
            capture.addProperty("captureBindingId", "CAPTURE." + index);
            capture.addProperty("captureKind",
                    OutputCaptureSpec.FIELD_WRITE_STATE);
            capture.addProperty("outputPort", port);
            capture.addProperty("outputCell", cell);
            capture.addProperty("fieldSignature", cell);
            capture.addProperty("javaType", "int");
            capture.addProperty("definitionMethod", method);
            capture.addProperty("definitionUnitIndex", index + 1);
            capture.addProperty("outputSiteId", site);
            capture.addProperty("outputOccurrence", 1);
            capture.addProperty("replayOccurrence", 1);

            JsonArray captureBindings = new JsonArray();
            captureBindings.add(capture);
            JsonObject slice = new JsonObject();
            slice.addProperty("outputPort", port);
            slice.addProperty("outputCell", cell);
            slice.add("inputPorts", new JsonArray());
            slice.add("sites", strings(site));
            slice.add("staticSites", strings(site));
            slice.add("methods", strings(method));
            slice.add("causalEdgeIds", new JsonArray());
            slice.add("causalEdges", new JsonArray());
            slice.add("captureBindings", captureBindings);
            slice.add("captureBindingIssues", new JsonArray());
            members.add(OutputClosureCodec.singleton(region, instance, 1L,
                    port, cell, "HEAP_STATE", "int", slice));
        }

        JsonObject task = new JsonObject();
        task.addProperty("taskId", "TASK.BOUNDARY");
        task.addProperty("goalId", "GOAL.BOUNDARY");
        task.addProperty("regionId", region);
        task.addProperty("regionInstanceId", instance);
        task.addProperty("rootCallId", 1L);
        ClosureGoalKind.OUTPUT_RELATION_CLOSURE.writeToTask(task);
        task.add("inputActions", new JsonArray());
        task.add("branches", new JsonArray());
        LoopBoundPolicy.cfgBackedges(
                LoopBoundPolicy.MAX_LOOP_BODY_ITERATIONS).writeTo(task);
        OutputClosureCodec.writeTo(task, OutputClosureCodec.merge(members));
        return task;
    }

    private static JsonObject exactOutputCapture(int index) {
        JsonObject capture = new JsonObject();
        capture.addProperty("captureBindingId", "CAPTURE." + index);
        capture.addProperty("outputSiteId",
                "<test.Worker: void run()>#u" + (index + 1));
        capture.addProperty("outputOccurrence", 1);
        capture.addProperty("replayOccurrence", 1);
        JsonObject expression = new JsonObject();
        expression.addProperty("_type", "ConstExpr");
        expression.addProperty("_exp", "Y_I_" + index);
        capture.add("expression", expression);
        return capture;
    }

    private static JsonArray strings(String... values) {
        JsonArray result = new JsonArray();
        for (String value : values) result.add(value);
        return result;
    }

    private static BranchWitness replayWitness(
            String site, int occurrence, boolean outcome) {
        JsonObject left = new JsonObject();
        left.addProperty("_type", "SymbolExpression");
        left.addProperty("_exp", "REGION.IN.value");
        JsonObject right = new JsonObject();
        right.addProperty("_type", "ConstExpr");
        right.addProperty("_exp", "Y_I_0");
        JsonObject predicate = new JsonObject();
        predicate.addProperty("_type", "BinaryExpression");
        predicate.addProperty("_op", outcome ? ">" : "<=");
        predicate.add("_left", left);
        predicate.add("_right", right);
        return BranchWitness.vmPc(site, "ROOT", 1, occurrence, outcome,
                predicate, occurrence, new JsonObject());
    }

    @Test
    public void interruptedRegionRootStillPersistsItsResult() throws Exception {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        java.nio.file.Path output = folder.newFile("result.jsonl").toPath();

        Thread.currentThread().interrupt();
        try {
            assertTrue(ConcolicRegionRuntime.appendResultLine(
                    output, result, "{\"complete\":true}"));
            assertTrue(Thread.currentThread().isInterrupted());
        } finally {
            Thread.interrupted();
        }

        JsonObject persisted = new JsonParser().parse(new String(
                Files.readAllBytes(output), StandardCharsets.UTF_8).trim())
                .getAsJsonObject();
        assertEquals("CONCOLIC_REGION_RESULT",
                persisted.get("event").getAsString());
        assertTrue(persisted.getAsJsonObject("engineSummary")
                .get("complete").getAsBoolean());
    }

    @Test
    public void inactiveBackedgeHookDoesNotChangeWorkloadExecution() {
        ConcolicRegionRuntime.resetForTests();

        ConcolicRegionRuntime.checkLoopBackedge(
                "<test.Loop: void run()>#backedge:u4->u1", 1);
    }

    @Test
    public void unguardedEighthBackedgeCutsBeforeNinthLoopBody() {
        ConcolicRegionRuntime.LoopBackedgeBudget budget =
                new ConcolicRegionRuntime.LoopBackedgeBudget(
                        LoopBoundPolicy.cfgBackedges(8));
        String edge = "<test.Loop: void run()>#backedge:u4->u1";

        for (int attempt = 1; attempt <= 8; attempt++) {
            assertEquals(attempt, budget.recordTraversal(edge));
        }
        // A denied attempt is not reported as a completed traversal.
        assertEquals(7, budget.toJson().get(edge).getAsInt());

        ConcolicRegionRuntime.LoopBoundCut cut =
                new ConcolicRegionRuntime.LoopBoundCut(
                        edge, 8, 8L,
                        "MAX_LOOP_BODY_ITERATIONS_REACHED");
        JsonObject encoded = cut.toJson();
        assertEquals("LOOP_BOUND", encoded.get("kind").getAsString());
        assertEquals(8L, encoded.get("attemptedTraversal").getAsLong());
        assertEquals(8, encoded.get("maxLoopBodyIterations").getAsInt());
        assertEquals("MAX_LOOP_BODY_ITERATIONS_REACHED",
                encoded.get("reason").getAsString());
        assertEquals("CUT",
                ConcolicRegionRuntime.exceptionalExitKind(cut));
        assertEquals("THROW", ConcolicRegionRuntime.exceptionalExitKind(
                new IllegalStateException("workload failure")));
    }

    @Test
    public void guardedLoopCanExitNormallyAfterEightBodies() {
        ConcolicRegionRuntime.LoopBackedgeBudget budget =
                new ConcolicRegionRuntime.LoopBackedgeBudget(
                        LoopBoundPolicy.cfgBackedges(8));
        String loop = "<test.Loop: void run()>#loop:u1";

        assertTrue(budget.canEnterBody(loop));
        for (int completed = 1; completed <= 8; completed++) {
            assertEquals(completed,
                    budget.recordGuardedTraversal(loop));
            if (completed < 8) assertTrue(budget.canEnterBody(loop));
        }
        assertEquals(8, budget.completed(loop));
        assertFalse(budget.canEnterBody(loop));
        // A false header guard invokes no body-entry hook and therefore exits
        // normally. A true guard consults canEnterBody and cuts before body 9.
    }

    @Test
    public void completeContainerSnapshotsFailClosedAboveCapacity() {
        ConcolicRegionRuntime.requireCompleteContainerSnapshotCapacity(
                new int[LoopBoundPolicy
                        .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY]);
        try {
            ConcolicRegionRuntime.requireCompleteContainerSnapshotCapacity(
                    new int[LoopBoundPolicy
                            .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY + 1]);
            fail("oversized complete snapshot must be rejected");
        } catch (IllegalStateException expected) {
            assertTrue(expected.getMessage().contains(
                    "BOUND_INSUFFICIENT"));
            assertTrue(expected.getMessage().contains(
                    "symbolic snapshot capacity is " + LoopBoundPolicy
                            .SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY));
        }
    }

    @Test
    public void sparseIndexedAssignmentsMutateOnlyRequestedElements() {
        int[] array = new int[]{3, 5, 7};
        List<Integer> list = new ArrayList<>(Arrays.asList(11, 13, 17));
        Object arrayIdentity = array;
        Object listIdentity = list;

        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                array, 0, "INT", "19"));
        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                array, 2, "INT", "23"));
        assertTrue(ConcolicRegionRuntime.writeIndexedContainerElement(
                list, 1, "INT", "29"));

        assertSame(arrayIdentity, array);
        assertSame(listIdentity, list);
        assertArrayEquals(new int[]{19, 5, 23}, array);
        assertEquals(Arrays.asList(11, 29, 17), list);
    }

    @Test
    public void invalidIndexedTargetsFailWithoutReplacingContainers() {
        int[] array = new int[]{3};
        List<Integer> immutable = Collections.singletonList(5);

        assertFalse(ConcolicRegionRuntime.writeIndexedContainerElement(
                array, 1, "INT", "7"));
        assertFalse(ConcolicRegionRuntime.writeIndexedContainerElement(
                immutable, 0, "INT", "7"));
        assertFalse(ConcolicRegionRuntime.writeIndexedContainerElement(
                new Object(), 0, "INT", "7"));

        assertArrayEquals(new int[]{3}, array);
        assertEquals(Collections.singletonList(5), immutable);
    }

    @Test
    public void replayWriteSuppressesOnlyTheSameExactFieldLiveIn() {
        Object writtenOwner = new Object();
        Object otherOwner = new Object();
        ConcolicRegionRuntime.ReplayFieldWrites writes =
                new ConcolicRegionRuntime.ReplayFieldWrites();

        writes.add(writtenOwner, RESULT_FIELD);

        assertTrue(writes.contains(writtenOwner, RESULT_FIELD));
        assertFalse(writes.contains(writtenOwner, OTHER_FIELD));
        assertFalse(writes.contains(otherOwner, RESULT_FIELD));
        assertFalse(writes.contains(writtenOwner, "result"));
    }

    @Test
    public void associativeReplayNeverCreatesAnAbsentKey() {
        Map<Integer, Object> values = new LinkedHashMap<>();
        values.put(3, null);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(values,
                associativeAssignment(7, "NULL", false), null));
        assertFalse(values.containsKey(7));
        assertTrue(values.containsKey(3));
        assertEquals(null, values.get(3));

        assertFalse(ConcolicRegionRuntime.writeContainerTarget(values,
                associativeAssignment(7,
                        "CONTAINER_REFERENCE_ALIAS", true), new Object()));
        assertFalse(values.containsKey(7));
    }

    @Test
    public void dynamicAssociativeReplayTargetsTheCurrentRunKey() {
        Map<Integer, Object> values = new LinkedHashMap<>();
        Object original = new Object();
        values.put(41, original);
        ConcolicRegionRuntime.ModelAssignment assignment =
                dynamicAssociativeAssignment(1, "NULL");

        assertTrue(ConcolicRegionRuntime.writeAssociativeContainerTarget(
                values, 41, assignment, null));
        assertTrue(values.containsKey(41));
        assertEquals(null, values.get(41));
        assertFalse(values.containsKey(7));
    }

    @Test
    public void referenceReplayReplacesOnlyExistingContainerSlots() {
        Object oldIndexed = new Object();
        Object sourceIndexed = new Object();
        List<Object> indexed = new ArrayList<>(
                Collections.singletonList(oldIndexed));
        ConcolicRegionRuntime.ModelAssignment indexedAssignment =
                indexedReferenceAssignment(0);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(indexed,
                indexedAssignment, sourceIndexed));
        assertEquals(1, indexed.size());
        assertSame(sourceIndexed, indexed.get(0));
        assertFalse(ConcolicRegionRuntime.writeContainerTarget(indexed,
                indexedReferenceAssignment(1), new Object()));
        assertEquals(1, indexed.size());

        Object oldMapped = new Object();
        Object sourceMapped = new Object();
        Map<Integer, Object> mapped = new LinkedHashMap<>();
        mapped.put(3, oldMapped);

        assertTrue(ConcolicRegionRuntime.writeContainerTarget(mapped,
                associativeAssignment(3,
                        "CONTAINER_REFERENCE_ALIAS", true), sourceMapped));
        assertEquals(1, mapped.size());
        assertSame(sourceMapped, mapped.get(3));
    }

    @Test
    public void orderedAssociativeReplayWritesTheSelectedCursor() {
        Set<Integer> set = new LinkedHashSet<>(Arrays.asList(3, 5));
        assertFalse(ConcolicRegionRuntime.writeContainerTarget(set,
                iterationAssignment(0, "KEY", 5), null));
        assertEquals(Arrays.asList(3, 5), new ArrayList<>(set));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(set,
                iterationAssignment(0, "KEY", 13), null));
        assertEquals(Arrays.asList(13, 5), new ArrayList<>(set));

        Map<Integer, Integer> map = new LinkedHashMap<>();
        map.put(3, 7);
        map.put(5, 11);
        assertFalse(ConcolicRegionRuntime.writeContainerTarget(map,
                iterationAssignment(0, "KEY", 5), null));
        assertEquals(Arrays.asList(3, 5),
                new ArrayList<>(map.keySet()));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(map,
                iterationAssignment(0, "KEY", 17), null));
        assertEquals(Arrays.asList(17, 5),
                new ArrayList<>(map.keySet()));
        assertTrue(ConcolicRegionRuntime.writeContainerTarget(map,
                iterationAssignment(1, "VALUE", 19), null));
        assertEquals(Integer.valueOf(19), map.get(5));
    }

    @Test
    public void modelReplayWritesTheDeclaredHiddenFieldOnly() {
        HiddenDerived owner = new HiddenDerived();
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "hidden-base");
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "7");
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);
        String baseField = "<" + HiddenBase.class.getName()
                + ": int value>";

        assertTrue(ConcolicRegionRuntime.writeModeledField(
                owner, baseField, assignment));
        assertEquals(7, ((HiddenBase) owner).value);
        assertEquals(2, owner.value);
    }

    private static class HiddenBase {
        int value = 1;
    }

    private static final class HiddenDerived extends HiddenBase {
        int value = 2;
    }

    private static final class InheritedOnlyDerived extends HiddenBase {
    }

    @Test
    public void modelReplayResolvesAnInheritedFieldReferenceOwner() {
        InheritedOnlyDerived owner = new InheritedOnlyDerived();
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "inherited-base");
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", "11");
        ConcolicRegionRuntime.ModelAssignment assignment =
                new ConcolicRegionRuntime.ModelAssignment(encoded);
        String inheritedReference = "<" + InheritedOnlyDerived.class.getName()
                + ": int value>";

        assertTrue(ConcolicRegionRuntime.writeModeledField(
                owner, inheritedReference, assignment));
        assertEquals(11, owner.value);
    }

    @Test
    public void nestedReferenceSourceUsesTheExistingFieldPathResolver() {
        NestedRoot root = new NestedRoot();

        assertSame(root.holder,
                ConcolicRegionRuntime.resolveFieldPathLeafOwner(root,
                        Arrays.asList("holder", "values")));
        assertSame(root.holder.values,
                ConcolicRegionRuntime.resolveFieldPathLeafOwner(root,
                        Arrays.asList("holder", "values", "[0]")));
    }

    private static ConcolicRegionRuntime.ModelAssignment
    indexedReferenceAssignment(int index) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "indexed-" + index);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "CONTAINER_REFERENCE_ALIAS");
        encoded.addProperty("referenceSourceInputSymbol", "REGION.0.in.1");
        JsonObject target = new JsonObject();
        target.addProperty("shape", "INDEXED");
        target.addProperty("index", index);
        target.addProperty("sourceShape", "INDEXED");
        target.addProperty("sourceIndex", 0);
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    private static ConcolicRegionRuntime.ModelAssignment
    associativeAssignment(int key, String valueType, boolean alias) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "test-" + key + "-"
                + valueType);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", valueType);
        if (alias) {
            encoded.addProperty("referenceSourceInputSymbol",
                    "REGION.0.in.1");
        }
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("keyJavaType", "I");
        target.addProperty("keyValue", Integer.toString(key));
        if (alias) {
            target.addProperty("sourceShape", "ASSOCIATIVE");
            target.addProperty("sourceKeyJavaType", "I");
            target.addProperty("sourceKeyValue", "3");
        }
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    private static ConcolicRegionRuntime.ModelAssignment
    dynamicAssociativeAssignment(int ordinal, String valueType) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "dynamic-" + ordinal);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", valueType);
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("selectorKind", "ACCESS_ORDINAL");
        target.addProperty("accessOrdinal", ordinal);
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    private static ConcolicRegionRuntime.ModelAssignment
    iterationAssignment(int index, String projection, int value) {
        JsonObject encoded = new JsonObject();
        encoded.addProperty("modelAssignmentKey", "iteration-" + index);
        encoded.addProperty("inputSymbol", "REGION.0.in.0");
        encoded.addProperty("valueType", "INT");
        encoded.addProperty("value", Integer.toString(value));
        JsonObject target = new JsonObject();
        target.addProperty("shape", "ASSOCIATIVE");
        target.addProperty("selectorKind", "ITERATION_INDEX");
        target.addProperty("index", index);
        target.addProperty("projection", projection);
        encoded.add("containerTarget", target);
        return new ConcolicRegionRuntime.ModelAssignment(encoded);
    }

    @Test
    public void concreteBranchWitnessIsReadableByTheImporter() {
        JsonObject witness = ConcolicRegionRuntime.concreteBranchWitness(
                "<test.Worker: void run()>", 3, false);
        // A concrete witness must never look like a solvable decision.
        assertFalse(witness.has("witness"));
        assertFalse(witness.has("occurrence"));
        assertFalse(witness.has("rawPathConditionSize"));

        JsonArray witnesses = new JsonArray();
        witnesses.add(witness);
        JsonObject raw = new JsonObject();
        raw.add("concreteBranchWitnesses", witnesses);

        Map<String, Set<Boolean>> decoded =
                ConcolicSummaryImporter.concreteBranchOutcomes(raw);
        assertEquals(Collections.singleton(Boolean.FALSE),
                decoded.get("<test.Worker: void run()>#u3"));
    }

    @Test
    public void engineReservationWaitsForTheHolderToRelease()
            throws Exception {
        ConcolicRegionRuntime.resetForTests();
        System.setProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY,
                "60000");
        try {
            assertEquals("",
                    ConcolicRegionRuntime.reserveSymbolicEngineForTests());
            final List<String> outcome = Collections.synchronizedList(
                    new ArrayList<String>());
            Thread waiter = new Thread(new Runnable() {
                @Override
                public void run() {
                    outcome.add(ConcolicRegionRuntime
                            .reserveSymbolicEngineForTests());
                }
            });
            waiter.start();
            // The waiter must not be discarded while the engine is held.
            waiter.join(200L);
            assertTrue(waiter.isAlive());
            assertTrue(outcome.isEmpty());

            ConcolicRegionRuntime.releaseSymbolicEngineForTests();
            waiter.join(30_000L);
            assertFalse(waiter.isAlive());
            assertEquals(Collections.singletonList(""), outcome);
        } finally {
            System.clearProperty(
                    ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY);
            ConcolicRegionRuntime.resetForTests();
        }
    }

    @Test
    public void engineReservationTimeoutIsANamedSkipReason() {
        ConcolicRegionRuntime.resetForTests();
        System.setProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY, "50");
        try {
            assertEquals("",
                    ConcolicRegionRuntime.reserveSymbolicEngineForTests());
            long started = System.currentTimeMillis();
            // A held engine may be blocked on the waiting thread itself, so
            // the wait must expire instead of deadlocking the workload.
            assertEquals(ConcolicRegionRuntime.ENGINE_BUSY_TIMEOUT,
                    ConcolicRegionRuntime.reserveSymbolicEngineForTests());
            assertTrue(System.currentTimeMillis() - started >= 50L);
        } finally {
            System.clearProperty(
                    ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY);
            ConcolicRegionRuntime.resetForTests();
        }
    }

    @Test
    public void terminalSelectedSkipHaltsNonzeroOnlyAfterDurableEvidence() {
        assertEquals(3, ConcolicRegionRuntime
                .terminalSelectedSkipHaltStatus(
                        ConcolicRegionRuntime.SKIP_ENGINE_UNAVAILABLE,
                        ConcolicRegionRuntime.ENGINE_BUSY_TIMEOUT, true));
        assertEquals(2, ConcolicRegionRuntime
                .terminalSelectedSkipHaltStatus(
                        ConcolicRegionRuntime.SKIP_ENGINE_UNAVAILABLE,
                        ConcolicRegionRuntime.ENGINE_BUSY_TIMEOUT, false));
        assertEquals(-1, ConcolicRegionRuntime
                .terminalSelectedSkipHaltStatus(
                        ConcolicRegionRuntime.SKIP_ENGINE_UNAVAILABLE,
                        ConcolicRegionRuntime.ENGINE_BUSY_INTERRUPTED, true));
        assertEquals(-1, ConcolicRegionRuntime
                .terminalSelectedSkipHaltStatus(
                        ConcolicRegionRuntime.SKIP_REPLAY_PREFIX_UNMATCHED,
                        "a later compatible activation may still match",
                        true));
    }

    @Test
    public void engineWaitBudgetFallsBackToTheDefault() {
        System.clearProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY);
        assertEquals(ConcolicRegionRuntime.DEFAULT_ENGINE_WAIT_MILLIS,
                ConcolicRegionRuntime.engineWaitMillis());
        System.setProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY,
                "not-a-number");
        try {
            assertEquals(ConcolicRegionRuntime.DEFAULT_ENGINE_WAIT_MILLIS,
                    ConcolicRegionRuntime.engineWaitMillis());
            System.setProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY,
                    "0");
            assertEquals(0L, ConcolicRegionRuntime.engineWaitMillis());
        } finally {
            System.clearProperty(
                    ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY);
        }
    }

    /**
     * Two candidate activations of one region template compete for the single
     * symbolic engine.  The one that wins it contradicts its recorded prefix
     * on its first replayed branch and then keeps executing, as a long-lived
     * workload root does.  Nothing it walks after that contradiction can
     * belong to the replayed path, so the engine must come back at the
     * contradiction and not at that root's eventual return -- otherwise the
     * candidate that could still match spends its whole wait budget on a
     * result that cannot exist.
     */
    @Test
    public void aContradictedReplayHandsTheEngineToTheNextCandidate()
            throws Exception {
        long budget = 20_000L;
        ConcolicRegionRuntime.resetForTests();
        System.setProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY,
                Long.toString(budget));
        BranchReplayContract contract = BranchReplayContract.flip(
                Collections.singletonList(replayWitness("ROOT#u1", 1, true)),
                replayWitness("ROOT#u7", 1, true));
        // The first candidate drives the prefix the other way; the second
        // reproduces it and reaches the demanded opposite source outcome.
        ReplayJob contradicting = new ReplayJob(
                ConcolicRegionRuntime.ENTRY_STATE_RANK_UNDECIDED, contract,
                new boolean[]{false}, new String[]{"ROOT#u1"},
                new int[]{1});
        ReplayJob matching = new ReplayJob(
                ConcolicRegionRuntime.ENTRY_STATE_RANK_UNDECIDED, contract,
                new boolean[]{true, false},
                new String[]{"ROOT#u1", "ROOT#u7"}, new int[]{1, 1});
        Thread first = new Thread(contradicting, "candidate-1");
        Thread second = new Thread(matching, "candidate-2");
        try {
            first.start();
            assertTrue(contradicting.reserved.await(30, TimeUnit.SECONDS));
            assertEquals("", contradicting.contention);

            // Only the first candidate is sequenced; the second replays as
            // soon as it is admitted.
            matching.mayReplay.countDown();
            second.start();
            // The second candidate is now blocked on an engine it can only
            // get if the first one gives it back early.
            assertFalse(matching.reserved.await(200, TimeUnit.MILLISECONDS));

            contradicting.mayReplay.countDown();
            second.join(budget - 5_000L);
            assertFalse(second.isAlive());
            assertEquals("PUBLISHED", matching.outcome);
            assertEquals("", matching.contention);
            assertTrue(matching.waitedMillis < budget / 2);

            // The engine came back while its holder was still inside the
            // region root, which is the whole point.
            assertEquals("ABANDONED", contradicting.outcome);
            assertTrue(first.isAlive());
        } finally {
            contradicting.mayReplay.countDown();
            contradicting.regionBodyReturns.countDown();
            first.join(30_000L);
            second.join(30_000L);
            System.clearProperty(
                    ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY);
            ConcolicRegionRuntime.resetForTests();
        }
    }

    /**
     * A recorded entry value is compared value-wise, so it orders candidates
     * and never rejects one.  The candidate whose entry state still agrees
     * goes first while both are waiting.
     */
    @Test
    public void aBetterRankedCandidateTakesTheEngineFirst() throws Exception {
        ConcolicRegionRuntime.resetForTests();
        System.setProperty(ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY,
                "20000");
        final List<String> admitted = Collections.synchronizedList(
                new ArrayList<String>());
        Thread mismatched = null;
        Thread matched = null;
        try {
            assertEquals("",
                    ConcolicRegionRuntime.reserveSymbolicEngineForTests());
            mismatched = admissionOrderThread("MISMATCH",
                    ConcolicRegionRuntime.ENTRY_STATE_RANK_MISMATCH,
                    admitted);
            mismatched.start();
            // Both must be waiting before the engine is freed, or the test
            // would only observe arrival order.
            Thread.sleep(500L);
            matched = admissionOrderThread("MATCHES",
                    ConcolicRegionRuntime.ENTRY_STATE_RANK_MATCHES, admitted);
            matched.start();
            Thread.sleep(500L);
            assertTrue(admitted.isEmpty());

            ConcolicRegionRuntime.releaseSymbolicEngineForTests();
            matched.join(30_000L);
            mismatched.join(30_000L);
            // Ranking orders the candidates; it never discards the worse one.
            assertEquals(Arrays.asList("MATCHES", "MISMATCH"), admitted);
        } finally {
            if (matched != null) matched.join(30_000L);
            if (mismatched != null) mismatched.join(30_000L);
            System.clearProperty(
                    ConcolicRegionRuntime.ENGINE_WAIT_PROPERTY);
            ConcolicRegionRuntime.resetForTests();
        }
    }

    private static Thread admissionOrderThread(final String name,
                                               final int entryStateRank,
                                               final List<String> admitted) {
        return new Thread(new Runnable() {
            @Override
            public void run() {
                if (!ConcolicRegionRuntime.reserveSymbolicEngineForTests(
                        entryStateRank).isEmpty()) {
                    admitted.add(name + ":TIMEOUT");
                    return;
                }
                admitted.add(name);
                ConcolicRegionRuntime.releaseSymbolicEngineForTests();
            }
        }, name);
    }

    /**
     * One candidate activation, wired in the order the region hooks use it:
     * reserve the engine, replay the recorded prefix branch by branch, and
     * give the engine back at the first branch the prefix forbids -- before
     * the region root itself returns.
     */
    private static final class ReplayJob implements Runnable {
        private final int entryStateRank;
        private final BranchReplayContract contract;
        private final boolean[] outcomes;
        private final String[] sites;
        private final int[] occurrences;
        private final CountDownLatch reserved = new CountDownLatch(1);
        private final CountDownLatch mayReplay = new CountDownLatch(1);
        private final CountDownLatch regionBodyReturns =
                new CountDownLatch(1);
        private volatile String contention = "";
        private volatile String outcome = "";
        private volatile long waitedMillis = -1L;

        private ReplayJob(int entryStateRank, BranchReplayContract contract,
                          boolean[] outcomes, String[] sites,
                          int[] occurrences) {
            this.entryStateRank = entryStateRank;
            this.contract = contract;
            this.outcomes = outcomes;
            this.sites = sites;
            this.occurrences = occurrences;
        }

        @Override
        public void run() {
            long started = System.currentTimeMillis();
            contention = ConcolicRegionRuntime
                    .reserveSymbolicEngineForTests(entryStateRank);
            waitedMillis = System.currentTimeMillis() - started;
            reserved.countDown();
            if (!contention.isEmpty()) {
                outcome = "SKIPPED";
                return;
            }
            boolean held = true;
            try {
                mayReplay.await(30, TimeUnit.SECONDS);
                ConcolicRegionRuntime.ReplayProgress progress =
                        new ConcolicRegionRuntime.ReplayProgress(contract);
                for (int index = 0; index < sites.length; index++) {
                    progress.observe(sites[index], occurrences[index],
                            outcomes[index]);
                    if (progress.failed()) {
                        outcome = "ABANDONED";
                        ConcolicRegionRuntime
                                .releaseSymbolicEngineForTests();
                        held = false;
                        // The workload keeps running this root afterwards.
                        regionBodyReturns.await(30, TimeUnit.SECONDS);
                        return;
                    }
                }
                outcome = progress.complete() ? "PUBLISHED" : "INCOMPLETE";
            } catch (InterruptedException interrupted) {
                Thread.currentThread().interrupt();
                outcome = "INTERRUPTED";
            } finally {
                if (held) {
                    ConcolicRegionRuntime.releaseSymbolicEngineForTests();
                }
            }
        }
    }

    private static final class NestedRoot {
        private final NestedHolder holder = new NestedHolder();
    }

    private static final class NestedHolder {
        private final List<Object> values = new ArrayList<>(
                Collections.singletonList(new Object()));
    }
}
