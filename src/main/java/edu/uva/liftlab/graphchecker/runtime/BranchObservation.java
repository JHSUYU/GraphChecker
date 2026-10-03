package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.BranchWitness;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.contiguousConditionIndices;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.vmEventConditionIndices;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

/**
 * One decision of one instrumented site, as a published row (CONTRACT-SPEC
 * §2.2).
 *
 * <p>Reserve the VM event ({@link #prepare}), capture the decision against
 * the open path-condition window, state it to the replay-prefix matcher,
 * and address the target reach ({@link #observe}) -- written once against
 * {@link BranchDecision} for binary and multiway sites.  Nothing here may
 * change the workload's value.  Whether a decision may carry a term is
 * {@link VmBranchAttestation}'s to answer.</p>
 */
final class BranchObservation {
    private BranchObservation() {
    }

    /**
     * Reserves a VM-attested branch event immediately before the original
     * conditional executes.
     */
    static long prepare(String method, int unitIndex,
                        String expression) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || !active.pathRecordingStarted) return 0L;
        try {
            PreparedBranch prepared = active.prepareBranch(method, unitIndex,
                    expression);
            return prepared == null ? 0L : prepared.handle;
        } catch (Throwable throwable) {
            return 0L;
        }
    }

    /** Exact multiway counterpart of {@link #resolveBranch}. */
    static void observeSwitch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        SwitchExpectation expected;
        try {
            expected = SwitchExpectation.parse(branchKind, encodedCaseKeys,
                    observedSuccessorIndex);
        } catch (IllegalArgumentException malformed) {
            // The weave's case keys are refused by this decoder: NAMED as
            // UNATTESTED_ARM and recorded CONCRETE, so the row shows the site
            // ran (silence would read as "never reached") but states no term.
            ActiveRegion unattested = ConcolicRegionRuntime.activeRegion();
            RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                    SiteId.render(method, unitIndex),
                    "the weave states switch domain kind=" + safe(branchKind)
                            + " keys=[" + safe(encodedCaseKeys)
                            + "] successor=" + observedSuccessorIndex
                            + " and this decoder refuses it ("
                            + malformed.getMessage() + "), so the run cannot"
                            + " say whether a case arm or the default was"
                            + " taken: the decision is recorded as concrete,"
                            + " states no term, and its arm is not an"
                            + " observation");
            if (unattested != null) {
                unattested.recordConcreteDecision(method, unitIndex,
                        BranchDecision.binary(false));
            }
            return;
        }
        observe(BranchDecision.multiway(expected), preparedHandle,
                vmEventId, method, unitIndex, expression);
    }

    /** Observes one decision of either kind at one instrumented site. */
    static void observe(
            BranchDecision decision, long preparedHandle, long vmEventId,
            String method, int unitIndex, String expression) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null) return;
        String branchSite = SiteId.render(method, unitIndex);
        // A decision at a woven site is recorded whether or not the plan
        // declared the site: the recorded set must be what ran.
        if (!active.pathRecordingStarted) {
            int decided = active.recordConcreteDecision(method, unitIndex,
                    decision);
            if (decided > 0) {
                active.observeReplayDecision(branchSite, decided, decision);
                if (active.replayPrefixContradicted()) {
                    ConcolicRegionRuntime.finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                            null);
                }
            }
            return;
        }
        PreparedBranch prepared = active.takePreparedBranch(preparedHandle);
        if (prepared == null || !prepared.matches(method, unitIndex,
                expression)) {
            // No unverified VM event may be rebound heuristically.
            return;
        }
        ConcolicVmBroker api = engine();
        boolean paused = false;
        boolean replayContradicted = false;
        try {
            api.pausePathCondition();
            paused = true;
            boolean recorded = decision.recordPaused(active, api,
                    method, unitIndex, expression, prepared.occurrence,
                    vmEventId);
            // Advances the replay contract; says nothing about whether the
            // target site ran.
            active.observeReplayDecision(branchSite, prepared.occurrence,
                    decision);
            replayContradicted = active.replayPrefixContradicted();
            // A bounded loop may run the planned target occurrence at another
            // one: targetReach keeps the planner's ordinal, the mapping the
            // actual occurrence.
            boolean permuted = decision.addressesPermutedTargetOccurrence()
                    && FocusedReplay.focused(active.d3Address);
            if (ConcolicRegionRuntime.statesTargetReach(recorded, permuted,
                    active.activation.targetTest(branchSite),
                    active.activation.targetBranchOccurrence,
                    prepared.occurrence)) {
                // Reaching the target is the site having executed, nothing
                // else: not gated on a symbolic predicate (a concrete fatal
                // branch reached by control dependence still reaches), and not
                // on the replay contract (a flip whose source branch is
                // elsewhere names no event here, and every flip's disjunct is
                // wanted).  Recording continues: the occurrence still owes
                // RPC, state and throw effects.
                // The test that decided, at the planner's ordinal when a
                // loop permuted it: a disjunctive target is read from the
                // test the occurrence reached it at, and SOLR-18406's flipped
                // replay decided the second (#u20) with the first never run.
                active.recordTargetReach(branchSite,
                        permuted ? active.activation.targetBranchOccurrence
                                : prepared.occurrence,
                        decision.outcome(), vmEventId);
            }
        } catch (Throwable throwable) {
            RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                    branchSite + "#" + prepared.occurrence,
                    "this decision was not captured, so it states neither an"
                            + " arm nor the target reach that would have"
                            + " stood beside it: " + ConcolicRegionRuntime.rootCause(throwable));
        } finally {
            if (paused) resumePathCondition(active, api);
            if (replayContradicted) {
                // Release the engine now: nothing publishable can follow.
                ConcolicRegionRuntime.finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    /**
     * One decision's VM event read against its window, and whether the VM
     * attests it (a refusal is already named).  {@code baseline} is the raw
     * path-condition size before this decision.
     */
    private static final class Capture {
        private final int baseline;
        /** The event names one contiguous condition range. */
        private final boolean exactRange;
        private final PathConditionWindow conditions;
        private final VmBranchAttestation.Attestation attestation;

        private Capture(int baseline, boolean exactRange,
                        PathConditionWindow conditions,
                        VmBranchAttestation.Attestation attestation) {
            this.baseline = baseline;
            this.exactRange = exactRange;
            this.conditions = conditions;
            this.attestation = attestation;
        }
    }

    /** Reads and attests one decision's VM event, binary or multiway. */
    private static Capture capture(
            ActiveRegion active, ConcolicVmBroker api, String siteId,
            String expression, boolean outcome, int occurrence,
            SwitchExpectation expected, long vmEventId) throws Exception {
        int baseline = active.lastPathConditionSize;
        // One read of the event stream, used by both questions asked of it:
        // the events since the previous read (VM f10), this decision's
        // among them.  The whole frame each time was quadratic in its
        // decisions (hdfs-17960's NameNode restart decides 1561).
        JsonElement events = ConcolicRegionRuntime.parseJson(
                api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        PathConditionWindow conditions = PathConditionWindow.forEvent(
                active.expressionStore, api, eventConditionIndices);
        VmBranchAttestation.Attestation attestation =
                VmBranchAttestation.attest(active, siteId, expression,
                        outcome, vmEventId, occurrence, conditions,
                        noVmCondition ? 0 : baseline, expected, events);
        if (!attestation.valid) {
            VmBranchAttestation.noteRefused(siteId, occurrence, attestation,
                    windowOutcome(eventConditionIndices, conditions));
        }
        return new Capture(baseline,
                contiguousConditionIndices(eventConditionIndices),
                conditions, attestation);
    }

    /**
     * Captures one exact binary decision; false only where the VM emitted no
     * branch event, so no row exists beside which a target reach could be
     * stated.  Not "attested enough to reach": a concrete decision at the
     * target still reaches.
     */
    private static boolean recordBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        if (vmEventId <= 0L) {
            // The VM emitted no symbolic branch event.
            return false;
        }
        Capture read = capture(active, api, SiteId.render(method, unitIndex),
                expression, observedOutcome, occurrence, null, vmEventId);
        PathConditionWindow conditions = read.conditions;
        VmBranchAttestation.Attestation vmAttestation = read.attestation;
        int baseline = read.baseline;
        // An exact conditionless event contributes no branch guard, and a
        // non-contiguous one names no exact range: both leave the window
        // empty and the raw size at the baseline.
        int rawPathConditionSize = read.exactRange ? conditions.size()
                : baseline;
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        // Exact VM ownership is one condition for an IfStmt.
        int mappingBaseline = conditionIndex >= 0
                ? conditionIndex : baseline;
        int mappingLimit = conditionIndex >= 0
                ? conditionIndex + 1 : rawPathConditionSize;
        // A row with no term of its own states the arm the jump took; a row
        // that publishes a term states whether THAT term held, and the term
        // is added below (CONTRACT-SPEC §2.2).
        JsonObject mapping = decisionRow(method, unitIndex, occurrence,
                vmEventId, observedOutcome, mappingBaseline, mappingLimit);
        if (conditionIndex >= 0) {
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition =
                    VmBranchAttestation.semanticCondition(
                            expression, observedOutcome, condition);
            mapping.add("witness", BranchWitness.immutablePredicate(
                    semanticCondition).toImmutableJsonView());
            // The term is the predicate under which the JUMP is taken,
            // fixed across replays and arms (CONTRACT-SPEC §2.2: a
            // consumer forms `outcome ? term : (not term)`).  The VM
            // states the SATISFIED form, which moves the arm into the
            // term and hides a flip; so the fallen-through arm's term is
            // the negation of the VM's constraint -- a respelling only.
            JsonElement written = observedOutcome ? condition
                    : VmBranchAttestation.negated(condition);
            if (written != null && written.isJsonObject()) {
                mapping.add("siteCondition", written);
            }
        }
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
        // A row was published: the site executed.  Whether it states a
        // site predicate is the row's business.
        return true;
    }

    private static boolean recordSwitchBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        Capture read = capture(active, api, SiteId.render(method, unitIndex),
                expression, expected.caseArm(), occurrence, expected,
                vmEventId);
        int baseline = read.baseline;
        List<Integer> conditionIndices = read.attestation.valid
                ? read.attestation.conditionIndices
                : Collections.<Integer>emptyList();
        int mappingBaseline = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(0);
        int mappingLimit = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(
                conditionIndices.size() - 1) + 1;
        active.branchMappings.add(decisionRow(method, unitIndex, occurrence,
                vmEventId, expected.caseArm(), mappingBaseline, mappingLimit));
        for (Integer conditionIndex : conditionIndices) {
            JsonObject predicate = decisionRow(method, unitIndex, occurrence,
                    vmEventId, null, mappingBaseline, mappingLimit);
            predicate.add("witness",
                    BranchWitness.immutablePredicate(
                            read.conditions.get(conditionIndex))
                            .toImmutableJsonView());
            active.branchMappings.add(predicate);
        }
        active.lastPathConditionSize = Math.max(
                active.lastPathConditionSize, mappingLimit);
        return read.attestation.valid;
    }

    /**
     * Which answer the condition-window read gave, by name.  A conditionless
     * event is concrete and publishable; a refused range names conditions
     * this replay could not read, so the attestation refuses the arm with
     * this outcome beside it ({@link VmBranchAttestation#noteRefused}).
     * Refused exactly when the event's contiguous range ends past the window.
     */
    private static String windowOutcome(List<Integer> eventConditionIndices,
                                        PathConditionWindow conditions) {
        if (eventConditionIndices == null) return "EVENT_NOT_UNIQUE";
        if (eventConditionIndices.isEmpty()) return "CONDITIONLESS_EVENT";
        if (!contiguousConditionIndices(eventConditionIndices)) {
            return "EXACT_RANGE_UNAVAILABLE";
        }
        int last = eventConditionIndices.get(
                eventConditionIndices.size() - 1);
        return conditions.size() <= last
                ? "EXACT_RANGE_REFUSED" : "EXACT_EVENT_RANGE";
    }

    /**
     * One decision row, the DecisionRow is built from: its site, arm
     * ({@code null} on a switch's predicate row) and the raw path-condition
     * range {@code [baseline, limit)} it owns.
     *
     * <p>{@code vmEventId} is the VM's session-global event number for the
     * decision (the counter behind {@code fieldVersionId} and {@code
     * readEventId}), the only monotone per-replay clock the row carries: it
     * orders decisions against the anchor, other activations and the write
     * log, within one {@code sessionId}.  Published only when the VM
     * assigned one; a zero would order the decision ahead of everything.</p>
     */
    static JsonObject decisionRow(String method, int unitIndex,
                                  int occurrence, long vmEventId,
                                  Boolean outcome, int baseline, int limit) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", SiteId.render(method, unitIndex));
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        if (vmEventId > 0L) mapping.addProperty("vmEventId", vmEventId);
        if (outcome != null) mapping.addProperty("outcome", outcome);
        mapping.addProperty("rawPathConditionSize", limit);
        mapping.addProperty("rawPathConditionBaseline", baseline);
        return mapping;
    }

    /**
     * Restores the path condition one branch observation paused.  A lost
     * resume is BLOCKING: every later decision of this activation records
     * nothing, so the published path condition is a prefix nobody stated.
     */
    private static void resumePathCondition(ActiveRegion active,
                                            ConcolicVmBroker api) {
        try {
            api.resumePathCondition();
        } catch (Throwable throwable) {
            RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.BLOCKING,
                    firstNonBlank(active.address(),
                            Long.toString(active.token)),
                    "the path condition this branch observation paused was"
                            + " not resumed, so every decision this"
                            + " activation takes afterwards is unrecorded: "
                            + ConcolicRegionRuntime.rootCause(throwable));
        }
    }

    static final class SwitchExpectation {
        final String branchKind;
        final List<Integer> caseKeys;
        final int observedSuccessorIndex;

        SwitchExpectation(String branchKind, List<Integer> caseKeys,
                                  int observedSuccessorIndex) {
            this.branchKind = branchKind;
            this.caseKeys = Collections.unmodifiableList(
                    new ArrayList<>(caseKeys));
            this.observedSuccessorIndex = observedSuccessorIndex;
        }

        static SwitchExpectation parse(
                String branchKind, String encodedCaseKeys,
                int observedSuccessorIndex) {
            String kind = safe(branchKind);
            if (!("TABLE_SWITCH".equals(kind)
                    || "LOOKUP_SWITCH".equals(kind))) {
                throw new IllegalArgumentException(
                        "unsupported branch kind " + kind);
            }
            List<Integer> keys = new ArrayList<>();
            String encoded = safe(encodedCaseKeys);
            if (!encoded.isEmpty()) {
                for (String token : encoded.split(",", -1)) {
                    if (!token.matches("-?(?:0|[1-9][0-9]*)")) {
                        throw new IllegalArgumentException(
                                "malformed switch key " + token);
                    }
                    try {
                        keys.add(Integer.parseInt(token));
                    } catch (NumberFormatException malformed) {
                        throw new IllegalArgumentException(
                                "switch key outside int domain " + token,
                                malformed);
                    }
                }
            }
            if (keys.isEmpty() || observedSuccessorIndex < 0
                    || observedSuccessorIndex > keys.size()) {
                throw new IllegalArgumentException(
                        "successor " + observedSuccessorIndex
                                + " outside switch domain [0,"
                                + keys.size() + "]");
            }
            if ("TABLE_SWITCH".equals(kind)) {
                for (int index = 1; index < keys.size(); index++) {
                    if ((long) keys.get(index - 1) + 1L
                            != (long) keys.get(index)) {
                        throw new IllegalArgumentException(
                                "tableswitch keys are not dense/ordered");
                    }
                }
            } else {
                Set<Integer> distinct = new LinkedHashSet<>(keys);
                if (distinct.size() != keys.size()) {
                    throw new IllegalArgumentException(
                            "lookupswitch keys are not unique");
                }
            }
            return new SwitchExpectation(kind, keys,
                    observedSuccessorIndex);
        }

        boolean caseArm() {
            return observedSuccessorIndex < caseKeys.size();
        }
    }

    /**
     * One decision an instrumented site made: a binary outcome, or the
     * successor a multiway switch selected out of its static case-key
     * domain (carried as its {@link SwitchExpectation}).
     */
    static final class BranchDecision {
        final boolean outcome;
        private final SwitchExpectation expected;

        private BranchDecision(boolean outcome, SwitchExpectation expected) {
            this.outcome = outcome;
            this.expected = expected;
        }

        static BranchDecision binary(boolean outcome) {
            return new BranchDecision(outcome, null);
        }

        static BranchDecision multiway(SwitchExpectation expected) {
            return new BranchDecision(expected.caseArm(), expected);
        }

        /** The source-level outcome this decision took. */
        boolean outcome() { return outcome; }

        /** This decision's exact capture while the VM window is open. */
        boolean recordPaused(
                ActiveRegion active, ConcolicVmBroker api, String method,
                int unitIndex, String expression, int occurrence,
                long vmEventId) throws Exception {
            return expected == null
                    ? recordBranchPaused(active, api, method, unitIndex,
                    expression, occurrence, outcome, vmEventId)
                    : recordSwitchBranchPaused(active, api, method, unitIndex,
                    expression, occurrence, expected, vmEventId);
        }

        /**
         * Whether a bounded-loop permutation may address the planned target
         * occurrence from another one: yes for a binary branch (the solver
         * flips it), no for a switch successor (a path assumption).
         */
        boolean addressesPermutedTargetOccurrence() {
            return expected == null;
        }

    }

    static final class PreparedBranch {
        final long handle;
        private final String method;
        private final int unitIndex;
        private final String expression;
        final int occurrence;

        PreparedBranch(long handle, String method, int unitIndex,
                               String expression, int occurrence) {
            this.handle = handle;
            this.method = safe(method);
            this.unitIndex = unitIndex;
            this.expression = safe(expression);
            this.occurrence = occurrence;
        }

        boolean matches(String actualMethod, int actualUnitIndex,
                                String actualExpression) {
            return method.equals(safe(actualMethod))
                    && unitIndex == actualUnitIndex
                    && expression.equals(safe(actualExpression));
        }
    }
}
