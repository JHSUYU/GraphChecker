package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.contiguousConditionIndices;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.vmEventConditionIndices;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.plan.BranchWitness;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.ActiveRegion;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * R3: one decision of one instrumented site, as a published row.
 *
 * <p>The stages of one observation -- reserve the VM event before the
 * original conditional ({@link #prepare}), capture the decision against the
 * open path-condition window, state it to the one replay-prefix matcher,
 * and address the target reach it may complete ({@link #observe}) -- ask
 * the same questions of a binary branch and of a multiway switch, and are
 * written once against {@link BranchDecision}.</p>
 *
 * <p>The workload's own value is the hook's to return: nothing observed
 * here may change it, which is why {@link #observe} reports nothing back
 * and {@link #observeSwitch} returns the successor it was handed.</p>
 *
 * <p>Whether a captured decision may carry a term is not decided here:
 * {@link VmBranchAttestation} answers that, and a refusal is its row.</p>
 *
 * <p>Needs back from {@link ConcolicRegionRuntime}: the innermost
 * activation, the activation terminal ({@code finish}), {@code
 * statesTargetReach} (the anchor rule, which a test asserts against by
 * name there), {@code parseJson}, and the per-activation decision state
 * ActiveRegion holds -- branchMappings, preparedBranches,
 * lastPathConditionSize.</p>
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
    static int observeSwitch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        SwitchExpectation expected;
        try {
            expected = SwitchExpectation.parse(branchKind, encodedCaseKeys,
                    observedSuccessorIndex);
        } catch (IllegalArgumentException malformed) {
            // The weave handed static case keys this decoder refuses, so
            // the decision is not observed at all.  Not stated here: no
            // kind of the closed GapKind set names a plan/weave
            // disagreement about a switch's static domain, and both kept
            // corpora publish 0 switch rows, so there is no firing to
            // measure a choice against.  Reported for the planner instead.
            return observedSuccessorIndex;
        }
        observe(BranchDecision.multiway(expected), preparedHandle,
                vmEventId, method, unitIndex, expression);
        return observedSuccessorIndex;
    }

    /**
     * Observes one decision of either kind at one instrumented site.
     *
     * <p>The workload's own value is the hook's to return: nothing observed
     * here may change it, so this reports nothing back.</p>
     */
    static void observe(
            BranchDecision decision, long preparedHandle, long vmEventId,
            String method, int unitIndex, String expression) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null) return;
        String branchSite = SiteId.render(method, unitIndex);
        // A decision at a woven site is recorded, full stop.  The frozen
        // plan used to have to declare the site as well -- it carried the
        // branches an offline classification had selected, and every
        // decision at any other woven site was dropped here, so the
        // recorded decision set was a function of that classification rather
        // than of what ran.  With the selection gone, the arm below that
        // handled "woven but not declared" is unreachable and goes with it.
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
            // No unverified VM event may be rebound heuristically on a JDK
            // that advertised the exact API.
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
            // Advances the replay contract and records a prefix mismatch;
            // whether this decision consumed the contract's source event
            // says nothing about whether the target site ran.
            active.observeReplayDecision(branchSite, prepared.occurrence,
                    decision);
            replayContradicted = active.replayPrefixContradicted();
            // A bounded loop may have run the planned target occurrence at
            // another one.  targetReach is the planner's semantic source
            // address; the branch mapping beside it retains the actual
            // occurrence and symbolic support which matched that source.
            boolean permuted = decision.addressesPermutedTargetOccurrence()
                    && edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .focused(active.d3Address);
            if (ConcolicRegionRuntime.statesTargetReach(recorded, permuted,
                    active.activation.targetBranchSite,
                    active.activation.targetBranchOccurrence,
                    branchSite, prepared.occurrence)) {
                // Reaching the target is the site having executed, and
                // nothing else -- including whether the predicate there was
                // symbolic.  It was gated on a solver witness, so a target
                // branch that compares two concrete values published no
                // reach at all: on hdfs-17960 the fatal branch is
                // "i != sm.getNumSnapshots()" over two concrete ints, which
                // the root reaches by control dependence (the flip skips a
                // decrement), and the same activation then recorded the
                // decision AND was named as never having decided it.  The
                // anchor evidence is the fatal predicate when there is one
                // and the concrete outcome when there is not; which of the
                // two it is belongs in the branch row beside it, where the
                // composer reads it to decide a propagation cut.
                //
                // The replay contract decides whether this
                // activation followed the prefix it was asked to follow --
                // a different question, and one whose answer is "no" at the
                // target on every flip replay whose source branch is
                // somewhere else, because the contract names no event here
                // to consume.  Gating on it published the target event only
                // from the recording, so every flip's disjunct was lost
                // before composition ever saw it.  The composition wants
                // them all: a flip that leaves the predicate false is the
                // disjunct that contributes nothing, and a flip that
                // diverges is still evidence that the branch was tried.
                //
                // Reaching the target is also a fact of this case, never a
                // reason to stop recording it: the RPC, state and throw
                // effects the occurrence still owes all happen after this
                // branch.
                active.recordTargetReach(
                        permuted ? active.activation.targetBranchSite
                                : branchSite,
                        permuted ? active.activation.targetBranchOccurrence
                                : prepared.occurrence,
                        decision.outcome(), vmEventId);
            }
        } catch (Throwable throwable) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNATTESTED_ARM,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    branchSite + "#" + prepared.occurrence,
                    "this decision was not captured, so it states neither an"
                            + " arm nor the target reach that would have"
                            + " stood beside it: " + ConcolicRegionRuntime.rootCause(throwable));
        } finally {
            if (paused) resumePathCondition(active, api);
            if (replayContradicted) {
                // Release the engine here rather than at this activation's own
                // return: the branch that just executed already decided that
                // nothing publishable can follow.
                ConcolicRegionRuntime.finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    /**
     * Captures one exact binary decision; false only where the VM emitted no
     * branch event to capture, so there is no row beside which a target
     * reach could be stated.  It used to mean "attested well enough to
     * address a target reach", which read the presence of a path condition as
     * permission to publish the anchor -- so an activation that decided the
     * target site concretely published a branch row and no reach.
     */
    private static boolean recordBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        if (vmEventId <= 0L) {
            // The VM emitted no symbolic branch event.
            return false;
        }
        String siteId = SiteId.render(method, unitIndex);
        int baseline = active.lastPathConditionSize;
        // One read of the event stream, used by both questions asked of it.
        JsonElement events = ConcolicRegionRuntime.parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        // An exact conditionless event contributes no branch guard, and a
        // non-contiguous one names no exact range: both leave the window
        // empty and the raw size at the baseline.
        boolean exactRange = !noVmCondition
                && contiguousConditionIndices(eventConditionIndices);
        PathConditionWindow.Read read = PathConditionWindow.forEvent(
                active.expressionStore, api, eventConditionIndices);
        PathConditionWindow conditions = read.conditions;
        String windowOutcome = windowOutcome(eventConditionIndices,
                conditions);
        int rawPathConditionSize = exactRange ? conditions.size() : baseline;
        int attestationBaseline = noVmCondition ? 0 : baseline;
        VmBranchAttestation.Attestation vmAttestation =
                VmBranchAttestation.attest(api, active, siteId, expression,
                        observedOutcome, vmEventId, occurrence, conditions,
                        attestationBaseline, null, events);
        if (!vmAttestation.valid) {
            VmBranchAttestation.noteRefused(siteId, occurrence,
                    vmAttestation, windowOutcome);
        }
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence,
                vmEventId);
        // A row with no term of its own states the arm the jump took; a row
        // that publishes a term states whether THAT term held, and the term
        // is added below (CONTRACT v2.3 sec 1.3).
        mapping.addProperty("outcome", observedOutcome);
        // Exact VM ownership is one condition for an IfStmt.
        int mappingBaseline = conditionIndex >= 0
                ? conditionIndex : baseline;
        int mappingLimit = conditionIndex >= 0
                ? conditionIndex + 1 : rawPathConditionSize;
        mapping.addProperty("rawPathConditionSize", mappingLimit);
        mapping.addProperty("rawPathConditionBaseline", mappingBaseline);
        if (conditionIndex >= 0) {
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition =
                    VmBranchAttestation.semanticCondition(
                            expression, observedOutcome, condition);
            if (vmAttestation.valid) {
                mapping.add("witness", BranchWitness.immutablePredicate(
                        semanticCondition).toImmutableJsonView());
                // The predicate under which the JUMP is taken, which is the
                // one thing about this site that does not move between
                // replays or between arms, and the arm beside it
                // (CONTRACT v2.3 sec 1.3: a consumer forms
                // `outcome ? term : (not term)`).
                //
                // The VM publishes its constraint in the form the run
                // SATISFIED: `marker != false` where the source reads
                // `if marker == 0 goto` and the jump fell through, and
                // `marker == false` in the replay that took it.  Publishing
                // the satisfied form as the term moves the arm INTO the
                // term -- the term then differs between the two runs of one
                // site while `outcome` is true in both, so a flip cannot be
                // observed by comparing outcomes at all (P2f').  So the
                // taken arm's constraint is the term as it stands, and the
                // fallen-through arm's is its negation, which is a spelling
                // operation on the VM's own constraint and re-evaluates
                // nothing.
                JsonElement written = observedOutcome ? condition
                        : VmBranchAttestation.negated(condition);
                if (written != null && written.isJsonObject()) {
                    mapping.add("siteCondition", written);
                }
            }
        }
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
        // A row was published for this decision: the site executed and the
        // outcome beside it is this execution's own.  Whether it carried a
        // path condition is whether the row states a site predicate, which
        // is what the decision row publishes.
        return true;
    }

    private static boolean recordSwitchBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        String siteId = SiteId.render(method, unitIndex);
        int baseline = active.lastPathConditionSize;
        JsonElement events = ConcolicRegionRuntime.parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        PathConditionWindow.Read read = PathConditionWindow.forEvent(
                active.expressionStore, api, eventConditionIndices);
        PathConditionWindow conditions = read.conditions;
        String windowOutcome = windowOutcome(eventConditionIndices,
                conditions);
        VmBranchAttestation.Attestation attestation =
                VmBranchAttestation.attest(api, active, siteId, expression,
                        expected.caseArm(), vmEventId, occurrence, conditions,
                        noVmCondition ? 0 : baseline, expected, events);
        List<Integer> conditionIndices = attestation.valid
                ? attestation.conditionIndices
                : Collections.<Integer>emptyList();
        int mappingBaseline = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(0);
        int mappingLimit = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(
                conditionIndices.size() - 1) + 1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence,
                vmEventId);
        mapping.addProperty("outcome", expected.caseArm());
        mapping.addProperty("rawPathConditionSize", mappingLimit);
        mapping.addProperty("rawPathConditionBaseline", mappingBaseline);
        if (!attestation.valid) {
            VmBranchAttestation.noteRefused(siteId, occurrence, attestation,
                    windowOutcome);
        }
        active.branchMappings.add(mapping);
        if (attestation.valid) {
            for (Integer conditionIndex : conditionIndices) {
                JsonObject predicate = branchMapping(method, unitIndex,
                        occurrence, vmEventId);
                predicate.addProperty("rawPathConditionSize", mappingLimit);
                predicate.addProperty("rawPathConditionBaseline",
                        mappingBaseline);
                predicate.add("witness",
                        BranchWitness.immutablePredicate(
                                conditions.get(conditionIndex))
                                .toImmutableJsonView());
                active.branchMappings.add(predicate);
            }
        }
        active.lastPathConditionSize = Math.max(
                active.lastPathConditionSize, mappingLimit);
        return attestation.valid;
    }

    /**
     * Which answer the condition-window read gave, by name.
     *
     * <p>{@code PathConditionWindow.Read} used to carry this as a {@code
     * source} field nothing read, so "the VM refused the exact range" and
     * "this event names no condition at all" arrived here as one empty
     * window.  They are not one fact.  A conditionless event contributes no
     * branch guard and its decision is concrete and publishable; a refused
     * range means the event names conditions THIS replay could not read, so
     * the arm the row states has no term and the attestation refuses it --
     * with this outcome beside its own sentence
     * ({@link VmBranchAttestation#noteRefused}).</p>
     *
     * <p>Computed from what the event itself said, so the reader owns the
     * distinction: the window is refused exactly when the event named a
     * contiguous range whose last index the window it came back with cannot
     * hold.</p>
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
     * One published decision row.
     *
     * <p>{@code vmEventId} is the VM's own event sequence number for the
     * decision -- the id the native marker returned immediately before the
     * workload's branch.  It is the only monotone per-replay clock the
     * publication carries: {@code unitIndex} and the path-condition indices
     * are positions inside a method and inside one condition window, and
     * {@code startedAtMillis} is telemetry.  A composer needs this to say
     * which decisions were taken before an anchor and in what order two
     * activations' decisions interleave.</p>
     *
     * <p>Nothing here reads the id's scale.  It was a per-ThreadContext
     * counter -- 1, 2, 3 per thread, restarting for every context -- and the
     * VM now draws it from the session-global event counter, the same one
     * behind {@code fieldVersionId}, {@code readEventId} and
     * {@code regionEnterEventId}.  The values stop being small and dense and
     * start interleaving with the write log's, which is the point: "the
     * latest write whose event precedes this decision" becomes a valid
     * comparison, within one {@code sessionId}.  This publication is
     * unchanged either way, and the only other runtime use of the id is the
     * exact-event lookup in {@code PathConditionWindow}, which matches on
     * equality and requires the id to be unique among the events read -- true
     * on both scales.</p>
     *
     * <p>It is published only when the VM assigned one.  A decision recorded
     * with the symbolic gate closed has no VM event, and stating a zero there
     * would order it ahead of everything the VM did record.</p>
     */
    static JsonObject branchMapping(
            String method, int unitIndex, int occurrence, long vmEventId) {
        // The row the DecisionRow is built from states the site, the arm
        // and the predicate as written; the witness objects beside it are
        // the old publication's shapes and nothing reads them now.
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", SiteId.render(method, unitIndex));
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        if (vmEventId > 0L) mapping.addProperty("vmEventId", vmEventId);
        return mapping;
    }

    /**
     * Restores the path condition one branch observation paused.
     *
     * <p>BLOCKING when the resume is lost, and it has to be: the workload's
     * own observation stays muted for the rest of this activation, so every
     * decision after this point records nothing and the path condition the
     * session publishes is a prefix nobody stated.  The loop-accounting
     * sibling treats the same loss as a cut
     * ({@code BOUND_HOOK_RESUME_FAILURE}); here the activation keeps
     * running and the row says its arms cannot be trusted.</p>
     */
    private static void resumePathCondition(ActiveRegion active,
                                            ConcolicVmBroker api) {
        try {
            api.resumePathCondition();
        } catch (Throwable throwable) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNATTESTED_ARM,
                    edu.uva.liftlab.graphchecker.contract.GapClass.BLOCKING,
                    firstNonBlank(active.occurrenceId(),
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
     * One decision an instrumented site made: the outcome a binary branch
     * took, or the successor a multiway switch selected out of its static
     * case-key domain.
     *
     * <p>The stages of one observation -- record the decision behind a closed
     * symbolic gate, record it at a replay-invocation boundary, capture it
     * against the open VM path-condition window, observe it against the
     * recorded replay prefix, and address the target reach it may complete --
     * ask the same questions of both kinds, and are written once against
     * this.  A switch carries its {@link SwitchExpectation}; a binary branch
     * carries none.</p>
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
         * occurrence from a different one.  A binary branch is the decision
         * the solver flips, so it may; a multiway successor is retained as a
         * path assumption, so it addresses only the planned occurrence.
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
