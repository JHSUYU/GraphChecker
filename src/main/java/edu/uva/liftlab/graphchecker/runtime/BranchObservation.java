package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.plan.BranchWitness;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.contiguousConditionIndices;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.vmEventConditionIndices;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

final class BranchObservation {
    private BranchObservation() {
    }

    static long prepare(String method, int unitIndex,
                        String expression) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || !active.pathRecordingStarted) return 0L;
        try {
            PreparedBranch prepared = active.prepareBranch(method, unitIndex,
                    expression, ConcolicRegionRuntime.recordsHere(active));
            if (prepared == null) return 0L;
            String refused = ForcedArms.direct(active, method, unitIndex);
            if (!refused.isEmpty() && FocusedReplay.decideForced(refused)) {
                ConcolicResultPublisher.concludeAtRefusal();
            }
            return prepared.handle;
        } catch (Throwable throwable) {
            return 0L;
        }
    }

    static void observeSwitch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        SwitchExpectation expected;
        try {
            expected = SwitchExpectation.parse(branchKind, encodedCaseKeys,
                    observedSuccessorIndex);
        } catch (IllegalArgumentException malformed) {
            ActiveRegion unattested = ConcolicRegionRuntime.activeRegion();
            RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                    SiteId.render(method, unitIndex),
                    "the weave states switch domain kind=" + nonNull(branchKind)
                            + " keys=[" + nonNull(encodedCaseKeys)
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

    static void observe(
            BranchDecision decision, long preparedHandle, long vmEventId,
            String method, int unitIndex, String expression) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null) return;
        String branchSite = SiteId.render(method, unitIndex);
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
            return;
        }
        if (vmEventId <= 0L && prepared.recording) {
            RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                    branchSite, "the VM gave this branch no event although"
                            + " its occurrence records here: its frame does"
                            + " not track (pushed while recording was paused)"
                            + " or recording is paused around it, so it"
                            + " states no arm, and a door here decides"
                            + " nothing");
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
            active.observeReplayDecision(branchSite, prepared.occurrence,
                    decision);
            replayContradicted = active.replayPrefixContradicted();
            boolean permuted = decision.addressesPermutedTargetOccurrence()
                    && FocusedReplay.focused(active.d3Address);
            if (ConcolicRegionRuntime.statesTargetReach(recorded, permuted,
                    active.activation.targetTest(branchSite),
                    active.activation.targetBranchOccurrence,
                    prepared.occurrence)) {
                int reached = permuted
                        ? active.activation.targetBranchOccurrence
                        : prepared.occurrence;
                if (ForcedArms.reachedTarget(active, branchSite, reached,
                        decision.outcome())) {
                    active.recordTargetReach(branchSite, reached,
                            decision.outcome(), vmEventId);
                }
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
                ConcolicRegionRuntime.finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    private static final class Capture {
        private final int baseline;
        private final boolean exactRange;
        private final PathConditionWindow conditions;
        private final VmBranchAttestation.Attestation attestation;
        private final JsonObject event;

        private Capture(int baseline, boolean exactRange,
                        PathConditionWindow conditions,
                        VmBranchAttestation.Attestation attestation,
                        JsonObject event) {
            this.baseline = baseline;
            this.exactRange = exactRange;
            this.conditions = conditions;
            this.attestation = attestation;
            this.event = event;
        }
    }

    private static BranchWitness witness(ActiveRegion active,
                                         JsonElement condition) {
        Map<JsonElement, JsonElement> views = VIEWS.computeIfAbsent(
                active.expressionStore,
                store -> new IdentityHashMap<JsonElement, JsonElement>());
        synchronized (views) {
            if (views.size() >= VIEWS_HELD) views.clear();
            return BranchWitness.immutablePredicate(condition, views);
        }
    }

    private static final Map<VmExpressionTable.Store,
            Map<JsonElement, JsonElement>> VIEWS =
            Collections.synchronizedMap(new WeakHashMap<VmExpressionTable.Store,
                    Map<JsonElement, JsonElement>>());
    private static final int VIEWS_HELD = 1 << 16;

    private static Capture capture(
            ActiveRegion active, ConcolicVmBroker api, String siteId,
            String expression, boolean outcome, int occurrence,
            SwitchExpectation expected, long vmEventId) throws Exception {
        int baseline = active.lastPathConditionSize;
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
        List<JsonObject> event = events.isJsonObject()
                ? PathConditionWindow.eventsNumbered(events.getAsJsonObject(),
                vmEventId) : Collections.<JsonObject>emptyList();
        return new Capture(baseline,
                contiguousConditionIndices(eventConditionIndices),
                conditions, attestation,
                event.size() == 1 ? event.get(0) : null);
    }

    private static boolean recordBranchPaused(
            ActiveRegion active, ConcolicVmBroker api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        if (vmEventId <= 0L) {
            return false;
        }
        Capture read = capture(active, api, SiteId.render(method, unitIndex),
                expression, observedOutcome, occurrence, null, vmEventId);
        PathConditionWindow conditions = read.conditions;
        VmBranchAttestation.Attestation vmAttestation = read.attestation;
        int baseline = read.baseline;
        int rawPathConditionSize = read.exactRange ? conditions.size()
                : baseline;
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        int mappingBaseline = conditionIndex >= 0
                ? conditionIndex : baseline;
        int mappingLimit = conditionIndex >= 0
                ? conditionIndex + 1 : rawPathConditionSize;
        JsonObject mapping = decisionRow(method, unitIndex, occurrence,
                vmEventId, observedOutcome, mappingBaseline, mappingLimit);
        ForcedArms.mark(active, mapping, read.event);
        ForcedArms.statesCaller(active, mapping);
        if (conditionIndex >= 0) {
            active.termedDecisions++;
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition =
                    VmBranchAttestation.semanticCondition(
                            expression, observedOutcome, condition);
            mapping.add("witness", witness(active, semanticCondition)
                    .toImmutableJsonView());
            JsonElement written = observedOutcome ? condition
                    : VmBranchAttestation.negated(condition);
            if (written != null && written.isJsonObject()) {
                mapping.add("siteCondition", written);
            }
        }
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
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
        if (!conditionIndices.isEmpty()) active.termedDecisions++;
        for (Integer conditionIndex : conditionIndices) {
            JsonObject predicate = decisionRow(method, unitIndex, occurrence,
                    vmEventId, null, mappingBaseline, mappingLimit);
            predicate.add("witness", witness(active,
                    read.conditions.get(conditionIndex))
                    .toImmutableJsonView());
            active.branchMappings.add(predicate);
        }
        active.lastPathConditionSize = Math.max(
                active.lastPathConditionSize, mappingLimit);
        return read.attestation.valid;
    }

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

    static JsonObject decisionRow(String method, int unitIndex,
                                  int occurrence, long vmEventId,
                                  Boolean outcome, int baseline, int limit) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", SiteId.render(method, unitIndex));
        mapping.addProperty("method", nonNull(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        if (vmEventId > 0L) mapping.addProperty("vmEventId", vmEventId);
        if (outcome != null) mapping.addProperty("outcome", outcome);
        mapping.addProperty("rawPathConditionSize", limit);
        mapping.addProperty("rawPathConditionBaseline", baseline);
        return mapping;
    }

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
            String kind = nonNull(branchKind);
            if (!("TABLE_SWITCH".equals(kind)
                    || "LOOKUP_SWITCH".equals(kind))) {
                throw new IllegalArgumentException(
                        "unsupported branch kind " + kind);
            }
            List<Integer> keys = new ArrayList<>();
            String encoded = nonNull(encodedCaseKeys);
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

        boolean outcome() { return outcome; }

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
        final boolean recording;

        PreparedBranch(long handle, String method, int unitIndex,
                               String expression, int occurrence,
                               boolean recording) {
            this.handle = handle;
            this.method = nonNull(method);
            this.unitIndex = unitIndex;
            this.expression = nonNull(expression);
            this.occurrence = occurrence;
            this.recording = recording;
        }

        boolean matches(String actualMethod, int actualUnitIndex,
                                String actualExpression) {
            return method.equals(nonNull(actualMethod))
                    && unitIndex == actualUnitIndex
                    && expression.equals(nonNull(actualExpression));
        }
    }
}
