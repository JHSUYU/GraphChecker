package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.plan.ForcingTable;
import edu.uva.liftlab.graphchecker.plan.SiteId;

import java.util.List;
import java.util.Map;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

/**
 * THE FORCED REPLAY (PIPELINE §7.10): in a FORCE run, the declared
 * occurrence's branches between its entry and the marked throw take the
 * arms that lead to the throw ({@code plan.ForcingTable}, the declared
 * task's {@code targetBranch.force}), whatever their operands decide.
 *
 * <p>Armed in ONE activation, the declared occurrence's
 * ({@link FocusedReplay#declaredTarget}), on its thread, from its entry until
 * the target decision is forced: every evaluation of a table site there is
 * forced (a loop's turns, a recursion's calls -- each forced arm reaches the
 * throw by post-dominance, so the first that gets there ends it), a decider
 * only in a call of its helper from the method that table row names
 * ({@code via}); a nested planned region, another occurrence or thread,
 * never.  Java decides each branch at the woven prefix
 * ({@link BranchObservation#prepare}), the VM forces it at the bytecode
 * ({@code System.forceNextConcolicBranch}) and its event states the
 * concrete answer it overrode, so each decision row states it
 * ({@code DecisionRow#forced}).</p>
 *
 * <p>The first decision forced against its concrete arm opens the forced
 * world ({@link #forcedFrom}); the target row, reached there, states the
 * forced path condition from that decision on as its phi
 * ({@code RowPublication#target}, {@code TargetRow#forced}), and the run
 * ends once it is published ({@code ConcolicResultPublisher}).  An
 * occurrence that closes first -- an exception the forced world threw, a
 * branch no marker owned -- decides the run FORCE_DIVERGED, named with the
 * first exception and its frame; its session is withdrawn.</p>
 */
final class ForcedArms {
    /** The verdict detail of a run that reached its target forced. */
    static final String FORCED_TARGET = "FORCED_TARGET";
    /** The verdict detail of one that did not. */
    static final String FORCE_DIVERGED = "FORCE_DIVERGED";
    /** A decision mapping's mark: forced against its concrete arm. */
    static final String AGAINST = "forcedAgainst";

    private static final Object LOCK = new Object();
    /** The armed activation's token; 0 while none is. */
    private static volatile long armed;
    /** Whether an activation was ever armed. */
    private static boolean entered;
    /** The first decision of the armed activation forced against its
     *  concrete arm (a VM event id), 0 before one. */
    private static long forcedFrom;
    /** The target decision forced, {@code site#ordinal}, or "". */
    private static String target = "";
    /** How the armed activation ended once its target was forced. */
    private static String ended = "";
    /** The first exception that unwound a frame of the forced world. */
    private static String unwound = "";
    /** Why the run is FORCE_DIVERGED, or "". */
    private static String diverged = "";

    private ForcedArms() {
    }

    /** Arms {@code active} when this is a FORCE run and it is the declared
     *  occurrence; it then records from its entry. */
    static void arm(ActiveRegion active) {
        if (!FocusedReplay.forcing() || active.d3Address == null
                || !FocusedReplay.declaredTarget(active.d3Address)
                || active.activation.forcedArms.isEmpty()) {
            return;
        }
        synchronized (LOCK) {
            if (entered) return;
            entered = true;
            armed = active.token;
        }
        active.pathRecordingStarted = true;
    }

    /**
     * Asks the VM to force the branch the woven prefix marks next, when the
     * armed activation reaches a site of its table; called just before the
     * marker ({@link BranchObservation#prepare}).
     */
    static void direct(ActiveRegion active, String method, int unitIndex) {
        if (armed == 0L || active.token != armed) return;
        Map<String, ForcingTable.Arm> table = active.activation.forcedArms;
        ForcingTable.Arm arm = table.get(SiteId.render(method, unitIndex));
        if (arm == null || !arm.via.isEmpty() && !JvmNames.stable(arm.via)
                .equals(Identity.callerFrame())) {
            return;
        }
        try {
            ConcolicVmBroker.engine().forceNextBranch(arm.kind, arm.value);
        } catch (Throwable refused) {
            RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.DIAGNOSTIC,
                    arm.siteId, "the VM refused to force this branch ("
                            + ConcolicRegionRuntime.rootCause(refused)
                            + "), so it took the arm its operands decide");
        }
    }

    /**
     * States on one decision's row what the VM forced ({@code forced}, and
     * {@code concreteOutcome}: an if's arm its operands decided, a switch's
     * whether its selector had a case) and, at the first decision forced
     * against its concrete arm, opens the forced world.  {@code event} is
     * the decision's VM branch event; {@code caseKeys}, a switch's, else
     * null.
     */
    static void mark(ActiveRegion active, JsonObject mapping,
                     JsonObject event, List<Integer> caseKeys) {
        if (event == null || !optionalBool(event, "forced", false)) return;
        long concrete = optionalLongInteger(event, "concrete", 0L);
        boolean outcome = optionalBool(mapping, "outcome", false);
        boolean concreteOutcome = caseKeys == null ? concrete != 0L
                : caseKeys.contains(Integer.valueOf((int) concrete));
        ForcingTable.Arm arm = active.activation.forcedArms.get(
                optionalString(mapping, "siteId"));
        // A switch forced to a case other than its selector's, or to its
        // default from a case, took another successor than its selector.
        boolean against = caseKeys == null || arm == null
                ? concreteOutcome != outcome
                : arm.kind == ForcingTable.CASE ? concrete != arm.value
                : concreteOutcome;
        mapping.addProperty("forced", true);
        mapping.addProperty("concreteOutcome", concreteOutcome);
        if (!against) return;
        mapping.addProperty(AGAINST, true);
        long seq = optionalLongInteger(mapping, "vmEventId", 0L);
        if (seq <= 0L || active.token != armed) return;
        synchronized (LOCK) {
            if (forcedFrom == 0L || seq < forcedFrom) forcedFrom = seq;
        }
    }

    /** Where this activation's forced world begins, or 0: none, or it
     *  is not the activation whose target was forced on its fatal arm. */
    static long forcedFrom(ActiveRegion active) {
        synchronized (LOCK) {
            return active.token == disarmed && !target.isEmpty()
                    ? forcedFrom : 0L;
        }
    }

    /** The armed activation, once it reached its target decision. */
    private static long disarmed;

    /**
     * The armed activation reached its target decision: on its fatal arm
     * (forced, or as its operands decided), the forced path ends there;
     * on its healthy one (a branch the VM could not force: no marker owned
     * it), the run is FORCE_DIVERGED.  Nothing it decides from here is
     * forced.
     */
    static void reachedTarget(ActiveRegion active, String site, int ordinal,
                              boolean outcome) {
        synchronized (LOCK) {
            if (active.token != armed) return;
            Boolean fatal = site.equals(active.activation.targetBranchSite)
                    ? Boolean.valueOf(
                    active.activation.targetBranchRequiredOutcome)
                    : active.activation.targetGuards.get(site);
            if (fatal != null && fatal.booleanValue() == outcome) {
                target = site + "#" + ordinal;
            } else {
                diverged = FORCE_DIVERGED + ": the target decision " + site
                        + "#" + ordinal + " took its healthy arm, which no"
                        + " marker of its frame let the VM force";
            }
            disarmed = armed;
            armed = 0L;
        }
    }

    /** An exception unwinds a woven frame: the first in the forced world is
     *  named in a divergence. */
    static void unwinding(Throwable thrown) {
        if (armed == 0L || thrown == null) return;
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null || active.token != armed) return;
        synchronized (LOCK) {
            if (!unwound.isEmpty() || forcedFrom == 0L) return;
            StackTraceElement[] trace = thrown.getStackTrace();
            unwound = thrown.getClass().getName()
                    + (thrown.getMessage() == null ? ""
                    : ": " + thrown.getMessage())
                    + (trace.length == 0 ? "" : " at " + trace[0]);
        }
    }

    /**
     * The armed activation (or the one it was) ends: after its forced
     * target, how it ended; before it, the FORCE_DIVERGED reason, which
     * decides the run ({@link FocusedReplay#decideForced}: it ends at once).
     *
     * @return that reason, or "" when this ending decides nothing
     */
    static String finished(ActiveRegion active, String exitKind,
                           String exceptionType) {
        String reason;
        synchronized (LOCK) {
            if (active.token == disarmed && !target.isEmpty()) {
                ended = exitKind + (exceptionType == null
                        || exceptionType.isEmpty() ? "" : " " + exceptionType);
                return "";
            }
            if (active.token == disarmed) {
                reason = diverged;
            } else if (active.token != armed) {
                return "";
            } else {
                armed = 0L;
                diverged = FORCE_DIVERGED + ": the declared occurrence closed"
                        + " (" + exitKind + (exceptionType == null
                        || exceptionType.isEmpty() ? "" : " " + exceptionType)
                        + ") before its target decision was forced"
                        + (forcedFrom == 0L ? ", no branch forced against"
                        + " its concrete arm" : "; forced from event "
                        + forcedFrom)
                        + (unwound.isEmpty() ? ""
                        : "; the forced world first threw " + unwound);
                reason = diverged;
            }
        }
        return reason;
    }

    /** The FORCE obligation's verdict at the run's end. */
    static ObligationResult verdict(String obligationId, String sessionId) {
        synchronized (LOCK) {
            if (!target.isEmpty()) {
                return ObligationResult.of(obligationId, Verdict.ADMITTED,
                        sessionId, FORCED_TARGET + ": the declared "
                                + "occurrence took its fatal arm at "
                                + target + ", forced"
                                + (forcedFrom == 0L ? " along its concrete"
                                + " arms" : " from event " + forcedFrom)
                                + "; it ended "
                                + (ended.isEmpty() ? "unclosed" : ended));
            }
            return ObligationResult.of(obligationId, Verdict.NOT_ADMITTED,
                    sessionId, !diverged.isEmpty() ? diverged
                            : FORCE_DIVERGED + ": " + (entered
                            ? "the declared occurrence never closed"
                            : "the declared occurrence never ran"));
        }
    }

    static void resetForTests() {
        synchronized (LOCK) {
            armed = 0L;
            disarmed = 0L;
            entered = false;
            forcedFrom = 0L;
            target = "";
            ended = "";
            unwound = "";
            diverged = "";
        }
    }
}
