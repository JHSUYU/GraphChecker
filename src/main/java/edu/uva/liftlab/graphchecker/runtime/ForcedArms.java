package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonObject;
import edu.uva.liftlab.graphchecker.contract.JvmNames;
import edu.uva.liftlab.graphchecker.contract.ObligationResult;
import edu.uva.liftlab.graphchecker.contract.Verdict;
import edu.uva.liftlab.graphchecker.plan.ForcingTable;
import edu.uva.liftlab.graphchecker.plan.SiteId;

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

    /** Whether {@code active} is the armed activation of this FORCE run,
     *  on its way to its target: its loops are bounded by the work cap
     *  alone ({@code LoopAccounting.LoopBackedgeBudget#traverse}). */
    static boolean armedOn(ActiveRegion active) {
        long token = armed;
        return token != 0L && active.token == token;
    }

    /**
     * Asks the VM to force the branch the woven prefix marks next, when the
     * armed activation reaches a site of its table; called just before the
     * marker ({@link BranchObservation#prepare}).  A refusal -- a negative
     * status, or the call failing -- leaves the branch to its operands, so
     * the run can force nothing: it is FORCE_DIVERGED at once.
     *
     * @return that reason, which decides the run
     *         ({@link FocusedReplay#decideForced}), or ""
     */
    static String direct(ActiveRegion active, String method, int unitIndex) {
        if (armed == 0L || active.token != armed) return "";
        Map<String, ForcingTable.Arm> table = active.activation.forcedArms;
        ForcingTable.Arm arm = table.get(SiteId.render(method, unitIndex));
        if (arm == null || arm.passable
                || !arm.via.isEmpty() && !calledFrom(arm.via)) {
            return "";
        }
        String refused;
        try {
            int status = ConcolicVmBroker.engine().forceNextBranch(arm.arm);
            refused = status == 0 ? "" : "status " + status;
        } catch (Throwable thrown) {
            refused = ConcolicRegionRuntime.rootCause(thrown);
        }
        if (refused.isEmpty()) return "";
        synchronized (LOCK) {
            if (active.token != armed) return "";
            diverged = FORCE_DIVERGED + ": the VM refused to force "
                    + arm.siteId + " (" + refused + "), so the branch took"
                    + " the arm its operands decide";
            disarmed = armed;
            armed = 0L;
            return diverged;
        }
    }

    /**
     * States on a decision row the frame that called its method, where the
     * occurrence's forcing table names its site with a {@code via} ({@code
     * DecisionRow#via}): COMPOSE counts a decider on the way only in a call
     * of its helper from there ({@code compose.RestsOn#wayGuard}), as a
     * FORCE run forces it only there ({@link #direct}).  In every run, not
     * only a FORCE run: each task carries its target's table.
     */
    static void statesCaller(ActiveRegion active, JsonObject mapping) {
        ForcingTable.Arm arm = active.activation.forcedArms.get(
                optionalString(mapping, "siteId"));
        if (arm != null && !arm.via.isEmpty()) {
            mapping.addProperty("via", Identity.callerFrame());
        }
    }

    /** Whether the running helper was called from {@code via}: the frame
     *  one level out, as {@code Identity} enters it. */
    static boolean calledFrom(String via) {
        return JvmNames.stable(via).equals(Identity.callerFrame());
    }

    /**
     * States on one if's decision row what the VM forced ({@code forced},
     * and {@code concreteOutcome}, the arm its operands decided) and, at the
     * first decision forced against its concrete arm, opens the forced
     * world.  {@code event} is the decision's VM branch event.
     */
    static void mark(ActiveRegion active, JsonObject mapping,
                     JsonObject event) {
        if (event == null || !optionalBool(event, "forced", false)) return;
        boolean concreteOutcome =
                optionalLongInteger(event, "concrete", 0L) != 0L;
        mapping.addProperty("forced", true);
        mapping.addProperty("concreteOutcome", concreteOutcome);
        if (concreteOutcome == optionalBool(mapping, "outcome", false)) {
            return;
        }
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
     * The armed activation reached a test of its target: on its fatal arm
     * (forced, or as its operands decided), the forced path ends there.  On
     * its healthy arm, a passable test -- one whose healthy arm runs on to
     * another test of the same throw, the first of {@code if (a || b)},
     * left to its operands -- decides nothing: the run goes on to the test
     * that is forced (solr-18406 F2V3: getAndSaveCommitPoint's u11).  Any
     * other test on its healthy arm (a branch the VM could not force: no
     * marker owned it) makes the run FORCE_DIVERGED.  Once decided, nothing
     * the activation decides is forced.
     *
     * @return whether this test's reach is the target row's: false for the
     *         passable test that decided nothing, so the row stands at the
     *         forced test and states the forced path condition up to it
     *         (solr-18406 SC1: a row left at u11, before the forced world
     *         opened at u12, stated the plain disjunction as its phi)
     */
    static boolean reachedTarget(ActiveRegion active, String site,
                                 int ordinal, boolean outcome) {
        synchronized (LOCK) {
            if (active.token != armed) return true;
            Boolean fatal = site.equals(active.activation.targetBranchSite)
                    ? Boolean.valueOf(
                    active.activation.targetBranchRequiredOutcome)
                    : active.activation.targetGuards.get(site);
            boolean healthy = fatal == null || fatal.booleanValue() != outcome;
            ForcingTable.Arm arm = active.activation.forcedArms.get(site);
            if (healthy && arm != null && arm.passable) return false;
            if (!healthy) {
                target = site + "#" + ordinal;
            } else {
                diverged = FORCE_DIVERGED + ": the target decision " + site
                        + "#" + ordinal + " took its healthy arm, which no"
                        + " marker of its frame let the VM force";
            }
            disarmed = armed;
            armed = 0L;
            return true;
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
                        + (active.cut == null ? "" : ": " + active.cut)
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

    /** Why the run never reached its forced target -- its FORCE_DIVERGED
     *  verdict detail -- or "" once it did. */
    static String unreached() {
        synchronized (LOCK) {
            return target.isEmpty() ? verdictDetail() : "";
        }
    }

    /** A NOT_ADMITTED verdict's detail; called under {@link #LOCK}. */
    private static String verdictDetail() {
        return !diverged.isEmpty() ? diverged : FORCE_DIVERGED + ": "
                + (entered ? "the declared occurrence never closed"
                : "the declared occurrence never ran");
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
                    sessionId, verdictDetail());
        }
    }
}
