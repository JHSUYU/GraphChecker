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

final class ForcedArms {
    static final String FORCED_TARGET = "FORCED_TARGET";
    static final String FORCE_DIVERGED = "FORCE_DIVERGED";
    static final String AGAINST = "forcedAgainst";

    private static final Object LOCK = new Object();
    private static volatile long armed;
    private static boolean entered;
    private static long forcedFrom;
    private static String target = "";
    private static String ended = "";
    private static String unwound = "";
    private static String diverged = "";

    private ForcedArms() {
    }

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

    static boolean armedOn(ActiveRegion active) {
        long token = armed;
        return token != 0L && active.token == token;
    }

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

    static void statesCaller(ActiveRegion active, JsonObject mapping) {
        ForcingTable.Arm arm = active.activation.forcedArms.get(
                optionalString(mapping, "siteId"));
        if (arm != null && !arm.via.isEmpty()) {
            mapping.addProperty("via", Identity.callerFrame());
        }
    }

    static boolean calledFrom(String via) {
        return JvmNames.stable(via).equals(Identity.callerFrame());
    }

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

    static long forcedFrom(ActiveRegion active) {
        synchronized (LOCK) {
            return active.token == disarmed && !target.isEmpty()
                    ? forcedFrom : 0L;
        }
    }

    private static long disarmed;

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

    static String unreached() {
        synchronized (LOCK) {
            return target.isEmpty() ? verdictDetail() : "";
        }
    }

    private static String verdictDetail() {
        return !diverged.isEmpty() ? diverged : FORCE_DIVERGED + ": "
                + (entered ? "the declared occurrence never closed"
                : "the declared occurrence never ran");
    }

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
