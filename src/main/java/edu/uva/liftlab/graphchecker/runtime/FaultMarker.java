package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * The explicit fault-marker cluster (C12 of the survey): what the recording
 * answered one workload-declared marker with.
 *
 * <p>A marker is a {@code boolean} literal at a call site the program is
 * about to branch on, declared by the workload itself
 * ({@code annotation.Debug.makeSymbolicBoolean}) and stamped
 * {@code EXPLICIT_SYMBOLIC_FAULT} on the action's {@code sourceKind} when
 * the finalizer mints its port.  Three questions -- which frozen actions
 * model this firing, what polarity the recording gave it, and whether this
 * activation's plan controls it at all -- and the one hook that asks them,
 * whose answer the workload consumes as a value it cannot refuse.</p>
 *
 * <p>Pure relocation out of {@link ConcolicRegionRuntime}, which keeps
 * {@code materializeSymbolicBoolean} as the delegate: that name is woven
 * into no bytecode but IS called from outside this repository
 * ({@code ipc.Client:1247} in the 17899 bugs, through
 * {@code annotation.Debug}), so it is pinned by
 * {@code src/test/resources/external-callers.txt} and stays where its
 * callers name it.</p>
 *
 * <p>What it needs back from {@link ConcolicRegionRuntime}: the innermost
 * activation.  The rest -- the per-activation firing counter and the
 * unanswered-firing row -- is ActiveRegion's.</p>
 */
final class FaultMarker {
    private FaultMarker() {
    }

    /**
     * The frozen actions that model one firing of a named fault marker.
     *
     * <p>The classification lives on {@code sourceKind}: the finalizer stamps
     * it there when it mints the port
     * ({@code RuntimeSelectedRegionFinalizer.explicitFaultPorts}).  Nothing
     * writes it into {@code symbolicDemand}, which carries the scheduler's
     * selection verdict for the same action and is either absent or
     * {@code WORKLOAD_DECLARED_SYMBOLIC_FAULT} for a fault, so reading the
     * demand here matched nothing and pinned every marker to {@code false}.
     * </p>
     *
     * <p>A marker literal is one call site, so two in-scope requests inside
     * one activation are two recorded firings with two roots.  The recorded
     * {@code replayOccurrence} is what tells them apart; without it both rows
     * answer to the name and the firing resolves to nothing.  More than one
     * survivor is still ambiguous and the caller refuses.</p>
     */
    static List<SymbolizeAction> explicitFaultCandidates(
            Collection<SymbolizeAction> actions, String name,
            int occurrence) {
        List<SymbolizeAction> candidates = new ArrayList<>();
        for (SymbolizeAction action : actions == null
                ? Collections.<SymbolizeAction>emptyList() : actions) {
            if (!RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                    .equals(action.sourceKind)
                    || !safe(name).equals(action.symbolicName)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            candidates.add(action);
        }
        return candidates;
    }

    /**
     * The polarity the recording gave one fault marker, or null.
     *
     * <p>{@code recordedPrimitiveValue} is already gated on the action's
     * {@code observed} flag, so a value here is one the mint actually saw.
     * Anything that is not a boolean literal states nothing: a marker is a
     * {@code boolean} and a value that cannot be read as one is not the
     * recording's answer to it.</p>
     */
    static Boolean recordedFaultPolarity(SymbolizeAction action) {
        String recorded = action == null ? ""
                : safe(action.recordedPrimitiveValue).trim();
        if ("true".equalsIgnoreCase(recorded)) return Boolean.TRUE;
        if ("false".equalsIgnoreCase(recorded)) return Boolean.FALSE;
        return null;
    }

    /** Whether this activation's plan controls the named fault marker. */
    static boolean declaresExplicitFault(
            Collection<SymbolizeAction> actions, String name) {
        for (SymbolizeAction action : actions == null
                ? Collections.<SymbolizeAction>emptyList() : actions) {
            if (RuntimeSelectedRegionFinalizer.EXPLICIT_SYMBOLIC_FAULT
                    .equals(action.sourceKind)
                    && safe(name).equals(action.symbolicName)) {
                return true;
            }
        }
        return false;
    }

    /** Returns the replay model for one explicitly named application fault. */
    static boolean materialize(String name) {
        ActiveRegion active = ConcolicRegionRuntime.activeRegion();
        if (active == null) {
            // Outside every replayed region: no activation is claiming
            // anything about this firing, so there is no ledger to refuse.
            return false;
        }
        int occurrence = active.materializationOccurrences.explicitFault(
                name);
        List<SymbolizeAction> candidates = explicitFaultCandidates(
                active.activation.symbolize, name, occurrence);
        if (candidates.size() > 1) {
            return false;
        }
        boolean controlled = declaresExplicitFault(
                active.activation.symbolize, name);
        if (candidates.isEmpty()) {
            active.noteFaultIdle(name, occurrence, controlled,
                    "NO_ACTION_ACCEPTS_THIS_OCCURRENCE");
            return false;
        }
        SymbolizeAction selected = candidates.get(0);
        // The recording's own polarity is the answer.  The plan states it as
        // this action's primitiveValue, gated on observed, so it is a value
        // the mint witnessed and not a default chosen here -- which is the
        // whole difference between answering the marker and pinning it.
        // Only a firing with no recorded value is unanswered.
        Boolean recorded = recordedFaultPolarity(selected);
        if (recorded == null) {
            active.noteFaultIdle(name, occurrence, controlled,
                    "NO_RECORDED_VALUE");
            return false;
        }
        return recorded;
    }
}
