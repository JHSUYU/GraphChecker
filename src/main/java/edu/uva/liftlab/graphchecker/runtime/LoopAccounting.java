package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

/**
 * Loop bounds (PIPELINE §2): what a replay may run, and the terminal it
 * takes after.
 *
 * <p>The unroll bound of an instrumented backedge ({@link #checkBackedge})
 * and the resource ceiling of a fixed-count loop ({@link #checkReplayBody}),
 * both per loop per method activation, and
 * the enclosing call a LOOP_BODY_ROOT occurrence's k counts against
 * ({@link #enterLoopRoot}).  The policy lives in {@code plan/LoopBoundPolicy};
 * this class only accounts and cuts.  Woven hook names stay in
 * {@link ConcolicRegionRuntime} as delegates.</p>
 */
final class LoopAccounting {
    private LoopAccounting() {
    }

    /** Enclosing method calls that own LOOP_BODY_ROOT iteration frames. */
    private static final ThreadLocal<Deque<LoopRootInvocationContext>>
            LOOP_ROOT_INVOCATIONS =
            new ThreadLocal<Deque<LoopRootInvocationContext>>() {
                @Override
                protected Deque<LoopRootInvocationContext> initialValue() {
                    return new ArrayDeque<>();
                }
            };

    /** Accounts for one attempted traversal of an instrumented backedge. */
    static void checkBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;
        String edge = safe(backedgeId);
        account(active, () -> {
            if (edge.isEmpty() || !active.activation.loopBound
                    .acceptsInstrumentedBound(instrumentedMaxTraversals)) {
                return new LoopBoundCut(edge, instrumentedMaxTraversals,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            }
            long attempted = active.traverseBackedge(edge);
            return attempted < instrumentedMaxTraversals ? null
                    : new LoopBoundCut(edge, instrumentedMaxTraversals,
                            "MAX_LOOP_BODY_ITERATIONS_REACHED");
        }, reason -> new LoopBoundCut(edge, instrumentedMaxTraversals,
                "BOUND_HOOK_" + reason));
    }

    /** Charges one loop body to the replay resource cap. */
    static void checkReplayBody(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;
        String loop = safe(loopId);
        // Instrumented under a different policy: loop ids untrusted.
        account(active, () -> loop.isEmpty() || instrumentedMaxTraversals
                != active.activation.loopBound.maxBackedgeTraversals()
                ? new ReplayLoopResourceCut(loop, 0, 0L,
                        "INSTRUMENTATION_POLICY_MISMATCH")
                : active.chargeLoopBody(loop),
                reason -> new ReplayLoopResourceCut(loop,
                        instrumentedMaxTraversals, 0L, "BODY_HOOK_" + reason));
    }

    /**
     * Both hooks' control flow: charge with the path condition paused, and
     * end at the cut.  Fail-CLOSED: a charge or resume that throws is cut
     * and named too ({@code failed}), or the bound silently stops being
     * enforced.
     */
    private static void account(ActiveRegion active, Supplier<Error> charge,
                                Function<String, Error> failed) {
        ConcolicVmBroker api = engine();
        boolean paused = false;
        Error cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            cut = charge.get();
        } catch (Throwable failure) {
            cut = failed.apply("FAILURE:"
                    + ConcolicRegionRuntime.rootCause(failure));
        } finally {
            if (resumeFailed(api, paused) && cut == null) {
                cut = failed.apply("RESUME_FAILURE");
            }
        }
        endAtCut(active, cut);
    }

    /** Resumes the paused path condition; true when the resume failed. */
    private static boolean resumeFailed(ConcolicVmBroker api,
                                        boolean paused) {
        if (!paused) return false;
        try {
            api.resumePathCondition();
            return false;
        } catch (Throwable failure) {
            return true;
        }
    }

    /**
     * Both hooks' terminal: publishes the bounded prefix, states the cut and
     * its reason as one {@code BOUND_INSUFFICIENT} gap row, and detaches.
     * At most once per activation ({@code finish} is a compare-and-set).
     */
    private static void endAtCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        RowRuntime.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                firstNonBlank(active.address(), Long.toString(active.token)),
                "this activation's local path was cut: " + cut.getMessage());
        ConcolicRegionRuntime.finish(active.token, "CUT", "", null);
    }

    /**
     * Opens the enclosing call that addresses LOOP_BODY_ROOT iterations.  It
     * is counted once; body entries only consult it.
     */
    static long enterLoopRoot(
            String loopRootHookGroup, String rootMethod,
            Object receiver, Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        Deque<LoopRootInvocationContext> contexts =
                LOOP_ROOT_INVOCATIONS.get();
        // Minted before the plan is asked: it is what a loop task binds to.
        long token = ConcolicRegionRuntime.TOKEN_COUNTER.incrementAndGet();
        // No index frame: only the campaign weaves this hook, so the
        // recording never stands on it; the REGION hook pushes the frame.
        ConcolicTaskPlan.LoopRootAdmission admission =
                config.addressLoopRootInvocation(loopRootHookGroup,
                        rootMethod, receiver, rootArguments, token);
        // The planned occurrence it answered by shape takes the planned
        // address here, once, where it opened (IDENTITY §9): its bodies'
        // rows, endpoints and ordinals state it.
        if (admission.answered != null) {
            RowRuntime.answered(Identity.answer(admission.answered.address),
                    admission.answered.address);
        }
        // Asked here, the only place this entry's marker is still innermost:
        // an entry that opened no occurrence addresses no bodies
        // (#bodiesAddressedHere).
        contexts.push(new LoopRootInvocationContext(token, loopRootHookGroup,
                admission.admitted, Identity.openedNone()));
        return token;
    }

    /** Closes one enclosing LOOP_BODY_ROOT method call. */
    static void exitLoopRoot(long token) {
        if (token == 0L) return;
        try {
            Deque<LoopRootInvocationContext> contexts =
                    LOOP_ROOT_INVOCATIONS.get();
            LoopRootInvocationContext context = contexts.peek();
            if (context == null || context.token != token) return;
            contexts.pop();
            if (contexts.isEmpty()) LOOP_ROOT_INVOCATIONS.remove();
        } catch (Throwable ignored) {
            // Bookkeeping must not alter a workload terminal.
        }
    }

    /**
     * The enclosing invocation on this thread that owns {@code task}, or
     * null: the one it was admitted for, which its row names.
     */
    static LoopRootInvocationContext enclosingLoopRoot(RuntimeTask task) {
        if (task == null || !task.loopBodyRoot) return null;
        for (LoopRootInvocationContext context
                : LOOP_ROOT_INVOCATIONS.get()) {
            if (!context.groupKey.equals(task.loopRootHookGroup)) {
                continue;
            }
            return context.offeredTaskIds.contains(task.taskId)
                    ? context : null;
        }
        return null;
    }

    /**
     * Whether an enclosing invocation on this thread addresses the bodies of
     * {@code groupKey} with an occurrence of its own.
     *
     * <p>Asked by {@code ConcolicRegionRuntime#enterRegionFrame} instead of
     * the fold rule (IDENTITY §1) at a loop body.  The fold gates region
     * ENTRIES; a body is an ITERATION of an entry that already ran, and the
     * fold there would ask about whatever region
     * folds innermost, refusing every body.  False when the loop root's own
     * entry folded: its bodies would re-activate the occurrence it folded
     * into.</p>
     */
    static boolean bodiesAddressedHere(String groupKey) {
        for (LoopRootInvocationContext context : LOOP_ROOT_INVOCATIONS.get()) {
            if (context.groupKey.equals(safe(groupKey))) {
                return !context.foldedEntry;
            }
        }
        return false;
    }

    /** One enclosing method invocation for bounded body activations. */
    static final class LoopRootInvocationContext {
        /** This invocation's entry event: what a loop task is bound to. */
        final long token;
        /** The loop root it opened ({@code ExecutionTask#loopRootHookGroup}). */
        final String groupKey;
        /** The tasks this entry was offered to. */
        private final Set<String> offeredTaskIds;
        /** Whether the region entry at this same Java entry folded. */
        private final boolean foldedEntry;

        private LoopRootInvocationContext(
                long token, String groupKey, Set<String> offeredTaskIds,
                boolean foldedEntry) {
            this.token = token;
            this.groupKey = safe(groupKey);
            this.offeredTaskIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(offeredTaskIds));
            this.foldedEntry = foldedEntry;
        }
    }

    /** Completed traversals and bodies, per budget key (a loop in one
     *  method activation). */
    static final class LoopBackedgeBudget {
        private static final String SCOPE_SEPARATOR = "\u0000frame:";
        private final int maxTraversals;
        private final Map<String, Integer> traversals =
                new LinkedHashMap<>();
        private final Map<String, Integer> bodies = new LinkedHashMap<>();

        LoopBackedgeBudget(LoopBoundPolicy policy) {
            if (policy == null) {
                throw new IllegalArgumentException(
                        "loop bound policy is required");
            }
            maxTraversals = policy.maxBackedgeTraversals();
        }

        long recordTraversal(String backedgeId) {
            Integer previous = traversals.get(backedgeId);
            int completed = previous == null ? 0 : previous;
            long attempted = (long) completed + 1L;
            // Attempt K would enter body K+1: only K-1 transfers complete.
            if (attempted < maxTraversals) {
                traversals.put(backedgeId, (int) attempted);
            }
            return attempted;
        }

        static String scoped(String loopId, long frame) {
            return safe(loopId) + SCOPE_SEPARATOR + frame;
        }

        /** Counts one body against the cap; returns the body number. */
        long recordBody(String loopId) {
            long entered = (long) bodies.getOrDefault(loopId, 0) + 1L;
            bodies.put(loopId, (int) Math.min(entered, Integer.MAX_VALUE));
            return entered;
        }

    }

    /** Control signal aborting a replay that spent its loop resource cap. */
    public static final class ReplayLoopResourceCut extends Error {
        private static final long serialVersionUID = 1L;
        static final String REASON = "REPLAY_LOOP_RESOURCE_CAP";

        ReplayLoopResourceCut(String loopId, int maxBodies,
                              long attemptedBody, String reason) {
            super(safe(reason) + " at " + safe(loopId) + ": body "
                    + attemptedBody + " exceeds " + maxBodies);
        }

    }

    /** Non-workload control signal used solely to abort a bounded path. */
    public static final class LoopBoundCut extends Error {
        private static final long serialVersionUID = 1L;

        LoopBoundCut(String backedgeId, int maxTraversals, String reason) {
            super(safe(reason) + " at " + safe(backedgeId)
                    + " after " + maxTraversals
                    + " loop body iterations");
        }

    }
}
