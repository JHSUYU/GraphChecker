package edu.uva.liftlab.graphchecker.runtime;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;

import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime.RootHookGroup;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * R5 bounds: what a replay is allowed to run, and the terminal it takes
 * when it has run it.
 *
 * <p>Three things, one notion.  The declared unroll bound of an
 * instrumented backedge ({@link #checkBackedge}), the replay's own resource
 * ceiling per dynamic loop invocation ({@link #checkReplayBody}), and the
 * enclosing method call a LOOP_BODY_ROOT occurrence's k is counted against
 * ({@link #enterLoopRoot}).  The policy itself is not here: {@code
 * plan/LoopBoundPolicy} states it and {@code ConcolicTaskPlan} carries it
 * per task, so this class only accounts and cuts.</p>
 *
 * <p>What it needs back from {@link ConcolicRegionRuntime}: the innermost
 * unmuted activation, the bookkeeping mute, the activation terminal
 * ({@code finish}), the token counter, and {@code SiblingHookGroupEntry} --
 * the sibling-hook rule both root stacks share, which the region stack
 * still owns.  The woven hook names stay there as delegates; nothing here
 * is woven by name.</p>
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

    /**
     * Accounts for one attempted traversal of an instrumented normal CFG
     * backedge.
     */
    static void checkBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;

        ConcolicVmBroker api = engine();
        boolean paused = false;
        LoopBoundCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            String edge = safe(backedgeId);
            int runtimeMax = instrumentedMaxTraversals;
            if (edge.isEmpty() || !active.activation.loopBound
                    .acceptsInstrumentedBound(runtimeMax)) {
                cut = active.loopBoundCut(edge, runtimeMax,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            } else {
                long attempted = active.loopBackedges.recordTraversal(edge);
                if (attempted >= runtimeMax) {
                    cut = active.loopBoundCut(edge, runtimeMax,
                            "MAX_LOOP_BODY_ITERATIONS_REACHED");
                }
            }
        } catch (Throwable failure) {
            cut = active.loopBoundCut(safe(backedgeId),
                    instrumentedMaxTraversals,
                    "BOUND_HOOK_FAILURE:" + ConcolicRegionRuntime.rootCause(failure));
        } finally {
            if (resumeLoopAccounting(active, api, paused) && cut == null) {
                cut = active.loopBoundCut(safe(backedgeId),
                        instrumentedMaxTraversals,
                        "BOUND_HOOK_RESUME_FAILURE");
            }
        }
        endAtCut(active, cut);
    }

    /**
     * Charges one loop body to the replay resource cap without consulting the
     * unroll bound.
     */
    static void checkReplayBody(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;

        ConcolicVmBroker api = engine();
        boolean paused = false;
        ReplayLoopResourceCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            String loop = safe(loopId);
            if (loop.isEmpty() || instrumentedMaxTraversals
                    != active.activation.loopBound.maxBackedgeTraversals()) {
                // The class was instrumented under a different policy, so its
                // loop identities cannot be trusted to account for anything.
                cut = new ReplayLoopResourceCut(loop, 0, 0L);
            } else {
                cut = active.chargeLoopBody(loop);
            }
        } catch (Throwable failure) {
            // Fail-OPEN, unlike the sibling: checkLoopBackedge turns the
            // same failure into a BOUND_HOOK_FAILURE cut, while here the
            // body goes uncharged and the replay resource cap stops being
            // enforced for it.  Left as it stands because the fix is the
            // sibling's control flow (end the activation), not a row.
        } finally {
            resumeLoopAccounting(active, api, paused);
        }
        endAtCut(active, cut);
    }

    /** Opens one dynamic invocation of a fixed-count loop. */
    static void openInvocation(String loopId) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            active.openLoopInvocation(safe(loopId));
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /** Closes the open dynamic invocation of a fixed-count loop. */
    static void closeInvocation(String loopId) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;
        ConcolicRegionRuntime.beginBookkeeping();
        try {
            active.closeLoopInvocation(safe(loopId));
        } finally {
            ConcolicRegionRuntime.endBookkeeping();
        }
    }

    /**
     * Restores the path condition a loop-accounting hook paused.  True when
     * the resume was lost, leaving the workload's own observation muted.
     */
    private static boolean resumeLoopAccounting(
            ActiveRegion active, ConcolicVmBroker api, boolean paused) {
        if (!paused) return false;
        try {
            api.resumePathCondition();
            return false;
        } catch (Throwable failure) {
            return true;
        }
    }

    /** Publishes the bounded prefix and detaches symbolic observation. */
    private static void endAtCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        ConcolicRegionRuntime.finish(active.token, "CUT", "", null);
    }

    /**
     * Opens the lightweight enclosing call that addresses LOOP_BODY_ROOT
     * iterations. The outer invocation is counted once; individual body
     * entries only consult this context and never advance that address.
     */
    static long enterLoopRoot(
            String instrumentationSelector, String rootMethod,
            Object receiver, Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        RootHookGroup group = config.loopRootHookGroup(
                instrumentationSelector, rootMethod);
        Deque<LoopRootInvocationContext> contexts =
                LOOP_ROOT_INVOCATIONS.get();
        for (LoopRootInvocationContext existing : contexts) {
            if (existing.claimsSiblingHook(group.key)) return 0L;
        }
        // The entry event of this enclosing invocation, minted before the
        // plan is asked, because it is what the plan binds a loop task to:
        // the bodies of one occurrence are the bodies of ONE enclosing
        // activation, and a second one is a second k.
        long token = ConcolicRegionRuntime.TOKEN_COUNTER.incrementAndGet();
        // No index frame: this hook is woven by the campaign and by nothing
        // else, so a frame pushed here is a frame the recording never stands
        // on.  The frame of this entry is the one its REGION hook pushes --
        // the campaign's at a campaign root, the skeleton weave's at any
        // other skeleton root -- which is exactly where the recording pushes
        // one.
        Map<String, Integer> admittedTasks = config.addressLoopRootInvocation(
                group.key, rootMethod, receiver, rootArguments, token);
        contexts.push(new LoopRootInvocationContext(token, group.key,
                Math.max(0, group.hookCount - 1), admittedTasks));
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
            // Runtime bookkeeping must not alter a workload terminal.
        }
    }

    /**
     * The enclosing invocation on this thread that owns {@code task}, or
     * {@code null}.
     *
     * <p>One loop task's bodies belong to exactly one of these -- the
     * invocation it was admitted for -- and the row it publishes names
     * which, so "two enclosing invocations, one occurrence" is a statement
     * the corpus can contradict rather than an inference from thread
     * names.</p>
     */
    static LoopRootInvocationContext enclosingLoopRoot(RuntimeTask task) {
        if (task == null || !task.loopBodyRoot) return null;
        for (LoopRootInvocationContext context
                : LOOP_ROOT_INVOCATIONS.get()) {
            if (!context.groupKey.equals(task.loopRootHookGroupKey())) {
                continue;
            }
            return context.ordinalByTaskId.containsKey(task.taskId)
                    ? context : null;
        }
        return null;
    }

    /** One real enclosing method invocation for bounded body activations. */
    static final class LoopRootInvocationContext
            extends ConcolicRegionRuntime.SiblingHookGroupEntry {
        /** This invocation's entry event: what a loop task is bound to. */
        final long token;
        /** Which k this entry was counted at, per task it was offered to. */
        private final Map<String, Integer> ordinalByTaskId;

        private LoopRootInvocationContext(
                long token, String groupKey, int remainingSiblingHooks,
                Map<String, Integer> ordinalByTaskId) {
            super(groupKey, remainingSiblingHooks);
            this.token = token;
            this.ordinalByTaskId = Collections.unmodifiableMap(
                    new LinkedHashMap<>(ordinalByTaskId));
        }
    }

    /** Per-activation, per-CFG-edge completed traversal accounting. */
    static final class LoopBackedgeBudget {
        private static final String SCOPE_SEPARATOR = "\u0000definition:";
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
            // Body one executes before this edge. Attempt K would enter body
            // K+1, so only the first K-1 backedge transfers may complete.
            if (attempted < maxTraversals) {
                traversals.put(backedgeId, (int) attempted);
            }
            return attempted;
        }

        static String scoped(String loopId, long invocation) {
            return safe(loopId) + SCOPE_SEPARATOR + invocation;
        }

        /**
         * Counts one body of this loop against the replay resource cap and
         * returns the body number just entered.
         */
        long recordBody(String loopId) {
            long entered = (long) bodies.getOrDefault(loopId, 0) + 1L;
            bodies.put(loopId, (int) Math.min(entered, Integer.MAX_VALUE));
            return entered;
        }

    }

    /**
     * Non-workload control signal aborting a replay that has spent its loop
     * resource cap.
     */
    public static final class ReplayLoopResourceCut extends Error {
        private static final long serialVersionUID = 1L;
        static final String REASON = "REPLAY_LOOP_RESOURCE_CAP";

        ReplayLoopResourceCut(String loopId, int maxBodies,
                              long attemptedBody) {
            super(REASON + " at " + safe(loopId) + ": body "
                    + attemptedBody + " exceeds " + maxBodies);
        }

    }

    /** Non-workload control signal used solely to abort a bounded path. */
    public static final class LoopBoundCut extends Error {
        private static final long serialVersionUID = 1L;

        LoopBoundCut(String backedgeId, int maxTraversals, String reason) {
            super("concolic path cut at " + safe(backedgeId)
                    + " after " + maxTraversals
                    + " loop body iterations");
        }

    }
}
