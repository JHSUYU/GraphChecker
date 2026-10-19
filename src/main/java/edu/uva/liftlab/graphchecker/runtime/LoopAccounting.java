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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;

final class LoopAccounting {
    private LoopAccounting() {
    }

    private static final ThreadLocal<Deque<LoopRootInvocationContext>>
            LOOP_ROOT_INVOCATIONS =
            new ThreadLocal<Deque<LoopRootInvocationContext>>() {
                @Override
                protected Deque<LoopRootInvocationContext> initialValue() {
                    return new ArrayDeque<>();
                }
            };

    static void checkBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;
        String edge = nonNull(backedgeId);
        account(active, () -> {
            if (edge.isEmpty() || !active.activation.loopBound
                    .acceptsInstrumentedBound(instrumentedMaxTraversals)) {
                return new LoopBoundCut(edge, instrumentedMaxTraversals,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            }
            return active.traverseBackedge(edge, instrumentedMaxTraversals);
        }, reason -> new LoopBoundCut(edge, instrumentedMaxTraversals,
                "BOUND_HOOK_" + reason));
    }

    static void checkReplayBody(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = ConcolicRegionRuntime.observingActiveRegion();
        if (active == null) return;
        String loop = nonNull(loopId);
        account(active, () -> loop.isEmpty() || !active.activation.loopBound
                .acceptsInstrumentedBound(instrumentedMaxTraversals)
                ? new ReplayLoopResourceCut(loop, 0, 0L,
                        "INSTRUMENTATION_POLICY_MISMATCH")
                : active.chargeLoopBody(loop, instrumentedMaxTraversals),
                reason -> new ReplayLoopResourceCut(loop,
                        instrumentedMaxTraversals, 0L, "BODY_HOOK_" + reason));
    }

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

    private static void endAtCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        active.cut = cut.getMessage();
        RowRuntime.gap(GapKind.BOUND_INSUFFICIENT, GapClass.DIAGNOSTIC,
                firstNonBlank(active.address(), Long.toString(active.token)),
                "this activation's local path was cut: " + cut.getMessage());
        ConcolicRegionRuntime.finish(active.token, "CUT", "", null);
    }

    static long enterLoopRoot(
            String loopRootHookGroup, String rootMethod,
            Object receiver, Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        Deque<LoopRootInvocationContext> contexts =
                LOOP_ROOT_INVOCATIONS.get();
        long token = ConcolicRegionRuntime.TOKEN_COUNTER.incrementAndGet();
        ConcolicTaskPlan.LoopRootAdmission admission =
                config.addressLoopRootInvocation(loopRootHookGroup,
                        rootMethod, receiver, rootArguments, token);
        if (admission.answered != null) {
            RowRuntime.answered(Identity.answer(admission.answered.address),
                    admission.answered.address);
        }
        contexts.push(new LoopRootInvocationContext(token, loopRootHookGroup,
                admission.admitted, Identity.openedNone()));
        return token;
    }

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
        }
    }

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

    static boolean bodiesAddressedHere(String groupKey) {
        for (LoopRootInvocationContext context : LOOP_ROOT_INVOCATIONS.get()) {
            if (context.groupKey.equals(nonNull(groupKey))) {
                return !context.foldedEntry;
            }
        }
        return false;
    }

    static final class LoopRootInvocationContext {
        final long token;
        final String groupKey;
        private final Set<String> offeredTaskIds;
        private final boolean foldedEntry;

        private LoopRootInvocationContext(
                long token, String groupKey, Set<String> offeredTaskIds,
                boolean foldedEntry) {
            this.token = token;
            this.groupKey = nonNull(groupKey);
            this.offeredTaskIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(offeredTaskIds));
            this.foldedEntry = foldedEntry;
        }
    }

    static final class LoopBackedgeBudget {
        private static final String SCOPE_SEPARATOR = "\u0000frame:";
        private final Map<String, Integer> traversals = new LinkedHashMap<>();
        private final Map<String, Integer> symbolic = new LinkedHashMap<>();
        private final Map<String, Integer> termedAt = new LinkedHashMap<>();
        private final Map<String, Integer> bodies = new LinkedHashMap<>();

        Error traverse(String loopId, String key, int termed, int bound,
                       boolean forced) {
            int attempted = traversals.merge(key, 1, Integer::sum);
            if (forced) return overWorkCap(loopId, attempted + 1L, bound);
            Integer before = termedAt.put(key, termed);
            boolean decided = before == null || before.intValue() != termed;
            int counted = decided ? symbolic.merge(key, 1, Integer::sum)
                    : symbolic.getOrDefault(key, 0);
            if (decided && counted >= bound) {
                return new LoopBoundCut(loopId, bound,
                        LoopBoundPolicy.K_L_REACHED);
            }
            return overWorkCap(loopId, attempted + 1L, bound);
        }

        ReplayLoopResourceCut body(String loopId, String key, int bound) {
            int entered = bodies.merge(key, 1,
                    (held, one) -> held == Integer.MAX_VALUE ? held
                            : held + one);
            return overWorkCap(loopId, entered, bound);
        }

        private static ReplayLoopResourceCut overWorkCap(String loopId,
                                                         long body,
                                                         int bound) {
            int cap = LoopBoundPolicy.workCap(bound);
            return body <= cap ? null : new ReplayLoopResourceCut(loopId,
                    cap, body, ReplayLoopResourceCut.REASON);
        }

        static String scoped(String loopId, long frame) {
            return nonNull(loopId) + SCOPE_SEPARATOR + frame;
        }

    }

    public static final class ReplayLoopResourceCut extends Error {
        private static final long serialVersionUID = 1L;
        static final String REASON = LoopBoundPolicy.WORK_CAP_REACHED;

        ReplayLoopResourceCut(String loopId, int maxBodies,
                              long attemptedBody, String reason) {
            super(nonNull(reason) + " at " + nonNull(loopId) + ": body "
                    + attemptedBody + " exceeds " + maxBodies);
        }

    }

    public static final class LoopBoundCut extends Error {
        private static final long serialVersionUID = 1L;

        LoopBoundCut(String backedgeId, int maxTraversals, String reason) {
            super(nonNull(reason) + " at " + nonNull(backedgeId)
                    + " after " + maxTraversals
                    + " loop body iterations");
        }

    }
}
