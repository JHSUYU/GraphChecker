package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.CanonicalJson;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.concolic.RecordedReadFrom;
import edu.uva.liftlab.graphchecker.concolic.RpcExpressionHandoff;
import edu.uva.liftlab.graphchecker.concolic.SelectedReadCut;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SparseReadCutGate;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.VmHandoffEvidence;
import edu.uva.liftlab.graphchecker.concolic.SmtModelValueCodec;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.PathObservation;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ThreadFactory;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.array;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

/**
 * Runtime bridge injected at symbolic-region roots for the second (concolic)
 * unit-test execution.
 *
 * <p>The class uses reflection for the custom {@code java.lang.System} APIs so
 * GraphChecker itself remains buildable and testable on an ordinary JDK.</p>
 */
public final class ConcolicRegionRuntime {
    static final String CONFIGURED_SOURCE_PHASE_OBSERVATIONS =
            "configuredSourcePhaseObservations";
    static final String CONFIGURED_SOURCE_PHASE_GAPS =
            "configuredSourcePhaseGaps";
    private static final Pattern DEFAULT_EXECUTOR_THREAD_NAME =
            Pattern.compile("^pool-[0-9]+-thread-([0-9]+)$");
    private static final Pattern DEFAULT_OBJECT_IDENTITY_THREAD_NAME =
            Pattern.compile("^([A-Za-z_$][A-Za-z0-9_$.]*?)@"
                    + "[0-9a-fA-F]+$");
    private static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    private static final int SNAPSHOT_INDEXED = 0;
    private static final int SNAPSHOT_MAP = 1;
    private static final int SNAPSHOT_SET = 2;
    private static final int SNAPSHOT_ARRAY = 3;
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    private static final Object CONFIG_LOCK = new Object();
    private static final Object WRITE_LOCK = new Object();
    /** Guards the process-exit barrier alone. */
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    /**
     * JSON decoding and durable result publication must not hold an RPC
     * handler after its VM-owned read-outs are complete.
     */
    private static final ThreadPoolExecutor RESULT_PUBLICATION_EXECUTOR =
            new ThreadPoolExecutor(2, 2, 0L, TimeUnit.MILLISECONDS,
                    new ArrayBlockingQueue<Runnable>(128),
                    new ThreadFactory() {
                        @Override
                        public Thread newThread(Runnable runnable) {
                            Thread thread = new Thread(runnable,
                                    "causynth-result-publication-"
                                            + PUBLICATION_THREAD_COUNTER
                                            .incrementAndGet());
                            thread.setDaemon(true);
                            return thread;
                        }
                    }, new ThreadPoolExecutor.AbortPolicy());
    /** Guarded by {@link #PUBLICATION_LOCK}. */
    private static int resultPublicationsInFlight;
    /**
     * Selected activations that are live but have not yet registered a
     * publication.
     */
    private static int liveSelectedRegions;
    private static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    /** Monotonic ordinal of one recorded-evidence read-out batch. */
    private static final AtomicLong EVIDENCE_SNAPSHOTS = new AtomicLong();
    static final String HALT_AFTER_SELECTED_RESULT_PROPERTY =
            "causynth.concolic.halt.after.selected.result";
    /** Why an activation never published a region result. */
    static final String SKIP_NOT_STARTED = "NOT_STARTED";
    static final String SKIP_REPLAY_PREFIX_UNMATCHED =
            "REPLAY_PREFIX_UNMATCHED";
    static final String SKIP_SEED_OUTCOME_CONFLICT = "SEED_OUTCOME_CONFLICT";
    static final String SKIP_UNAPPLIED_MODEL_ASSIGNMENT =
            "UNAPPLIED_MODEL_ASSIGNMENT";
    /**
     * A candidate ran to its terminal and was not the occurrence its plan row
     * addressed: it ran on another source, or inside another request scope.
     */
    static final String SKIP_OCCURRENCE_ANCHOR_UNMATCHED =
            "OCCURRENCE_ANCHOR_UNMATCHED";
    /** The source this occurrence is anchored on never existed in this run. */
    static final String SKIP_ANCHOR_SOURCE_NEVER_EXISTED =
            "ANCHOR_EPOCH_NOT_REACHED";
    /**
     * A bounded loop address ran, but the response exchange selected as its
     * causal identity never occurred before the workload ended.
     */
    static final String SKIP_CAUSAL_ANCHOR_NOT_OBSERVED =
            "CAUSAL_ANCHOR_NOT_OBSERVED";
    /**
     * The region root was still running when the workload ended, so this
     * occurrence never reached {@code NORMAL}, {@code THROW} or a bounded
     * {@code CUT}.
     */
    /**
     * A loop-body region reached its bounded occurrence set (K_L rows) and
     * this and later iterations run concretely without capture.  Not a
     * failure: the occurrence set is bounded, not silently truncated, and the
     * composer reads this marker to know so.
     */
    static final String SKIP_LOOP_OCCURRENCES_BOUNDED =
            "LOOP_OCCURRENCES_BOUNDED";
    static final String SKIP_TERMINAL_NEVER_REACHED =
            "TERMINAL_NEVER_REACHED";
    /**
     * How long the process-exit barrier waits for a live activation that is
     * making no instrumented progress.
     */
    private static final long TERMINAL_GRACE_MILLIS = 30_000L;
    /** Emits one line per replay milestone to stderr. */
    static final String DIAGNOSTICS_PROPERTY =
            "causynth.concolic.diagnostics";
    private static volatile Boolean diagnostics;
    private static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    private static final ThreadLocal<Long> CURRENT_TOKEN = new ThreadLocal<>();
    private static final ThreadLocal<Integer> OBSERVATION_PAUSE_DEPTH =
            ThreadLocal.withInitial(() -> 0);
    /**
     * Dynamic root-invocation ownership used only by injected entry/exit
     * hooks.
     */
    private static final ThreadLocal<Deque<RootInvocationFrame>>
            ROOT_INVOCATION_FRAMES = new ThreadLocal<Deque<RootInvocationFrame>>() {
        @Override
        protected Deque<RootInvocationFrame> initialValue() {
            return new ArrayDeque<>();
        }
    };
    private static final ThreadLocal<AccessorCallContext>
            CURRENT_ACCESSOR_CALL_CONTEXT = new ThreadLocal<>();
    private static final Pattern BRANCH_OPERATOR = Pattern.compile(
            "(?:^|\\s)(==|!=|<=|>=|<|>)(?:\\s|$)");
    private static volatile Configuration configuration;
    private static volatile EngineApi engineApi;
    /** Session this JVM opened for its workload, or zero when it opened none. */
    private static volatile long workloadSessionId;
    /**
     * Exact configured-source fields selected into the current VM session.
     * Identity semantics matter: two equal Hadoop keys are distinct carriers.
     */
    private static final Object PROPAGATED_SOURCE_FIELD_LOCK = new Object();
    private static final IdentityHashMap<Object, Set<String>>
            PROPAGATED_SOURCE_FIELDS = new IdentityHashMap<>();
    /** Exact materialized activation owning each session VM context. */
    private static final Object CONTEXT_ACTIVATION_LOCK = new Object();
    private static final Map<Long, WriterActivationIdentity>
            CONTEXT_ACTIVATIONS = new LinkedHashMap<>();
    private ConcolicRegionRuntime() {
    }

    /**
     * Starts an observation-only subtree before an instrumented method calls
     * back into this runtime. Soot emits this boundary in the analyzed method
     * so runtime/Gson frames are entered while symbolic propagation is muted.
     * The VM still keeps structural shadow frames balanced.
     */
    public static void pauseObservation() {
        OBSERVATION_PAUSE_DEPTH.set(OBSERVATION_PAUSE_DEPTH.get() + 1);
        try {
            engine().pausePathCondition();
        } catch (Throwable ignored) {
            // A missing/inactive engine is already handled by the region hook.
        }
    }

    /** Completes the observation-only subtree started by {@link #pauseObservation()}. */
    public static void resumeObservation() {
        int depth = OBSERVATION_PAUSE_DEPTH.get();
        if (depth <= 1) OBSERVATION_PAUSE_DEPTH.remove();
        else OBSERVATION_PAUSE_DEPTH.set(depth - 1);
        try {
            engine().resumePathCondition();
        } catch (Throwable ignored) {
            // Resume is intentionally harmless when no region is active.
        }
    }

    /**
     * Opens the exact static call-site context for a configured-source hook.
     */
    public static long enterConfiguredSourcePhaseCallSite(
            String method, int unitIndex, String declaredCallee) {
        try {
            ActiveRegion active = activeRegion();
            long replayOwnerId = active == null ? 0L : active.token;
            return CausynthTraceRecorder.beginCall(replayOwnerId, safe(method),
                    unitIndex, safe(declaredCallee), null);
        } catch (Throwable ignored) {
            // Evidence bookkeeping must never change workload behavior.  A
            // zero id makes both matching close hooks no-ops.
            return 0L;
        }
    }

    /** Closes the context opened by {@link #enterConfiguredSourcePhaseCallSite}. */
    public static void exitConfiguredSourcePhaseCallSite(
            long invocationId, Object returnValue, String primitiveValue) {
        if (invocationId <= 0L) return;
        try {
            CausynthTraceRecorder.endCall(invocationId, returnValue,
                    safe(primitiveValue));
        } catch (Throwable ignored) {
            // See enterConfiguredSourcePhaseCallSite: trace failure is not an
            // application failure.
        }
    }

    /** Closes a configured-source call-site on the invocation's throw edge. */
    public static void throwConfiguredSourcePhaseCallSite(long invocationId) {
        if (invocationId <= 0L) return;
        try {
            CausynthTraceRecorder.throwCall(invocationId);
        } catch (Throwable ignored) {
            // Keep the original workload exception as the only visible one.
        }
    }

    /**
     * Mutes this layer's own bookkeeping for the duration of one evidence
     * call, and must be paired with {@link #endBookkeeping()} in a finally.
     *
     * <p>It has to be: this layer reflects, parses JSON, builds strings and
     * walks collections holding the very objects the workload symbolized, and
     * an unmuted call records hundreds of conditions of GraphChecker's own
     * control flow into the workload's path condition and mints session
     * expressions for GraphChecker's own strings.</p>
     */
    private static void beginBookkeeping() {
        pauseObservation();
    }

    /** Ends the muted subtree {@link #beginBookkeeping()} opened. */
    private static void endBookkeeping() {
        resumeObservation();
    }

    /**
     * Accounts for one attempted traversal of an instrumented normal CFG
     * backedge.
     */
    public static void checkLoopBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        if (OBSERVATION_PAUSE_DEPTH.get() > 0) return;
        ActiveRegion active = activeRegion();
        if (active == null) return;

        EngineApi api = engine();
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
                long attempted = active.loopBackedges.recordTraversal(
                        active.loopBudgetScopes.isEmpty() ? edge
                                : LoopBackedgeBudget.scoped(edge,
                                active.loopBudgetScopes.peek()));
                if (attempted >= runtimeMax) {
                    cut = active.loopBoundCut(edge, runtimeMax,
                            "MAX_LOOP_BODY_ITERATIONS_REACHED");
                }
            }
        } catch (Throwable failure) {
            cut = active.loopBoundCut(safe(backedgeId),
                    instrumentedMaxTraversals,
                    "BOUND_HOOK_FAILURE:" + rootCause(failure));
        } finally {
            if (paused) {
                try {
                    api.resumePathCondition();
                } catch (Throwable failure) {
                    active.addUnresolvedOnce(
                            "loop-bound path-condition resume failed: "
                                    + rootCause(failure));
                    if (cut == null) {
                        cut = active.loopBoundCut(safe(backedgeId),
                                instrumentedMaxTraversals,
                                "BOUND_HOOK_RESUME_FAILURE");
                    }
                }
            }
        }
        endAtCut(active, cut);
    }

    /**
     * Charges one loop body to the replay resource cap without consulting the
     * unroll bound.
     */
    public static void checkReplayLoopBody(
            String loopId, int instrumentedMaxTraversals) {
        if (OBSERVATION_PAUSE_DEPTH.get() > 0) return;
        ActiveRegion active = activeRegion();
        if (active == null) return;

        EngineApi api = engine();
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
                active.replayResourceCut = cut.toJson();
                active.addUnresolvedOnce(
                        ReplayLoopResourceCut.REASON
                                + ":INSTRUMENTATION_POLICY_MISMATCH:" + loop);
            } else {
                cut = active.chargeLoopBody(loop);
            }
        } catch (Throwable failure) {
            active.addUnresolvedOnce("replay loop resource hook failed: "
                    + rootCause(failure));
        } finally {
            if (paused) {
                try {
                    api.resumePathCondition();
                } catch (Throwable failure) {
                    active.addUnresolvedOnce(
                            "loop-bound path-condition resume failed: "
                                    + rootCause(failure));
                }
            }
        }
        endAtCut(active, cut);
    }

    /**
     * Records the exact array length supplying one fixed-count loop
     * invocation.
     */
    public static void recordLoopCardinality(
            String loopId, int cardinality) {
        if (OBSERVATION_PAUSE_DEPTH.get() > 0) return;
        ActiveRegion active = activeRegion();
        if (active == null) return;
        beginBookkeeping();
        try {
            active.recordLoopCardinality(safe(loopId), cardinality);
        } finally {
            endBookkeeping();
        }
    }

    /** Ends the current dynamic occurrence of one fixed-count loop. */
    public static void completeLoopCardinality(String loopId) {
        if (OBSERVATION_PAUSE_DEPTH.get() > 0) return;
        ActiveRegion active = activeRegion();
        if (active == null) return;
        beginBookkeeping();
        try {
            active.completeLoopCardinality(safe(loopId));
        } finally {
            endBookkeeping();
        }
    }

    /** Publishes the bounded prefix and detaches symbolic observation. */
    private static void endAtCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        finishRootInvocation(active.token, "CUT", "", null);
    }

    /**
     * Opens the exact accessor invocation selected by one activation's
     * symbolize action.
     *
     * <p>Soot initializes the token to zero and always invokes the exit hook,
     * so disabled and unselected executions remain harmless.</p>
     */
    public static long enterAccessorCallContext(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object receiver) {
        try {
            ActiveRegion active = activeRegion();
            String caller = safe(callerMethod);
            String site = safe(callSiteId);
            String callee = safe(declaredCallee);
            if (active == null || caller.isEmpty() || callUnitIndex < 0
                    || callee.isEmpty()
                    || !site.equals(siteId(caller, callUnitIndex))) {
                return 0L;
            }
            AccessorCallContext previous =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (previous != null && previous.regionToken != active.token) {
                // A context may never cross a region activation.
                CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                previous = null;
            }
            long contextToken = ACCESSOR_CONTEXT_TOKEN_COUNTER
                    .incrementAndGet();
            String occurrenceKey = safe(caller) + "\n" + safe(site) + "\n"
                    + safe(callee);
            int occurrence = active.accessorCallOccurrences.getOrDefault(
                    occurrenceKey, 0) + 1;
            active.accessorCallOccurrences.put(occurrenceKey, occurrence);
            CURRENT_ACCESSOR_CALL_CONTEXT.set(new AccessorCallContext(
                    contextToken, active.token, Thread.currentThread(),
                    caller, callUnitIndex, site, callee, receiver, occurrence,
                    previous));
            return contextToken;
        } catch (Throwable ignored) {
            // Instrumentation hooks must not perturb the workload.
            return 0L;
        }
    }

    /** Closes a lightweight accessor scope on normal or exceptional return. */
    public static void exitAccessorCallContext(long contextToken) {
        if (contextToken == 0L) return;
        try {
            AccessorCallContext current =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (current == null) return;
            if (current.contextToken == contextToken) {
                if (current.previous == null) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                } else {
                    CURRENT_ACCESSOR_CALL_CONTEXT.set(current.previous);
                }
                return;
            }
            // Out-of-order close means malformed instrumentation or a missed
            // exceptional edge.
            for (AccessorCallContext cursor = current; cursor != null;
                 cursor = cursor.previous) {
                if (cursor.contextToken == contextToken) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                    return;
                }
            }
        } catch (Throwable ignored) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        }
    }

    static void resetForTests() {
        // A publication owns the configuration and test hooks that were live
        // when it was queued.
        boolean interrupted = false;
        synchronized (PUBLICATION_LOCK) {
            while (resultPublicationsInFlight > 0) {
                try {
                    PUBLICATION_LOCK.wait();
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
            }
        }
        synchronized (CONFIG_LOCK) {
            configuration = null;
            engineApi = null;
            workloadSessionId = 0L;
        }
        clearPropagatedSourceFields();
        clearContextActivations();
        SymbolicMessageEnvelope.clear();
        ACTIVE.clear();
        CURRENT_TOKEN.remove();
        ROOT_INVOCATION_FRAMES.remove();
        CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        beforePublicationDecodeForTests = null;
        synchronized (PUBLICATION_LOCK) {
            if (resultPublicationsInFlight != 0) {
                throw new IllegalStateException(
                        "selected result publication survived test reset");
            }
            liveSelectedRegions = 0;
            PUBLICATION_LOCK.notifyAll();
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    /**
     * Waits until every selected activation that is live or already publishing
     * a result has either durably closed its JSONL record or reported a write
     * failure.
     */
    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        List<ActiveRegion> stranded = new ArrayList<>();
        synchronized (PUBLICATION_LOCK) {
            // The live-region count covers the interval after a selected
            // activation is ACTIVE but before finish registers publication.
            long progress = liveRegionProgress();
            long deadline = System.nanoTime()
                    + TERMINAL_GRACE_MILLIS * 1_000_000L;
            while (liveSelectedRegions > 0
                    || resultPublicationsInFlight > 0) {
                long remaining = deadline - System.nanoTime();
                if (remaining <= 0L) {
                    // Nothing published and no body ran for the whole grace.
                    if (resultPublicationsInFlight == 0) {
                        stranded.addAll(ACTIVE.values());
                    }
                    // An activation counted live but not yet ACTIVE is a few
                    // instructions from being one; there is nothing to name
                    // and the barrier keeps covering that window.
                    if (!stranded.isEmpty()) break;
                    remaining = TERMINAL_GRACE_MILLIS * 1_000_000L;
                    deadline = System.nanoTime() + remaining;
                }
                int live = liveSelectedRegions;
                int publishing = resultPublicationsInFlight;
                try {
                    PUBLICATION_LOCK.wait(remaining / 1_000_000L,
                            (int) (remaining % 1_000_000L));
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
                long observed = liveRegionProgress();
                if (observed != progress || live != liveSelectedRegions
                        || publishing != resultPublicationsInFlight) {
                    progress = observed;
                    deadline = System.nanoTime()
                            + TERMINAL_GRACE_MILLIS * 1_000_000L;
                }
            }
        }
        // Outside the barrier lock: each of these appends a durable row.
        for (ActiveRegion active : stranded) {
            strandWithoutTerminal(active);
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    /** Instrumented loop bodies every live activation has charged so far. */
    private static long liveRegionProgress() {
        long charged = 0L;
        for (ActiveRegion active : ACTIVE.values()) {
            charged += active.chargedLoopBodies;
        }
        return charged;
    }

    /** Names one activation whose root never reached a terminal. */
    private static void strandWithoutTerminal(ActiveRegion active) {
        if (!active.finished.compareAndSet(false, true)) return;
        active.releaseActivationOrdinal();
        active.abandoned = true;
        ACTIVE.remove(active.token, active);
        endLiveSelectedRegion();
        writeSkipped(active.activation, SKIP_TERMINAL_NEVER_REACHED,
                "the region root was still running "
                        + TERMINAL_GRACE_MILLIS
                        + "ms after the workload ended and charged no loop "
                        + "body in that time, so this occurrence reached no "
                        + "NORMAL, THROW or bounded CUT terminal",
                null);
    }

    /** Marks one selected activation live. */
    static void beginLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            liveSelectedRegions++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    /** Marks one selected activation no longer live. */
    static void endLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            if (liveSelectedRegions <= 0) {
                throw new IllegalStateException(
                        "live selected region underflow");
            }
            liveSelectedRegions--;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void beginSelectedResultPublication() {
        synchronized (PUBLICATION_LOCK) {
            resultPublicationsInFlight++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    static void endSelectedResultPublication() {
        synchronized (PUBLICATION_LOCK) {
            if (resultPublicationsInFlight <= 0) {
                throw new IllegalStateException(
                        "selected result publication underflow");
            }
            resultPublicationsInFlight--;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    /**
     * Opens the workload-wide symbolic session that outlives every individual
     * region in this JVM.
     *
     * @return an empty string on success, otherwise a named diagnostic
     */
    public static String openWorkloadSession() {
        if (configuration().tasks.isEmpty()) {
            clearPropagatedSourceFields();
            clearContextActivations();
            return "";
        }
        EngineApi api = engine();
        api.requireCurrentCapabilities();
        final long status;
        try {
            status = api.openWorkloadSession();
        } catch (Throwable failure) {
            return "WORKLOAD_SESSION_OPEN_FAILED: " + rootCause(failure);
        }
        if (status <= 0L) {
            return "WORKLOAD_SESSION_OPEN_REFUSED: "
                    + workloadSessionStatusName(status) + " "
                    + api.workloadSessionStatus();
        }
        SymbolicMessageEnvelope.clear();
        clearPropagatedSourceFields();
        clearContextActivations();
        workloadSessionId = status;
        return "";
    }

    /**
     * Closes the session opened by {@link #openWorkloadSession}.
     *
     * @return an empty string on success or when nothing was opened, otherwise
     * a named diagnostic
     */
    public static String closeWorkloadSession() {
        // Closing the workload is the general durability boundary, regardless
        // of which launcher owns it.
        awaitSelectedResultPublications();
        long sessionId = workloadSessionId;
        if (sessionId == 0L) {
            clearPropagatedSourceFields();
            clearContextActivations();
            return "";
        }
        EngineApi api = engine();
        final long status;
        try {
            status = api.closeWorkloadSession();
        } catch (Throwable failure) {
            return "WORKLOAD_SESSION_CLOSE_FAILED: " + rootCause(failure);
        }
        if (status != 0L) {
            return "WORKLOAD_SESSION_CLOSE_REFUSED: "
                    + workloadSessionStatusName(status)
                    + " sessionId=" + sessionId + " "
                    + api.workloadSessionStatus();
        }
        SymbolicMessageEnvelope.clear();
        clearPropagatedSourceFields();
        clearContextActivations();
        workloadSessionId = 0L;
        return "";
    }

    /** One JSON snapshot of the VM session, or {@code ""} when absent. */
    public static String workloadSessionStatus() {
        return engine().workloadSessionStatus();
    }

    private static String workloadSessionStatusName(long status) {
        if (status == 0L) return "OK";
        if (status == -1L) return "ALREADY_OPEN";
        if (status == -2L) return "NOT_OPEN";
        if (status == -3L) return "MEMBERS_REMAIN";
        if (status == -4L) return "CLOSING";
        return "UNNAMED_STATUS(" + status + ")";
    }

    /** Remembers one exact source field only for this workload session. */
    private static void rememberPropagatedSourceField(
            Object owner, String fieldSignature) {
        synchronized (PROPAGATED_SOURCE_FIELD_LOCK) {
            Set<String> fields = PROPAGATED_SOURCE_FIELDS.get(owner);
            if (fields == null) {
                fields = new LinkedHashSet<>();
                PROPAGATED_SOURCE_FIELDS.put(owner, fields);
            }
            fields.add(safe(fieldSignature));
        }
    }

    /** Whether a prior activation selected this very object field. */
    private static boolean propagatedSourceField(
            Object owner, String fieldSignature) {
        synchronized (PROPAGATED_SOURCE_FIELD_LOCK) {
            Set<String> fields = PROPAGATED_SOURCE_FIELDS.get(owner);
            return fields != null && fields.contains(safe(fieldSignature));
        }
    }

    private static void clearPropagatedSourceFields() {
        synchronized (PROPAGATED_SOURCE_FIELD_LOCK) {
            PROPAGATED_SOURCE_FIELDS.clear();
        }
    }

    private static void clearContextActivations() {
        synchronized (CONTEXT_ACTIVATION_LOCK) {
            CONTEXT_ACTIVATIONS.clear();
        }
    }

    private static void rememberContextActivation(
            long contextId, ActiveRegion active) {
        if (contextId <= 0L || active == null) return;
        synchronized (CONTEXT_ACTIVATION_LOCK) {
            CONTEXT_ACTIVATIONS.put(contextId,
                    new WriterActivationIdentity(active));
        }
    }

    private static void updateContextActivation(ActiveRegion active) {
        if (active == null || active.vmContextId <= 0L) return;
        synchronized (CONTEXT_ACTIVATION_LOCK) {
            WriterActivationIdentity identity = CONTEXT_ACTIVATIONS.get(
                    active.vmContextId);
            if (identity != null) identity.publishAs(active);
        }
    }

    /** Immutable owner of one session-global VM field-version event. */
    private static final class WriterActivationIdentity {
        private final String vmTaskId;
        private final String vmRegionId;
        private volatile String sourceKey;
        private volatile String occurrenceId;

        private WriterActivationIdentity(ActiveRegion active) {
            this.vmTaskId = active.activation.taskId;
            this.vmRegionId = active.activation.regionId;
            publishAs(active);
        }

        private void publishAs(ActiveRegion active) {
            sourceKey = active.activation.sourceKey;
            occurrenceId = active.occurrenceId();
        }

        private boolean owns(RuntimeTask writer) {
            return writer != null && vmTaskId.equals(writer.taskId)
                    && vmRegionId.equals(writer.regionId);
        }
    }

    /**
     * Called at a statically selected same-thread region root with its actual
     * reference arguments.  Primitive parameter slots are null.
     */
    public static long enterRegion(String instrumentationSelector,
                                   String rootMethod,
                                   Object receiver, Object[] rootArguments) {
        ActiveRegion active = admitRegion(instrumentationSelector, rootMethod,
                receiver, rootArguments);
        return active == null ? 0L : active.token;
    }

    /**
     * Admits the one planned occurrence this root invocation will execute.
     *
     * @return the started occurrence, or {@code null} when nothing was
     *         admitted or it could not be started
     */
    private static ActiveRegion admitRegion(
            String instrumentationSelector, String rootMethod, Object receiver,
            Object[] rootArguments) {
        Configuration config = configuration();
        if (config.tasks.isEmpty() || rootMethod == null) {
            return null;
        }
        RuntimeTask admitted = selectTask(config, instrumentationSelector,
                rootMethod, receiver, rootArguments);
        if (admitted == null) return null;
        if (boundedLoopOccurrenceCut(admitted)) {
            // The bounded loop's captured occurrence set is full: release the
            // candidate so the next iteration re-selects and re-caps, and run
            // this iteration concretely.
            config.releaseCandidate(admitted);
            return null;
        }
        List<RuntimeTask> siblings;
        beginBookkeeping();
        try {
            // Claimed before the region starts, so this activation's entry
            // setup covers every occurrence it may end up answering, and
            // before this activation's other entry hooks run, so each of them
            // finds its task already live and starts no second region.
            siblings = config.claimSiblingOccurrences(admitted, rootMethod,
                    receiver, rootArguments,
                    Thread.currentThread().getName(),
                    RuntimeTraceContext.current().requestApi);
        } finally {
            endBookkeeping();
        }
        ActiveRegion active = startSymbolicRegion(admitted, receiver,
                siblings);
        if (active == null) {
            for (RuntimeTask sibling : siblings) {
                config.releaseCandidate(sibling);
            }
        }
        return active;
    }

    /**
     * Decides which planned occurrence this root invocation admits, muted.
     *
     * <p>The decision itself is this bridge's own control flow over the
     * workload's own objects: {@code RootContextSelector.matches} compares the
     * root receiver against {@code null} and against a declared class, and a
     * campaign instruments one entry hook per plan row, so every later hook on
     * a thread that already holds a selected symbolic object evaluates that
     * comparison again.</p>
     */
    private static RuntimeTask selectTask(Configuration config,
                                          String instrumentationSelector,
                                          String rootMethod,
                                          Object receiver,
                                          Object[] rootArguments) {
        beginBookkeeping();
        try {
            return config.select(instrumentationSelector, rootMethod, receiver,
                    rootArguments);
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Whether this admission is a bounded cut of a loop-body region whose
     * captured occurrence set is already full.
     *
     * <p>When it is, the one region marker is written once and the caller
     * runs the iteration concretely: no VM region, no symbolization, no
     * capture, no occurrence row -- the fast path a bounded inner loop takes
     * past {@code checkLoopBackedge}.  Hadoop still runs every heartbeat; we
     * only stop capturing after K_L.</p>
     */
    private static boolean boundedLoopOccurrenceCut(RuntimeTask admitted) {
        if (!admitted.cutsBoundedLoopOccurrence()) return false;
        if (admitted.claimLoopBoundCutMarker()) {
            int bound = admitted.loopOccurrenceBudget;
            JsonObject evidence = new JsonObject();
            evidence.addProperty("plannedOccurrenceId", admitted.occurrenceId);
            evidence.addProperty("regionId", admitted.regionId);
            evidence.addProperty("boundedAt", bound);
            String reason = "loop-body region occurrence set bounded at K_L="
                    + bound + "; further iterations run concretely without "
                    + "capture";
            if (admitted.addressesOccurrencesByCausalAnchor()
                    || admitted.unanchoredTurnsReleased > 0) {
                JsonArray ports = new JsonArray();
                for (String portId : admitted.causalAnchorPorts()) {
                    ports.add(new JsonPrimitive(portId));
                }
                evidence.add("causalAnchorPorts", ports);
                JsonArray phases = new JsonArray();
                for (String phaseId
                        : admitted.configuredSourceAnchorPhases()) {
                    phases.add(new JsonPrimitive(phaseId));
                }
                evidence.add("configuredSourceAnchorPhases", phases);
                evidence.addProperty("anchoredOccurrences",
                        admitted.anchoredOccurrences);
                evidence.addProperty("unanchoredTurnsReleased",
                        admitted.unanchoredTurnsReleased);
                evidence.addProperty("turnsAdmitted",
                        admitted.admittedTurns);
                reason = reason + "; occurrences were addressed by the "
                        + "region's semantic anchors (ports="
                        + admitted.causalAnchorPorts() + ", sourcePhases="
                        + admitted.configuredSourceAnchorPhases() + "; "
                        + admitted.anchoredOccurrences + " anchored, "
                        + admitted.unanchoredTurnsReleased
                        + " unanchored turns released)";
            }
            writeSkipped(admitted, SKIP_LOOP_OCCURRENCES_BOUNDED, reason,
                    evidence);
        }
        return true;
    }

    /** Starts one planned region occurrence. */
    private static ActiveRegion startSymbolicRegion(
            RuntimeTask admitted, Object receiver,
            List<RuntimeTask> siblings) {
        if (activeRegion() != null) {
            // One activation is one VM region context: CURRENT_TOKEN holds a
            // single token, so a second region started here would take every
            // capture from the one already running and leave it live and
            // blind. The claimant list is how another occurrence of this
            // exact activation rides it.
            admitted.noteUnaddressedCandidate(
                    "another selected occurrence was already running on this "
                            + "thread when this root was entered");
            configuration().releaseCandidate(admitted);
            return null;
        }
        beginLiveSelectedRegion();
        EngineApi api = engine();
        boolean engineStarted = false;
        boolean pathConditionPaused = false;
        ActiveRegion active = null;
        try {
            api.start(admitted.regionId, admitted.taskId);
            engineStarted = true;
            // Region setup performs reflection, collection lookups and JSON-
            // safe bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
            active = new ActiveRegion(TOKEN_COUNTER.incrementAndGet(),
                    admitted, receiver, Thread.currentThread());
            active.siblingClaimants.addAll(siblings);
            active.activationOrdinal = admitted.nextActivationOrdinal();
            ACTIVE.put(active.token, active);
            CURRENT_TOKEN.set(active.token);
            active.vmContextId = api.currentContextId();
            if (active.vmContextId <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no context id");
            }
            rememberContextActivation(active.vmContextId, active);
            // A delivery can establish the causal request immediately before
            // the selected handler entry.
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            SourceRef receiverSource = RuntimeTraceContext.sourceFor(receiver);
            if (receiverSource != null) {
                observeCausalSource(receiverSource.key());
            } else if (context.source != null
                    && RuntimeTraceContext.sameSourceIdentity(
                    admitted.sourceKey, context.source.key())) {
                observeCausalSource(context.source.key());
            } else {
                // The exact task selector is the only source authority when a
                // long-lived receiver has no alias of its own.
                observeCausalSource(admitted.sourceKey);
            }
            prepare(active);
            diag("REGION_START", "token=" + active.token
                    + " task=" + safe(admitted.taskId)
                    + " source=" + safe(admitted.sourceKey)
                    + " region=" + safe(admitted.regionId));
            api.resumePathCondition();
            pathConditionPaused = false;
            return active;
        } catch (Throwable throwable) {
            if (active != null) {
                ACTIVE.remove(active.token);
                CURRENT_TOKEN.remove();
            }
            if (engineStarted) {
                if (pathConditionPaused) {
                    // Best effort only: cleanupAfterFailure is also valid while recording
                    // is paused, but balancing the API keeps diagnostics clear.
                    try {
                        api.resumePathCondition();
                    } catch (Throwable ignored) {
                        // cleanupAfterFailure below owns the definitive cleanup.
                    }
                }
                api.cleanupAfterFailure();
            }
            writeSkipped(admitted, SKIP_NOT_STARTED,
                    "engine start failed: " + rootCause(throwable), null);
            configuration().releaseCandidate(admitted);
            endLiveSelectedRegion();
            return null;
        }
    }

    /** Performs the declared entry setup for one selected occurrence. */
    private static void prepare(ActiveRegion active) {
        if (active.prepared) return;
        active.prepared = true;
        // Every occurrence riding this activation gets its entry setup, so
        // whichever of them the exit settles on was actually prepared.
        for (RuntimeTask claimant : active.claimants()) {
            symbolizeReceiverFields(active, claimant, engine());
            selectDeclaredSharedCarriers(active, claimant);
            for (JsonObject gate : claimant.readCutGates) {
                installReadCutGate(gate);
            }
        }
        activateSelectedEventLedger(active);
    }

    /**
     * Tells the VM that this occurrence declares selected event sites.
     *
     * <p>README {@code EVENT-1}: the order domain must record because a task
     * selected event sites, not because some location happens to be a shared
     * carrier.</p>
     */
    private static void activateSelectedEventLedger(ActiveRegion active) {
        RuntimeTask declaring = active.activation;
        if (declaring.sharedCarriers.isEmpty()
                && declaring.communicationHandoffs.isEmpty()
                && safe(declaring.regionId).isEmpty()) {
            return;
        }
        EngineApi api = engine();
        try {
            boolean recording = api.activateEventLedger();
            if (!recording) {
                recordShared(failedShared(SharedStateEvidence.STAGE_LEDGER,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        "event-ledger activation did not start recording"),
                        null, active);
                return;
            }
            diag("EVENT_LEDGER_ACTIVATED", "task="
                    + safe(active.activation.taskId)
                    + " recording=" + recording);
        } catch (Throwable throwable) {
            recordShared(failedShared(SharedStateEvidence.STAGE_LEDGER,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, active);
        }
    }

    /**
     * Whether this activation declares any selected event site: a shared
     * carrier, a declared communication port, or the selected region
     * occurrence itself.
     */
    /** Instrumentation-facing root entry. */
    public static long enterRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        // Several hooks for one selected root may appear in nested replay
        // helpers.
        for (RootInvocationFrame existing : frames) {
            if (sameSelector(existing.instrumentationSelector,
                    instrumentationSelector)) {
                frames.push(new RootInvocationFrame(instrumentationSelector,
                        rootMethod, 0L));
                return 0L;
            }
        }
        RootInvocationFrame frame = new RootInvocationFrame(
                instrumentationSelector, rootMethod, 0L);
        frames.push(frame);
        long token = enterRegion(instrumentationSelector, rootMethod, receiver,
                rootArguments);
        frame.token = token;
        return token;
    }

    private static boolean sameSelector(String left, String right) {
        return left == null ? right == null : left.equals(right);
    }

    /** Called once per Java argument immediately after {@link #enterRegion}. */
    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) {
            return;
        }
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))
                    || action.index != argumentIndex) {
                continue;
            }
            if (value == null) {
                if (active.hasAppliedExactNullReferenceAssignment(action)) {
                    // The exact model assignment has already replaced this
                    // declared reference argument with null.
                    continue;
                } else if ("ARGUMENT".equals(action.location)
                        && action.declaresArrayInput(
                        Collections.<String>emptyList())) {
                    symbolize(active, action, null, engine());
                } else {
                    active.unresolved.add(action.symbol
                            + ": primitive argument requires a stack-value model (concrete="
                            + safe(primitiveValue) + ")");
                }
                continue;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                if (action.fieldPaths.isEmpty()) {
                    active.unresolved.add(action.symbol
                            + ": selective argument has no field paths");
                    continue;
                }
                for (List<String> path : action.fieldPaths) {
                    symbolizeFieldPath(active, action, value, path, engine());
                }
            } else {
                symbolize(active, action, value, engine());
            }
        }
    }

    /** Symbolizes one scheduler-selected helper-method argument in-region. */
    public static void symbolizeMethodArgument(String method,
                                               int argumentIndex,
                                               Object value,
                                               String primitiveValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        int occurrence = active.materializationOccurrences
                .observedMethodArgument(method, argumentIndex);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesMethodArgument(method, argumentIndex)
                    || !action.acceptsOccurrence(occurrence)
                    || !active.materialized.add(action.symbol)) {
                continue;
            }
            if (value == null && !action.declaresArrayInput(
                    Collections.<String>emptyList())) {
                active.unresolved.add(action.symbol
                        + ": null method argument cannot be symbolized");
                continue;
            }
            symbolize(active, action, value, engine());
        }
    }

    /**
     * Applies a solver model to the real root argument before ordinary Java
     * control flow consumes it.  Soot writes the returned value back to the
     * parameter local (including an unbox for primitive parameters).  No
     * branch outcome is overridden here: the changed input must make the
     * unmodified branch evaluate to the requested outcome during replay.
     */
    public static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return boxedOrReference;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (action.index != argumentIndex
                    || !("ARGUMENT".equals(action.location)
                    || "ARGUMENT_FIELD_PATH".equals(action.location))) {
                continue;
            }
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, null);
            }
            if (boxedOrReference == null) {
                ModelAssignment assignment = active.assignment(action, null);
                if (assignment == null) return null;
                Object modeled = assignment.referenceValue(null);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    active.unresolved.add(action.symbol
                            + ": unsupported root reference model "
                            + assignment.valueType + "=" + assignment.value);
                    return null;
                }
                active.recordModelAssignment(assignment);
                return modeled;
            }
            if ("ARGUMENT_FIELD_PATH".equals(action.location)) {
                for (List<String> path : action.fieldPaths) {
                    applyFieldPathModel(active, action, boxedOrReference,
                            path);
                }
            } else {
                ModelAssignment assignment = active.assignment(action, null);
                if (assignment != null) {
                    Object modeled = assignment.referenceValue(
                            boxedOrReference);
                    if (modeled != UnsupportedReplayValue.INSTANCE) {
                        active.recordModelAssignment(assignment);
                        if (containerValue(modeled)
                                && active.materialized.add(action.symbol)) {
                            symbolize(active, action, modeled, engine());
                        }
                        return modeled;
                    }
                    active.unresolved.add(action.symbol
                            + ": unsupported root reference model "
                            + assignment.valueType + "=" + assignment.value);
                }
            }
            if (containerValue(boxedOrReference)
                    && active.materialized.add(action.symbol)) {
                symbolize(active, action, boxedOrReference, engine());
            }
        }
        return boxedOrReference;
    }

    /** Applies a solver model at an exact in-region helper parameter. */
    public static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return boxedOrReference;
        int occurrence = active.materializationOccurrences.methodArgument(
                method, argumentIndex);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesMethodArgument(method, argumentIndex)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            if (boxedOrReference != null
                    && isPrimitiveBox(boxedOrReference)) {
                return materializePrimitiveValue(active, action,
                        boxedOrReference, null);
            }
            Object materialized = boxedOrReference;
            ModelAssignment assignment = active.assignment(action, null);
            if (assignment != null) {
                Object modeled = assignment.referenceValue(boxedOrReference);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    active.unresolved.add(action.symbol
                            + ": unsupported method argument model "
                            + assignment.valueType + "="
                            + assignment.value);
                    return boxedOrReference;
                }
                materialized = modeled;
                active.recordModelAssignment(assignment);
            }
            if (containerValue(materialized)
                    && active.materialized.add(action.symbol)) {
                symbolize(active, action, materialized, engine());
            }
            return materialized;
        }
        return boxedOrReference;
    }

    /** Materializes a reference-valued live-in at its defining Jimple local. */
    public static Object materializeReference(String method, int unitIndex,
                                              String local, Object value) {
        ActiveRegion active = activeRegion();
        if (active == null) {
            return value;
        }
        int occurrence = active.nextLocalMaterializationOccurrence(
                method, unitIndex, local);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, unitIndex, local)
                    || !action.acceptsOccurrence(occurrence)) {
                continue;
            }
            if (!active.materialized.add(action.symbol)) {
                continue;
            }
            Object materialized = value;
            ModelAssignment assignment = active.assignment(action, null);
            if (assignment != null) {
                Object modeled = assignment.referenceValue(value);
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    if (isPrimitiveBox(value)) {
                        return materializePrimitiveValue(active, action,
                                value, null);
                    }
                    active.unresolved.add(action.symbol
                            + ": unsupported local reference model "
                            + assignment.valueType + "=" + assignment.value);
                } else {
                    materialized = modeled;
                    active.recordModelAssignment(assignment);
                }
            }
            if (materialized != null
                    || action.declaresArrayInput(
                    Collections.<String>emptyList())) {
                symbolize(active, action, materialized, engine());
            }
            return materialized;
        }
        return value;
    }

    /**
     * Materializes a primitive live-in and returns a fresh boxed value.  Soot
     * immediately unboxes this result back into the original local, allowing
     * the VM's symbolic field expression to flow into the actual branch.
     */
    public static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        ActiveRegion active = activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        int occurrence = active.nextLocalMaterializationOccurrence(
                method, unitIndex, local);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesLocal(method, unitIndex, local)
                    || !action.acceptsOccurrence(occurrence)
                    || !action.repeatedPrimitiveAccessor()
                    && !active.materialized.add(action.symbol)) {
                continue;
            }
            return materializePrimitiveValue(active, action, boxedValue,
                    null);
        }
        return boxedValue;
    }

    /** Returns the replay model for one explicitly named application fault. */
    public static boolean materializeSymbolicBoolean(String name) {
        ActiveRegion active = activeRegion();
        if (active == null) return false;
        SymbolizeAction selected = null;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!"EXPLICIT_SYMBOLIC_FAULT".equals(action.symbolicDemand)
                    || !safe(name).equals(action.symbolicName)) continue;
            if (selected != null) {
                active.addUnresolvedOnce("ambiguous explicit fault: " + name);
                return false;
            }
            selected = action;
        }
        if (selected == null) return false;
        ModelAssignment assignment = active.assignment(selected, null);
        if (assignment == null) return false;
        Object value = coerceModelValue(assignment.valueType,
                assignment.value, Boolean.class);
        if (!(value instanceof Boolean)) {
            active.addUnresolvedOnce("unsupported explicit fault model: "
                    + assignment.valueType + "=" + assignment.value);
            return false;
        }
        active.recordModelAssignment(assignment);
        return (Boolean) value;
    }

    /**
     * Materializes the primitive value consumed by one exact {@code getstatic}
     * site.
     */
    public static Object materializeStaticPrimitiveField(
            String method, int unitIndex, String fieldSignature,
            String fieldName, Object boxedValue) {
        ActiveRegion active = activeRegion();
        if (active == null || boxedValue == null) {
            return boxedValue;
        }
        SymbolizeAction selected = null;
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesStaticField(method, unitIndex,
                    fieldSignature, fieldName)) {
                continue;
            }
            if (selected != null && selected != action) {
                active.addUnresolvedOnce(siteId(method, unitIndex)
                        + ": AMBIGUOUS_STATIC_FIELD_MATERIALIZATION");
                return boxedValue;
            }
            selected = action;
        }
        if (selected == null
                || !active.materialized.add(selected.symbol)) {
            return boxedValue;
        }
        List<String> logicalPath = selected.exactStaticFieldPath(
                fieldSignature, fieldName);
        if (logicalPath == null) {
            active.addUnresolvedOnce(siteId(method, unitIndex)
                    + ": STATIC_FIELD_LOGICAL_PATH_OR_DECLARATION_MISMATCH");
            return boxedValue;
        }
        return materializePrimitiveValue(active, selected, boxedValue,
                logicalPath);
    }


    public static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return;
        int occurrence = active.materializationOccurrences.field(
                method, unitIndex);
        selectAccessOwnerSharedCarriers(active, owner, fieldSignature);
        // An accessor can be an exact causal slot without being a new symbolic
        // live-in.
        // Every occurrence riding this activation, not only the one it was
        // entered under: entry-time symbolization already covers all of them
        // (see prepare), and asking only the entered task here made a
        // claimant's live-in invisible at the one hook that can materialize
        // it.  One activation carries the occurrence that generated a
        // once-only value and the occurrence that demands its provenance;
        // the reads that make it symbolic belong to whichever of them the
        // exit settles on, so both must be offered every access site.
        for (SymbolizeAction action : active.claimantDeclaredSymbolize()) {
            if (action.matchesField(method, unitIndex, owner,
                    fieldSignature, fieldName, null)
                    && action.acceptsDirectFieldOccurrence(occurrence)) {
                active.observedInputSlots.add(action.symbol);
            }
        }
        List<SymbolizeAction> claimed = active.claimantSymbolize();
        boolean writtenInThisRegion = active.writtenFields.contains(
                owner, fieldSignature);
        if (writtenInThisRegion) {
            boolean composedInput = false;
            for (SymbolizeAction action : claimed) {
                if (action.intraRegionComposedInput()
                        && action.matchesField(method, unitIndex, owner,
                        fieldSignature, fieldName, null)
                        && action.acceptsDirectFieldOccurrence(occurrence)) {
                    composedInput = true;
                    break;
                }
            }
            if (!composedInput) return;
        }
        active.snapshotReferenceAliasSources(owner);
        for (SymbolizeAction action : claimed) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName, null)
                    || !action.acceptsDirectFieldOccurrence(occurrence)
                    || writtenInThisRegion
                    && !action.intraRegionComposedInput()) {
                continue;
            }
            Object leafOwner = action.leafOwner(owner);
            if (leafOwner == null || leafOwner == MissingValue.INSTANCE) {
                active.addUnresolvedOnce(action.symbol
                        + ": field owner is unavailable for "
                        + action.fieldPath);
                continue;
            }
            active.recordFieldAccessOwner(action.symbol, leafOwner);
            if (!active.materialized.add(action.symbol)) continue;
            try {
                boolean assignmentFailed = false;
                Object materializedContainer = null;
                List<ModelAssignment> fieldAssignments =
                        active.fieldAssignments(action);
                for (ModelAssignment assignment : fieldAssignments) {
                    List<String> path = assignment.path.isEmpty()
                            ? action.fieldPath : assignment.path;
                    Object modeledOwner = path.equals(action.fieldPath)
                            ? leafOwner : resolveFieldPathLeafOwner(owner, path);
                    String modeledFieldSignature =
                            action.exactLeafFieldSignature(path);
                    Object referenceAlias =
                            active.referenceAliasValue(assignment, owner);
                    Object targetContainer = assignment.hasContainerTarget()
                            ? readExactField(modeledOwner,
                            modeledFieldSignature)
                            : null;
                    boolean sameContainer =
                            !assignment.hasContainerTarget()
                            || materializedContainer == null
                            || materializedContainer == targetContainer;
                    boolean written = sameContainer
                            && (assignment.hasContainerTarget()
                            ? assignment.validContainerTarget()
                            && writeContainerTarget(
                                    targetContainer, assignment,
                                    referenceAlias)
                            : writeModeledField(modeledOwner,
                            modeledFieldSignature, assignment,
                            referenceAlias));
                    if (modeledOwner == null
                            || modeledOwner == MissingValue.INSTANCE
                            || !written
                            || !sameContainer) {
                        active.addUnresolvedOnce(action.symbol + "."
                                + joinFieldPath(path)
                                + ": solver model could not be materialized");
                        assignmentFailed = true;
                        continue;
                    }
                    if (assignment.hasContainerTarget()) {
                        materializedContainer = targetContainer;
                    }
                    active.recordModelAssignment(assignment);
                }
                if (assignmentFailed) continue;

                // An intra-region read-from input names the value written by
                // an earlier selected output.
                if (fieldAssignments.isEmpty()
                        && action.intraRegionComposedInput()
                        && !action.observedPrimitiveValue.isEmpty()
                        && !writeObservedPrimitiveField(leafOwner,
                        action.exactLeafFieldSignature(),
                        action.observedPrimitiveValue)) {
                    active.addUnresolvedOnce(action.symbol
                            + ": observed intra-region primitive could not "
                            + "be seeded");
                    continue;
                }

                EngineApi api = engine();
                Field exactField = declaredInstanceField(leafOwner,
                        action.exactLeafFieldSignature());
                if (exactField == null) {
                    active.addUnresolvedOnce(action.symbol
                            + ": exact field declaration is unavailable");
                    continue;
                }
                Object value = exactField.get(leafOwner);
                if ("OBSERVED_FIELD_RECEIVER".equals(action.rootKind)
                        && "BOUNDED_CONTAINER_STATE".equals(
                        action.symbolicDemand)
                        && value instanceof Map<?, ?>) {
                    // The runtime trace selected this exact access site and
                    // supplied the actual declaring-field receiver.
                    selectSharedMapCarrier(value,
                            exactField.getDeclaringClass().getName(),
                            exactField.getName(), javaTypeDescriptor(
                            exactField.getType().getTypeName()));
                }
                if (materializedContainer != null) {
                    if (value != materializedContainer) {
                        active.addUnresolvedOnce(action.symbol
                                + ": container model target is not the "
                                + "symbolized field container");
                        continue;
                    }
                    requireTrackedContainer(api, materializedContainer,
                            action.symbol);
                    ensurePathRecordingStarted(active);
                    active.recordSymbolizedInputPort(action.symbol,
                            materializedContainer);
                } else if (value != null && value != MissingValue.INSTANCE
                        && containerValue(value)) {
                    requireTrackedContainer(api, value, action.symbol);
                    ensurePathRecordingStarted(active);
                    active.recordSymbolizedInputPort(action.symbol, value);
                } else {
                    api.symbolizeExactField(leafOwner,
                            exactFieldSignature(exactField),
                            action.symbol);
                    ensurePathRecordingStarted(active);
                }
                active.symbolized.add(action.symbol);
            } catch (Throwable throwable) {
                active.addUnresolvedOnce(action.symbol
                        + ": field materialization "
                        + safe(method) + "#u" + unitIndex + " failed: "
                        + rootCause(throwable));
            }
        }
    }

    static boolean writeObservedPrimitiveField(
            Object owner, String fieldSignature, String primitiveValue) {
        Field field = declaredInstanceField(owner, fieldSignature);
        if (field == null || !field.getType().isPrimitive()
                || safe(primitiveValue).isEmpty()) {
            return false;
        }
        Object modeled = coerceModelValue("INT", primitiveValue,
                field.getType());
        if (modeled == UnsupportedReplayValue.INSTANCE) return false;
        try {
            field.set(owner, modeled);
            return true;
        } catch (Throwable ignored) {
            return false;
        }
    }

    /**
     * Applies a sparse associative replay model to the key used by this
     * execution, rather than to the concrete key observed in an earlier run.
     *
     * <p>The pipeline currently brackets the call site with {@code
     * pauseObservation()} / {@code resumeObservation()}, so an inactive hook
     * paid two reflective invokes into a native gate before reaching the
     * {@code activeRegion() == null} return above - and HDFS startup is {@code
     * HashMap}-intensive, so it paid them in hot startup code.</p>
     */
    public static void materializeAssociativeRead(Object container,
                                                  Object key) {
        // Before the mute, deliberately.  A thread with no admitted region has
        // no model to apply, and the pause it would take is a reflective call
        // into the VM that the answer never needed.
        ActiveRegion active = activeRegion();
        if (active == null || !(container instanceof Map<?, ?>)) return;
        beginBookkeeping();
        try {
            materializeAssociativeReadObserved(active, container, key);
        } finally {
            endBookkeeping();
        }
    }

    private static void materializeAssociativeReadObserved(
            ActiveRegion active, Object container, Object key) {
        String inputSymbol = container == null ? ""
                : safe(active.symbolizedInputPorts.get(container));
        if (inputSymbol.isEmpty()) return;
        int occurrence = active.associativeAccessOccurrences.getOrDefault(
                inputSymbol, 0) + 1;
        active.associativeAccessOccurrences.put(inputSymbol, occurrence);
        ModelAssignment selected = null;
        for (ModelAssignment candidate : active.activation.modelAssignments) {
            if (!candidate.dynamicAssociativeTarget()
                    || !candidate.inputSymbol.equals(inputSymbol)
                    || candidate.containerAccessOrdinal != occurrence
                    || active.appliedModelAssignments.contains(candidate.key)) {
                continue;
            }
            if (selected != null) {
                active.addUnresolvedOnce(inputSymbol + "#access."
                        + occurrence + ": ambiguous model assignments");
                return;
            }
            selected = candidate;
        }
        if (selected == null) return;
        Object referenceAlias = active.referenceAliasValue(
                selected, active.receiver);
        if (!selected.validContainerTarget()
                || !writeAssociativeContainerTarget(container, key,
                selected, referenceAlias)) {
            active.addUnresolvedOnce(inputSymbol + "#access."
                    + occurrence
                    + ": solver model could not be materialized");
            return;
        }
        active.recordModelAssignment(selected);
    }

    /**
     * Selects a declared access-owner carrier on the object a selected field
     * store is about to write, before the store executes.
     *
     * <p>Selecting here is the same exact-access binding as at a read - the
     * declaring object is the one this store touches, never a searched-for
     * same-named receiver - taken one bytecode earlier, so the store's own
     * {@code putfield} publishes the writer's expression as a {@code WRITE}
     * version over a pre-write initial.</p>
     */
    public static void selectFieldWriteCarrier(Object owner,
                                               String fieldSignature) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return;
        selectAccessOwnerSharedCarriers(active, owner, fieldSignature);
    }

    /** Records a stable logical source a live occurrence just entered. */
    static void observeCausalSource(String sourceKey) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        if (sourceKey != null && !sourceKey.isEmpty()) {
            active.observedSourceKeys.add(sourceKey);
        }
    }

    public static void recordFieldWrite(Object owner,
                                        String fieldSignature) {
        ActiveRegion active = activeRegion();
        if (active != null) {
            active.writtenFields.add(owner, fieldSignature);
        }
    }

    /**
     * The VM name of one fresh mint.
     *
     * <p>The phase label is the stable semantic name of the mint SITE, which
     * the evidence contract keys its rows by.  Entries past the first append
     * their entry number, so every occurrence is its own VM root while a site
     * entered once keeps exactly the name it always had.</p>
     */
    /**
     * One entry of one declared mint site.
     *
     * <p>Wave 3 selects nothing.  The frozen catalog says only WHERE a mint
     * site is; every entry of that site is its own symbolic variable, and the
     * ordinal is the per-(activation, site) entry count starting at 1.</p>
     */
    private static final class SourceSiteEntry {
        private final ConfiguredSourcePhaseContract.Occurrence phase;
        private final String siteId;
        private final int ordinal;
        /** Whether this entry maps onto a catalog row of its own. */
        private final boolean cataloged;

        private SourceSiteEntry(
                ConfiguredSourcePhaseContract.Occurrence phase,
                String siteId, int ordinal, boolean cataloged) {
            this.phase = phase;
            this.siteId = safe(siteId);
            this.ordinal = ordinal;
            this.cataloged = cataloged;
        }

        private String phaseId() {
            return phase == null ? "" : phase.phaseId();
        }

        /** Identity of this entry inside one activation. */
        private String key() {
            return siteId + "#" + ordinal;
        }
    }

    /**
     * Mints one symbol for one entry of a declared mint site.
     *
     * <p>Every occurrence of a declared field is its own symbolic variable.
     * The VM is the authority on the value: a field that already carries a
     * propagated expression keeps it - {@code SymInstance::has_sym_exp} makes
     * the mint a no-op - and the published row says {@code reused}.  Manual
     * input is only WHICH FIELDS, never which occurrence of one.</p>
     */
    public static boolean symbolizeConfiguredSourceField(
            String sourceId, Object owner, String fieldSignature) {
        ActiveRegion active = activeRegion();
        // Nothing to mint on is not a gap: the site simply was not carrying a
        // declared owner on this entry.
        if (active == null || owner == null) return false;
        SourceSiteEntry entry = active.observeConfiguredSourceEntry(
                safe(sourceId), safe(fieldSignature));
        if (entry == null) return false;
        beginBookkeeping();
        try {
            Field field = declaredInstanceField(owner, safe(fieldSignature));
            if (field == null || !field.getType().isPrimitive()) {
                active.addUnresolvedOnce(entry.key()
                        + ": configured source is not an exact primitive "
                        + "field");
                return false;
            }
            EngineApi api = engine();
            String declaringClass = field.getDeclaringClass().getName();
            String descriptor = javaTypeDescriptor(
                    field.getType().getTypeName());
            // The authority question, asked before anything is written: did
            // this value arrive carrying an expression of its own?  A VM that
            // has no answer for an unsymbolized field is answering "no", so
            // the read-out never decides the mint by throwing.
            JsonElement carried;
            try {
                carried = engineExpression(api.fieldExpression(owner,
                        declaringClass, field.getName(), descriptor,
                        field.get(owner)));
            } catch (Throwable unsymbolized) {
                carried = null;
            }
            // A constant answer (the VM folds an unsymbolized primitive to a
            // ConstExpr) is no expression of its own: only a tree that names
            // at least one non-constant node was propagated here.
            boolean reused = isSymbolicExpression(carried);
            // The application's Map re-key reads the modeled value back
            // through this same path, so the model is written first.
            ModelAssignment assignment = active.configuredSourceAssignment(
                    entry.phaseId(), safe(sourceId), safe(fieldSignature));
            if (assignment != null) {
                if (!writeModeledField(owner, safe(fieldSignature),
                        assignment, MissingValue.INSTANCE)) {
                    throw new IllegalStateException(
                            "configured source model could not be written");
                }
            }
            String symbol = "";
            if (!reused) {
                // The phase is the stable semantic source site.  Exact
                // activation identity is recorded separately in the evidence
                // row; changing the VM label per occurrence only duplicates
                // equivalent symbolic roots and complicates composition.
                String sourceOccurrence = active.occurrenceId();
                symbol = "sym__" + safe(sourceId) + "__"
                        + safe(sourceOccurrence) + "__"
                        + entry.ordinal;
                String label = SymbolicSourceEvidence.engineLabelForPhase(
                        entry.phaseId(), safe(sourceId));
                api.symbolizeExactField(owner, exactFieldSignature(field),
                        entry.ordinal <= 1 ? label
                                : label + "__" + entry.ordinal);
            }
            // A source that survives in a shared object needs a session
            // version of its exact primitive field.  Selecting after the mint
            // makes the INITIAL version carry the source expression itself;
            // a later activation can then re-select the same field and let its
            // real getfield resolve that retained writer.  This is orthogonal
            // to Map/reference propagation: the object identity says which
            // field, while this scalar carrier preserves what the field held.
            SharedStateResult sourceCarrier = selectSharedFieldCarrier(
                    owner, declaringClass, field.getName(), descriptor);
            if (!sourceCarrier.ok()) {
                active.addUnresolvedOnce(entry.key()
                        + ": configured source carrier selection failed: "
                        + sourceCarrier.reason());
                return false;
            }
            rememberPropagatedSourceField(owner, safe(fieldSignature));
            ensurePathRecordingStarted(active);
            Object value = field.get(owner);
            JsonElement expression = engineExpression(api.fieldExpression(
                    owner, declaringClass, field.getName(), descriptor,
                    value));
            active.recordConfiguredSourceMint(entry, safe(sourceId),
                    safe(fieldSignature), symbol, expression, reused);
            // The evidence ledger names one row per ENTRY.  A fresh mint is
            // a root of its own.  A reused read is one only when what it
            // found is itself a bare VM root: then the declared source is an
            // honest NAME for the symbol already on the field, and naming it
            // neither re-mints nor replaces it.  A propagated COMPOUND names
            // roots that live elsewhere, so it stays suppressed - filing it
            // would name a root that does not exist.  The mint row above is
            // published either way, carrying the expression this read found,
            // and the importer names a suppressed entry as
            // CONFIGURED_SOURCE_ROOT_NOT_MATERIALIZED: a declared source that
            // materialized no root is a named gap, never silence.
            if (!reused || SymbolicSourceEvidence.namesOneBareVmRoot(
                    safe(fieldSignature), expression)) {
                // Fail closed: a concrete write is not a materialized
                // symbolic input until the VM has accepted the exact field
                // and returned one exact root for it.  A named read says so
                // on its row, so nothing downstream reads it as a mint.
                active.recordSymbolicSource(entry.key(),
                        SymbolicSourceEvidence.event(entry.phaseId(),
                                safe(sourceId),
                                active.occurrenceId(),
                                safe(fieldSignature), expression,
                                entry.ordinal, reused, symbol));
            }
            if (assignment != null) {
                // A concrete write is not a materialized symbolic input until
                // the VM has accepted the exact field and returned its
                // expression.
                active.recordModelAssignment(assignment);
            }
            return true;
        } catch (Throwable failure) {
            active.addUnresolvedOnce(entry.key()
                    + ": exact symbolic source materialization failed: "
                    + rootCause(failure));
            return false;
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Opens this activation's branch gate from a field version retained by an
     * earlier activation.  This operation is deliberately not a source
     * declaration: an unregistered field is left concrete, and no root, phase
     * row, or model assignment is created.  The following real getfield is
     * what resolves the retained writer and supplies the branch expression.
     */
    public static boolean resumePropagatedField(
            Object owner, String fieldSignature) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return false;
        beginBookkeeping();
        try {
            Field field = declaredInstanceField(owner, safe(fieldSignature));
            if (field == null || !field.getType().isPrimitive()) {
                active.addUnresolvedOnce("propagated field is not an exact "
                        + "primitive field: " + safe(fieldSignature));
                return false;
            }
            String declaringClass = field.getDeclaringClass().getName();
            String descriptor = javaTypeDescriptor(
                    field.getType().getTypeName());
            if (!propagatedSourceField(owner, safe(fieldSignature))) {
                return false;
            }
            SharedStateResult resumed = selectSharedFieldCarrier(owner,
                    declaringClass, field.getName(), descriptor);
            if (!resumed.ok()) {
                active.addUnresolvedOnce("propagated field carrier resume "
                        + "failed: " + resumed.reason());
                return false;
            }
            ensurePathRecordingStarted(active);
            return true;
        } catch (Throwable failure) {
            active.addUnresolvedOnce("propagated field resume failed: "
                    + rootCause(failure));
            return false;
        } finally {
            endBookkeeping();
        }
    }


    /**
     * True when the expression tree names at least one minted root (a
     * SymbolExpression leaf).  A structural expression with no root in it -
     * a field access over a container-derived reference, a constant fold -
     * carries no lineage anyone declared, so the mint site mints afresh.
     */
    static boolean isSymbolicExpression(JsonElement expression) {
        if (expression == null || expression.isJsonNull()) return false;
        if (expression.isJsonArray()) {
            for (JsonElement element : expression.getAsJsonArray()) {
                if (isSymbolicExpression(element)) return true;
            }
            return false;
        }
        if (!expression.isJsonObject()) return false;
        JsonObject node = expression.getAsJsonObject();
        JsonElement type = node.get("_type");
        if (type != null && type.isJsonPrimitive()
                && "SymbolExpression".equals(type.getAsString())) {
            return true;
        }
        for (Map.Entry<String, JsonElement> member : node.entrySet()) {
            if (!"_type".equals(member.getKey())
                    && isSymbolicExpression(member.getValue())) return true;
        }
        return false;
    }

    private static JsonElement engineExpression(String serialized) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            return null;
        }
        JsonElement expression = parsed.getAsJsonObject().get("expression");
        return expression == null || expression.isJsonNull()
                ? null : expression;
    }

    private static String siteId(String method, int unitIndex) {
        return safe(method) + "#u" + unitIndex;
    }

    /** Builds one concrete branch execution witness. */
    static JsonObject concreteBranchWitness(String method, int unitIndex,
                                            boolean outcome) {
        JsonObject witness = new JsonObject();
        witness.addProperty("kind", "CONCRETE_BRANCH_EXECUTION_WITNESS_V1");
        witness.addProperty("schemaVersion", 1);
        witness.addProperty("siteId", siteId(method, unitIndex));
        witness.addProperty("method", safe(method));
        witness.addProperty("unitIndex", unitIndex);
        witness.addProperty("sourceTakenOutcome", outcome);
        return witness;
    }

    /**
     * Captures one real Jimple field-path read immediately before a normal
     * region return.
     */
    public static void recordRegionExitFieldOutput(
            String captureBindingId, Object fieldOwner, Object fieldValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesRegionExitField()) return;
        if (request.occurrenceScoped()) {
            active.nextOutputCaptureOccurrence(request);
            active.addUnresolvedOnce(request.captureBindingId()
                    + ": exact bounded heap-write occurrence requires a "
                    + "mutation-site output capture hook");
            return;
        }
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

        recordRegionExitFieldOutput(active, request, fieldOwner, fieldValue,
                occurrence);
        finishLocalOutputRelation(active, fieldValue);
    }

    /** Records one exact value at a configured protocol call. */
    public static void recordCallOutput(
            String captureBindingId, Object value) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesCallOutput()) return;
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

        JsonObject row = outputCaptureRow(request, occurrence, occurrence);
        try {
            EngineApi api = engine();
            if (containerValue(value)
                    && !snapshotOutputContainer(value, api)) {
                throw new IllegalStateException(
                        "call output is not a supported container");
            }
            JsonElement expression = engineExpression(
                    api.expression(value));
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException(
                        "custom VM returned no call-output expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": call output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            if (active.activation.communicationHandoff(
                    request.outputPort(), true) != null) {
                finishStagedCommunicationRelation(
                        active, request.outputPort(), value);
            }
        }
    }

    /** Records that a declared communication response site was reached. */
    public static void recordCommunicationEffect(String captureBindingId) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesCommunicationEffect()) return;
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

        JsonObject row = outputCaptureRow(request, occurrence, occurrence);
        row.addProperty("interactionKind", "COMMUNICATION_EFFECT");
        row.addProperty("authority", "INSTRUMENTED_INTERACTION_SITE_V1");
        // README RPC-1: stamp the exact VM export this site published, so a
        // consumer's handoff reference resolves to its producer case by the
        // export event the VM already paired it with.
        Long exported = active.exportEventByPort.get(request.outputPort());
        if (exported != null && exported.longValue() > 0L) {
            row.addProperty("exportEventId", exported.longValue());
        }
        active.outputCaptures.add(row);
        finishLocalOutputRelation(active, null);
    }

    /** Starts one definition-invocation-local occurrence stream. */
    public static void beginMutationMethodStateOutput(
            String captureBindingId) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()
                || !request.definitionInvocationScoped()) {
            return;
        }
        diag("MUTATION_ENTER", safe(captureBindingId));
        active.beginMutationMethodStateOutput(request);
    }

    /** Gives a selected arithmetic Atomic RMW a primitive pre-state shadow. */
    public static void prepareAtomicMutationStateOutput(
            String captureBindingId, Object receiver) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()) return;
        String valueField = request.atomicArithmeticValueFieldSignature();
        if (valueField.isEmpty() || receiver == null
                || !active.claimAtomicMutationPreparation(
                request, receiver)) return;

        try {
            if (declaredInstanceField(receiver, valueField) == null) {
                throw new IllegalStateException(
                        "atomic receiver has no exact value field");
            }
            EngineApi api = engine();
            api.observeExactPrimitiveField(receiver, valueField);
            ensurePathRecordingStarted(active);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": atomic mutation pre-state observation failed: "
                    + rootCause(throwable));
        }
    }

    /**
     * Selects the exact mutator occurrence whose receiver will be captured
     * when the enclosing mutation method completes normally.
     */
    public static void recordMutationStateOutput(
            String captureBindingId, Object container) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()) return;
        MutationCaptureIndex index =
                active.nextMutationOutputCaptureOccurrence(request);
        if (index == null) return;
        diag("MUTATION_SITE", safe(captureBindingId)
                + " occ=" + index.selection + " version=" + index.version);
        if (!active.boundedOutputVersionSlot(request, index.version)) {
            return;
        }

        active.deferMutationStateOutput(request, container, index);
    }

    /** Emits a selected mutation receiver at its method's normal exit. */
    public static void recordMutationMethodExitStateOutput(
            String captureBindingId) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()) return;
        PendingMutationCapture pending =
                active.takeMutationStateOutput(request);
        diag("MUTATION_EXIT", safe(captureBindingId)
                + " pending=" + (pending != null));
        if (pending == null) return;

        JsonObject row = outputCaptureRow(request, pending.occurrence,
                pending.versionOrdinal);
        EngineApi api = engine();
        try {
            JsonElement expression;
            if (!request.atomicArithmeticValueFieldSignature().isEmpty()) {
                expression = atomicMutationValueExpression(
                        request, pending.container, api);
            } else {
                if (!snapshotOutputContainer(pending.container, api)) {
                    throw new IllegalStateException(
                            "mutation receiver is not a supported container");
                }
                expression = engineExpression(
                        api.expression(pending.container));
            }
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException(
                        "custom VM returned no mutation-state expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": mutation-state output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            finishLocalOutputRelation(active, pending.container);
        }
    }

    /** Captures one direct instance-field definition at the exact putfield. */
    public static void recordFieldWriteStateOutput(
            String captureBindingId, Object fieldOwner, Object fieldValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.demandedCapture(
                captureBindingId);
        if (request == null || !request.capturesFieldWriteState()) return;
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

        JsonObject row = outputCaptureRow(request, occurrence, occurrence);
        try {
            EngineApi api = engine();
            JsonElement expression;
            DeclaredField field = null;
            if (containerValue(fieldValue)) {
                if (!snapshotOutputContainer(fieldValue, api)) {
                    throw new IllegalStateException(
                            "field-write value is not a supported container");
                }
                expression = engineExpression(api.expression(fieldValue));
            } else {
                field = FieldPathSpec.declaredField(
                        request.fieldSignature());
                if (field == null) {
                    throw new IllegalStateException(
                            "field-write capture has no exact field");
                }
                expression = engineExpression(api.fieldExpression(
                        fieldOwner, field.owner(), field.name(),
                        javaTypeDescriptor(field.type()), fieldValue));
            }
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException(
                        "custom VM returned no field-write expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": field-write output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            finishLocalOutputRelation(active, fieldValue);
        }
    }

    private static JsonObject outputCaptureRow(OutputCaptureSpec request,
            int occurrence, int versionOrdinal) {
        JsonObject row = new JsonObject();
        row.addProperty("captureBindingId", request.captureBindingId());
        row.addProperty("outputSiteId", request.outputSiteId());
        row.addProperty("outputOccurrence", occurrence);
        row.addProperty("outputVersionOrdinal", versionOrdinal);
        return row;
    }

    private static void recordRegionExitFieldOutput(
            ActiveRegion active, OutputCaptureSpec request,
            Object fieldOwner, Object fieldValue, int occurrence) {

        JsonObject row = outputCaptureRow(request, occurrence, occurrence);

        EngineApi api = engine();
        try {
            JsonElement expression;
            DeclaredField declared = null;
            if (containerValue(fieldValue)) {
                // A tracked container relation may still be rooted at an
                // unconstrained STATE.
                snapshotOutputContainer(fieldValue, api);
                expression = engineExpression(api.expression(fieldValue));
            } else {
                declared = FieldPathSpec.declaredField(
                        request.fieldSignature());
                if (declared == null) {
                    throw new IllegalStateException(
                            "normal-exit capture has no exact field");
                }
                expression = engineExpression(api.fieldExpression(
                        fieldOwner, declared.owner(), declared.name(),
                        javaTypeDescriptor(declared.type()), fieldValue));
            }
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException("custom VM returned no "
                        + "normal-exit field expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": normal-exit field capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
        }
    }

    private static boolean exactOutputBoundaryCapture(
            OutputCaptureSpec request) {
        return request != null && (request.capturesCallOutput()
                || request.capturesCommunicationEffect()
                || request.capturesFieldWriteState()
                || request.capturesMutationState());
    }

    /** Admits an observation of the recorded output relation. */
    private static boolean successfulExactOutputCapture(
            OutputCaptureSpec request, JsonObject capture) {
        if (request == null || capture == null
                || !request.captureBindingId().equals(
                string(capture, "captureBindingId"))) {
            return false;
        }
        if (request.capturesCommunicationEffect()) {
            if (!"COMMUNICATION_EFFECT".equals(
                    string(capture, "interactionKind"))
                    || !"INSTRUMENTED_INTERACTION_SITE_V1".equals(
                    string(capture, "authority"))) {
                return false;
            }
        } else {
            JsonElement relation = capture.get("expression");
            if (relation == null || relation.isJsonNull()) return false;
        }
        return !request.occurrenceScoped()
                || request.outputSiteId().equals(
                string(capture, "outputSiteId"))
                && integer(capture, "outputOccurrence", -1) >= 1;
    }

    private static boolean completeExactOutputBoundary(
            boolean capturesOutputRelation,
            List<OutputCaptureSpec> requests,
            List<JsonObject> captures) {
        if (!capturesOutputRelation || requests == null || requests.isEmpty()) {
            return false;
        }
        Set<String> requestedBindings = new LinkedHashSet<>();
        for (OutputCaptureSpec request : requests) {
            if (!exactOutputBoundaryCapture(request)
                    || !requestedBindings.add(request.captureBindingId())) {
                return false;
            }
            int successfulRows = 0;
            for (JsonObject capture : captures) {
                if (successfulExactOutputCapture(request, capture)) {
                    successfulRows++;
                }
            }
            // One admitted observation completes the boundary.
            if (successfulRows < 1) return false;
        }
        return true;
    }

    /**
     * The demanded output boundaries this occurrence did not observe, named.
     *
     * <p>A boundary no activation can ever reach and one this activation
     * merely missed produce the same generic refusal otherwise, and they need
     * opposite answers: the first is a plan that demands an output the
     * workload never produces -- HDFS-11741's monitor region demands the
     * {@code needKeyUpdate} write of a per-rotation walk the workload runs
     * zero bodies of -- and the second is simply the next candidate's turn.
     * </p>
     */
    private static String unobservedOutputBoundaries(
            RuntimeTask task, List<JsonObject> captures) {
        StringBuilder missing = new StringBuilder();
        int named = 0;
        for (OutputCaptureSpec request : task.outputCaptures) {
            boolean observed = false;
            for (JsonObject capture : captures) {
                if (successfulExactOutputCapture(request, capture)) {
                    observed = true;
                    break;
                }
            }
            if (observed) continue;
            named++;
            if (named > 4) continue;
            if (missing.length() > 0) missing.append(", ");
            missing.append(request.captureBindingId()).append(" at ")
                    .append(request.outputSiteId());
        }
        if (named > 4) {
            missing.append(" and ").append(named - 4).append(" more");
        }
        return named == 0 ? "no boundary" : missing.toString();
    }

    /**
     * Whether this activation produced every output relation its task demands.
     *
     * <p>README {@code OCC-1}/{@code TERM-1}: the demanded boundary decides
     * what a published occurrence <em>is</em>, not whether it is published.
     * An activation that missed part of it is still an occurrence of the
     * address, and the row says so rather than disappearing.</p>
     */
    private static boolean relationallyComplete(
            RuntimeTask task, List<JsonObject> captures) {
        if (task == null || !task.capturesOutputRelation
                || task.outputCaptures.isEmpty()) {
            return true;
        }
        return completeExactOutputBoundary(task.capturesOutputRelation,
                task.outputCaptures, captures);
    }

    /**
     * Whether this activation reached the target its task exists to observe.
     *
     * <p>A {@code TARGET_REACH_CLOSURE} address is answered only by the
     * activation that took the annotated failure, so the SASL occurrence the
     * formula selects is one that read {@code allKeys} after the removal that
     * makes the read fail -- never a normal read of the initial version.
     * Normal exits still publish, marked {@code targetReached:false}.</p>
     */
    private static boolean targetReachedByActivation(ActiveRegion active) {
        RuntimeTask task = active.activation;
        if (task.declaresTargetBranch()) {
            return task.reachedRequiredTargetOutcome(active.targetReach);
        }
        // A target-reach closure with no declared branch event is answered by
        // the annotated target's own throw terminal.
        return task.capturesTargetReach
                && "THROW".equals(safe(active.exitKind))
                && !safe(active.exceptionType).isEmpty();
    }

    private static boolean incompleteRelationOnlyBoundary(
            RuntimeTask task, List<JsonObject> captures, String exitKind) {
        if (task == null || !"NORMAL".equals(exitKind)
                || !task.relationOnlySeed()
                || task.outputCaptures.isEmpty()) {
            return false;
        }
        for (OutputCaptureSpec request : task.outputCaptures) {
            if (!exactOutputBoundaryCapture(request)) return false;
        }
        return !completeExactOutputBoundary(task.capturesOutputRelation,
                task.outputCaptures, captures);
    }




    private static boolean snapshotOutputContainer(
            Object value, EngineApi api)
            throws Exception {
        requireCompleteContainerSnapshotCapacity(value);
        Object[] keys = null;
        Object[] values;
        int kind;
        if (value != null && value.getClass().isArray()) {
            int length = Array.getLength(value);
            values = new Object[length];
            for (int index = 0; index < length; index++) {
                values[index] = Array.get(value, index);
            }
            kind = SNAPSHOT_ARRAY;
        } else if (value instanceof Map<?, ?>) {
            List<Object> snapshotKeys = new ArrayList<>();
            List<Object> snapshotValues = new ArrayList<>();
            for (Map.Entry<?, ?> entry
                    : ((Map<?, ?>) value).entrySet()) {
                snapshotKeys.add(entry.getKey());
                snapshotValues.add(entry.getValue());
            }
            keys = snapshotKeys.toArray();
            values = snapshotValues.toArray();
            kind = SNAPSHOT_MAP;
        } else if (value instanceof Set<?>) {
            keys = ((Set<?>) value).toArray();
            values = new Object[keys.length];
            kind = SNAPSHOT_SET;
        } else if (value instanceof Collection<?>) {
            values = ((Collection<?>) value).toArray();
            kind = SNAPSHOT_INDEXED;
        } else {
            return false;
        }
        requireContainerSnapshotCapacity(values.length,
                "normal-exit container");
        if (!api.snapshotContainer(value, keys, values, kind)) {
            throw new IllegalStateException(
                    "custom VM rejected normal-exit container snapshot");
        }
        return true;
    }

    /** Reads the exact primitive state written by a supported Atomic RMW. */
    private static JsonElement atomicMutationValueExpression(
            OutputCaptureSpec request, Object receiver, EngineApi api)
            throws Exception {
        String fieldSignature = request
                .atomicArithmeticValueFieldSignature();
        DeclaredField declared = FieldPathSpec.declaredField(fieldSignature);
        Field field = declaredInstanceField(receiver, fieldSignature);
        if (declared == null || field == null) {
            throw new IllegalStateException(
                    "atomic receiver has no exact value field");
        }
        JsonElement encoded = parseJson(api.fieldExpression(
                receiver, declared.owner(), declared.name(),
                javaTypeDescriptor(declared.type()), field.get(receiver)));
        if (!encoded.isJsonObject()
                || !bool(encoded.getAsJsonObject(), "symbolic", false)
                || !"VM_EXACT_FIELD_SHADOW_V1".equals(string(
                encoded.getAsJsonObject(), "expressionAuthority"))) {
            throw new IllegalStateException(
                    "custom VM returned no symbolic Atomic value field");
        }
        JsonElement expression = encoded.getAsJsonObject().get("expression");
        return expression == null || expression.isJsonNull()
                ? null : expression;
    }

    /**
     * A complete snapshot has no failure-relevance proof with which to choose
     * sparse cells.
     */
    static void requireCompleteContainerSnapshotCapacity(Object value) {
        int size;
        if (value != null && value.getClass().isArray()) {
            size = Array.getLength(value);
        } else if (value instanceof Map<?, ?>) {
            size = ((Map<?, ?>) value).size();
        } else if (value instanceof Collection<?>) {
            size = ((Collection<?>) value).size();
        } else {
            return;
        }
        requireContainerSnapshotCapacity(size,
                "complete symbolic container");
    }

    private static void requireContainerSnapshotCapacity(
            int size, String description) {
        if (size > LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY) {
            throw new IllegalStateException("BOUND_INSUFFICIENT: "
                    + description + " has " + size
                    + " cells; symbolic snapshot capacity is "
                    + LoopBoundPolicy.SYMBOLIC_CONTAINER_SNAPSHOT_CAPACITY);
        }
    }

    /** Result of one VM symbolic-expression export or attach. */
    public static final class HandoffResult {
        private final String stage;
        private final int status;
        private final long handle;
        private final JsonObject record;

        private HandoffResult(String stage, int status, long handle,
                              JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.handle = handle;
            this.record = record;
        }

        public boolean ok() {
            return status == RpcExpressionHandoff.OK;
        }

        /** Numeric VM/runtime status; zero is the only success. */
        public int status() {
            return status;
        }

        /** Named reason for a failure; empty for a successful call. */
        public String reason() {
            return RpcExpressionHandoff.reason(status);
        }

        public long handle() {
            return handle;
        }

        /**
         * The VM ledger event of this exact attach.
         *
         * <p>README {@code RPC-1}: the second endpoint of the {@code
         * VALUE_HANDOFF} edge.</p>
         */
        @Override
        public String toString() {
            return "HandoffResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " handle=" + handle + "]";
        }
    }

    private static HandoffResult exportSymbolicLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor, String declaredPortId) {
        HandoffResult result;
        beginBookkeeping();
        try {
            result = exportLeaf(owner, declaringClass, fieldName, descriptor,
                    declaredPortId);
        } finally {
            endBookkeeping();
        }
        return result;
    }

    private static HandoffResult exportLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor, String declaredPortId) {
        String missing = missingFieldMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (!missing.isEmpty()) {
            return record(failed(RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.MISSING_METADATA, 0L, missing));
        }
        EngineApi api = engine();
        long handle;
        // README RPC-1: the VM reports the export's own ledger event here,
        // so the producer's interaction row can name the exact export it
        // published instead of leaving the Composer to count port
        // observations for it.
        long[] exportEvent = new long[1];
        try {
            handle = api.exportExpression(owner, declaringClass, fieldName,
                    descriptor, exportEvent);
        } catch (Throwable throwable) {
            return record(failed(RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.INVOCATION_FAILED, 0L,
                    rootCause(throwable)));
        }
        if (handle <= 0L) {
            int status = exportStatus(handle);
            HandoffResult result = failed(
                    RpcExpressionHandoff.STAGE_EXPORT, status, 0L,
                    "exportExpression returned " + handle);
            if (status == RpcExpressionHandoff.NOT_SYMBOLIC) return result;
            return record(result);
        }
        JsonObject exported = new JsonObject();
        exported.addProperty("exportEventId", exportEvent[0]);
        HandoffResult result = new HandoffResult(
                RpcExpressionHandoff.STAGE_EXPORT,
                RpcExpressionHandoff.OK, handle, exported);
        record(result);
        ActiveRegion exporting = activeRegion();
        if (exportEvent[0] > 0L && !safe(declaredPortId).isEmpty()
                && exporting != null) {
            exporting.exportEventByPort.put(safe(declaredPortId),
                    Long.valueOf(exportEvent[0]));
        }
        return result;
    }

    /**
     * Attaches one receive whose destination this occurrence's plan declares
     * as a communication port.
     */
    private static HandoffResult attachDeclaredCommunicationExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, SymbolicMessageEnvelope.Entry carried,
            CommunicationHandoffSpec declared) {
        beginBookkeeping();
        try {
            HandoffResult result = record(attach(owner, declaringClass,
                    fieldName, descriptor, carried.handle()));
            if (result.ok()) {
                recordVmHandoffEvent(declared, result, owner, declaringClass,
                        fieldName, descriptor, carried.producerTaskId(),
                        carried.producerOccurrenceId());
            }
            return result;
        } finally {
            endBookkeeping();
        }
    }

    /** The one instance field a declared communication port crosses on. */
    public static final class HandoffLeafCarrier {
        public boolean z;
        public byte b;
        public short s;
        public char c;
        public int i;
        public long j;
        public float f;
        public double d;
        public Object o;
    }

    /** Symbolic demand of a field a configured source mints per occurrence. */
    private static final String CONFIGURED_SOURCE_FIELD_DEMAND =
            "CONFIGURED_SYMBOLIC_SOURCE_FIELD_OWNED";

    private static final String CARRIER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                    + "$HandoffLeafCarrier";
    // ------------------------------------------------------------------
    // Communication message flow
    // ------------------------------------------------------------------

    /** Stages one VM handle and its producer on the next outbound message. */
    private static boolean stageMessageExpression(String portId,
                                                  long handle) {
        ActiveRegion active = activeRegion();
        boolean staged = active != null && SymbolicMessageEnvelope.stage(
                portId, handle, active.activation.taskId,
                active.occurrenceId());
        if (staged) active.stagedCommunicationPorts.add(portId);
        return staged;
    }

    /** Closes a producer once its complete relation is resident on the wire. */
    private static void finishStagedCommunicationRelation(
            ActiveRegion active, String portId, Object output) {
        if (active != null && active.activation.relationOnlySeed()
                && active.stagedCommunicationPorts.contains(portId)
                && active.demandedOutputRelationComplete()) {
            finish(active.token, "NORMAL", "", output);
        }
    }

    /** Closes a producer once every exact local output has been captured. */
    private static void finishLocalOutputRelation(
            ActiveRegion active, Object output) {
        if (active != null && active.activation.relationOnlySeed()
                && active.demandedOutputRelationComplete()) {
            finish(active.token, "NORMAL", "", output);
        }
    }

    // ------------------------------------------------------------------
    // Declared communication ports
    // ------------------------------------------------------------------

    /**
     * Exports the live expression of one declared communication port.
     *
     * <p>The value arrives on a {@link HandoffLeafCarrier} the
     * <em>instrumented frame</em> allocated and stored into, because a broker
     * leaf is an exact instance field while a cut argument is a local - and
     * because only the application's own frame propagates a value's expression
     * into a field.</p>
     */
    public static void exportCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        ActiveRegion active = activeRegion();
        CommunicationHandoffSpec site;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, true);
        } finally {
            endBookkeeping();
        }
        if (site == null || carrier == null) return;
        HandoffResult result = exportSymbolicLeaf(carrier, CARRIER_CLASS,
                field, descriptor, site.portId());
        // A concrete leaf is still a leaf the message carried.
        if (!result.ok()
                && result.status != RpcExpressionHandoff.NOT_SYMBOLIC) {
            return;
        }
        if (!stageMessageExpression(site.portId(),
                result.ok() ? result.handle() : 0L)) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.MISSING_METADATA,
                    result.ok() ? result.handle() : 0L,
                    "communication leaf could not enter the message: "
                            + site.portId()));
        } else {
            finishStagedCommunicationRelation(active, site.portId(), carrier);
        }
    }

    /**
     * Attaches the exported expression of one declared communication port.
     *
     * <p>After a successful attach the carrier leaf <em>denotes the sender's
     * expression</em>; the instrumented frame reads it straight back into its
     * own local, so the receiver's later arithmetic, branches and exports
     * build on that term directly.</p>
     */
    public static void attachCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        CommunicationHandoffSpec site;
        SymbolicMessageEnvelope.Entry carried;
        long handle;
        boolean leafCarried;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, false);
            carried = site == null ? null
                    : SymbolicMessageEnvelope.take(site.portId());
            leafCarried = carried != null && carried.present();
            handle = carried == null ? 0L : carried.handle();
        } finally {
            endBookkeeping();
        }
        if (site == null) return;
        if (carrier == null) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, handle,
                    "required communication port has no carrier: "
                            + site.portId()));
            return;
        }
        if (leafCarried && handle == 0L) {
            ActiveRegion active = activeRegion();
            if (active != null && acceptCommunicationEndpoint(active, site,
                    carried.producerTaskId(),
                    carried.producerOccurrenceId())) {
                active.observedInputSlots.add(site.portId());
                active.symbolized.remove(site.portId());
            }
            return;
        }
        // The native VM executes one selected region per workload instance.
        // A singleton consumer replay therefore sees the concrete message but
        // no live handle from the producer's separate replay.  Its frozen
        // exact wire binding is still the authority for this relation-bound
        // input; composition later equates it with the producer's output.
        ActiveRegion active = activeRegion();
        String plannedProducer = active == null ? ""
                : active.activation.attachProducerOccurrence(site.portId());
        if (!leafCarried && handle == 0L && !plannedProducer.isEmpty()
                && acceptCommunicationEndpoint(active, site, "",
                plannedProducer)) {
            active.observedInputSlots.add(site.portId());
            active.symbolized.remove(site.portId());
            return;
        }
        if (handle <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.UNKNOWN_HANDLE, 0L,
                    "required communication port carried no live VM handle: "
                            + site.portId()));
            return;
        }
        attachDeclaredCommunicationExpression(carrier, CARRIER_CLASS, field,
                descriptor, carried, site);
    }

    /** The declared site of {@code portId} in this occurrence's plan. */
    private static CommunicationHandoffSpec communicationHandoffSite(
            String portId, boolean exporting) {
        ActiveRegion active = activeRegion();
        if (active == null || safe(portId).isEmpty()) return null;
        return active.activation.communicationHandoff(portId, exporting);
    }

    /**
     * Files one case-local reference into the VM's own handoff ledger and the
     * exact expression now held by the attached destination.
     */
    private static void recordVmHandoffEvent(CommunicationHandoffSpec site,
                                             HandoffResult result,
                                             Object owner,
                                             String declaringClass,
                                             String fieldName,
                                             String descriptor,
                                             String producerTaskId,
                                             String producerOccurrenceId) {
        ActiveRegion active = activeRegion();
        if (active == null || site == null) return;
        if (safe(producerTaskId).isEmpty()
                || safe(producerOccurrenceId).isEmpty()) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, result.handle(),
                    "attached leaf carried no exact producer execution"));
            return;
        }
        long exportEvent = result.ok()
                ? longInteger(result.record, "exportEventId", 0L) : 0L;
        if (exportEvent <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "attached leaf named no VM export event"));
            return;
        }
        // README RPC-1: the reference carries both endpoints of the edge.
        long attachEvent = result.ok()
                ? longInteger(result.record, "attachEventId", 0L) : 0L;
        if (attachEvent <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "attached leaf named no VM attach event"));
            return;
        }
        JsonElement expression;
        try {
            Field storage = declaredInstanceField(owner, declaringClass,
                    fieldName, descriptor);
            if (storage == null) {
                recordHandoffGap(RpcExpressionHandoff.gap(
                        RpcExpressionHandoff.STAGE_ATTACH,
                        RpcExpressionHandoff.MISSING_METADATA,
                        result.handle(),
                        "attached leaf has no exact destination storage"));
                return;
            }
            Object value = storage.get(owner);
            EngineApi api = engine();
            expression = containerValue(value)
                    ? engineExpression(api.expression(value))
                    : engineExpression(api.fieldExpression(owner,
                    declaringClass, fieldName, descriptor, value));
        } catch (Throwable failure) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.INVOCATION_FAILED, result.handle(),
                    "attached destination expression read-out failed: "
                            + rootCause(failure)));
            return;
        }
        if (expression == null || expression.isJsonNull()) {
            // C2: the destination carried no propagated lineage.  A read with
            // no lineage is an unconstrained variable this occurrence names,
            // not a hole in the evidence, so the edge carries a free symbol
            // instead of a gap.
            expression = mintFreeAttachedExpression(active, site, owner,
                    declaringClass, fieldName, descriptor);
        }
        if (expression == null || expression.isJsonNull()) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "custom VM returned no attached destination expression"));
            return;
        }
        acceptVmHandoffExpression(active, site, exportEvent, attachEvent,
                expression, producerTaskId, producerOccurrenceId);
    }

    /**
     * Mints one free symbol on an attached destination that carried none.
     *
     * <p>Returns {@code null} when the read cannot be symbolized at all - no
     * owner, or a Java type the VM has no exact field shadow for - which is
     * the one case that stays an unresolved gap.</p>
     */
    private static JsonElement mintFreeAttachedExpression(
            ActiveRegion active, CommunicationHandoffSpec site, Object owner,
            String declaringClass, String fieldName, String descriptor) {
        if (active == null || owner == null) return null;
        try {
            Field storage = declaredInstanceField(owner, declaringClass,
                    fieldName, descriptor);
            if (storage == null || !storage.getType().isPrimitive()) {
                return null;
            }
            EngineApi api = engine();
            int ordinal = active.nextFreeSymbolOrdinal(site.siteId());
            String occurrenceId = active.occurrenceId();
            String symbol = "free__" + safe(site.siteId()) + "__"
                    + occurrenceId + "__" + ordinal;
            // A Soot site id carries spaces, brackets, colons and parens,
            // none of which survive into an SMT-LIB simple symbol, so the VM
            // name is the hashed identity the mint side already uses.
            String label = "FREE." + CanonicalJson.sha256(
                    safe(site.siteId()) + "\n" + occurrenceId);
            String vmSymbol = ordinal <= 1 ? label : label + "__" + ordinal;
            api.symbolizeExactField(owner, exactFieldSignature(storage),
                    vmSymbol);
            ensurePathRecordingStarted(active);
            JsonElement expression = engineExpression(api.fieldExpression(
                    owner, declaringClass, fieldName, descriptor,
                    storage.get(owner)));
            if (expression == null || expression.isJsonNull()) return null;
            active.recordFreeSymbol(symbol, vmSymbol, site.siteId(), ordinal,
                    descriptor, "no recorded lineage at communication attach");
            return expression;
        } catch (Throwable ignored) {
            return null;
        }
    }

    /** Commits one fully validated receiver-side handoff to the active case. */
    private static void acceptVmHandoffExpression(
            ActiveRegion active, CommunicationHandoffSpec site,
            long exportEvent, long attachEvent, JsonElement expression,
            String producerTaskId, String producerOccurrenceId) {
        if (!acceptCommunicationEndpoint(active, site, producerTaskId,
                producerOccurrenceId)) return;
        active.vmHandoffEvents.add(VmHandoffEvidence.event(site.portId(),
                exportEvent, attachEvent, expression, producerTaskId,
                producerOccurrenceId));
        // A VM-attached expression is an exact selected symbolic input just as
        // much as one created by a local symbolize hook.
        ensurePathRecordingStarted(active);
        // The receiving local now denotes the sender's expression, so any
        // fresh root the entry materialization minted for this same port is
        // dead code that only a second authority could still read.
        // README SMT-1 allows one authority per selected input, and after a
        // successful attach that authority is this edge.
        active.observedInputSlots.add(site.portId());
        active.symbolized.remove(site.portId());
    }

    /** Checks that one message entry came from its planned producer. */
    private static boolean acceptCommunicationEndpoint(
            ActiveRegion active, CommunicationHandoffSpec site,
            String producerTaskId, String producerOccurrenceId) {
        String expectedProducer = active.activation
                .attachProducerOccurrence(site.portId());
        String actualProducer = PathObservation.plannedOccurrenceOf(
                producerOccurrenceId);
        if (!expectedProducer.isEmpty()
                && !expectedProducer.equals(actualProducer)) {
            diag("ATTACH_ENDPOINT_PRODUCER_MISMATCH", "task="
                    + safe(active.activation.taskId) + " port="
                    + site.portId() + " expected=" + expectedProducer
                    + " actual=" + actualProducer);
            return false;
        }
        return true;
    }

    /** Files one handoff gap with the active region, when there is one. */
    private static void recordHandoffGap(JsonObject gap) {
        ActiveRegion active = activeRegion();
        if (active != null) active.rpcHandoffGaps.add(gap);
        diag(RpcExpressionHandoff.GAP_KIND, String.valueOf(gap));
    }

    private static HandoffResult attach(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long handle) {
        String missing = missingFieldMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (handle <= 0L) {
            missing = firstNonBlank(missing,
                    "attach needs a positive handle");
        }
        if (!missing.isEmpty()) {
            return failed(RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, handle, missing);
        }
        EngineApi api = engine();
        long exportEventId;
        // README RPC-1: both endpoints of the VALUE_HANDOFF edge leave the VM
        // together.
        long[] attachEvent = new long[1];
        try {
            exportEventId = api.attachExpression(owner, declaringClass,
                    fieldName, descriptor, handle, attachEvent);
        } catch (Throwable throwable) {
            return failed(RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.INVOCATION_FAILED, handle,
                    rootCause(throwable));
        }
        if (exportEventId <= 0L) {
            int status = exportStatus(exportEventId);
            return failed(RpcExpressionHandoff.STAGE_ATTACH, status, handle,
                    "attachExpression returned " + exportEventId);
        }
        if (attachEvent[0] <= 0L) {
            // A VM that accepted the attach but named no attach event has told
            // us half an edge.
            return failed(RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, handle,
                    "attachExpression named no attach event for export "
                            + exportEventId);
        }
        JsonObject success = new JsonObject();
        success.addProperty("exportEventId", exportEventId);
        success.addProperty("attachEventId", attachEvent[0]);
        return new HandoffResult(RpcExpressionHandoff.STAGE_ATTACH,
                RpcExpressionHandoff.OK, handle, success);
    }

    private static String missingFieldMetadata(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        if (owner == null) return "handoff leaf has no owner instance";
        if (firstNonBlank(declaringClass).isEmpty()
                || firstNonBlank(fieldName).isEmpty()
                || firstNonBlank(descriptor).isEmpty()) {
            return "handoff leaf has no exact declaring class, field name "
                    + "and type descriptor";
        }
        return "";
    }

    /** Maps a non-positive {@code exportExpression} answer onto a status. */
    private static int exportStatus(long handle) {
        if (handle == 0L || handle < Integer.MIN_VALUE) {
            return RpcExpressionHandoff.MALFORMED_RESULT;
        }
        return (int) handle;
    }

    private static HandoffResult failed(String stage, int status, long handle,
                                        String detail) {
        return new HandoffResult(stage, status, handle,
                RpcExpressionHandoff.gap(stage, status, handle, detail));
    }

    /**
     * Files failed calls with the active region and reports every outcome to
     * the diagnostic trace.
     */
    private static HandoffResult record(HandoffResult result) {
        ActiveRegion active = activeRegion();
        if (active != null && !result.ok()) {
            active.rpcHandoffGaps.add(result.record);
        }
        if (!result.ok()) {
            diag(RpcExpressionHandoff.GAP_KIND, result.toString());
        }
        return result;
    }

    private static final Object RUN_TOTALS_LOCK = new Object();
    private static boolean runTotalsHookRegistered;

    /**
     * Registers the one shutdown hook that publishes what only the end of a
     * run can state.
     */
    static void registerRunTotalsHook() {
        synchronized (RUN_TOTALS_LOCK) {
            if (runTotalsHookRegistered) return;
            runTotalsHookRegistered = true;
            try {
                Runtime.getRuntime().addShutdownHook(new Thread(
                        new Runnable() {
                            @Override
                            public void run() {
                                publishRunTotals();
                            }
                        }, "concolic-run-totals"));
            } catch (IllegalStateException shuttingDown) {
                // A run already shutting down cannot register one.  The
                // workload's own outcome is never replaced by this.
            }
        }
    }

    /**
     * Publishes what only the end of a run can state: every selected address
     * that nothing answered, and this run's handoff aggregates.
     */
    static void publishRunTotals() {
        configuration().publishUnansweredAddresses();
    }

    /** Outcome of one recorded shared-state evidence call. */
    public static final class SharedStateResult {
        private final String stage;
        private final int status;
        private final String locationKey;
        private final long initialFieldVersionId;
        private final JsonObject envelope;
        private final JsonObject record;

        private SharedStateResult(String stage, int status, String locationKey,
                                  long initialFieldVersionId,
                                  JsonObject envelope, JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.locationKey = locationKey;
            this.initialFieldVersionId = initialFieldVersionId;
            this.envelope = envelope;
            this.record = record;
        }

        public boolean ok() {
            return status == SharedStateEvidence.OK;
        }

        public int status() {
            return status;
        }

        /** Named reason for a failure; empty for an admitted answer. */
        public String reason() {
            return SharedStateEvidence.reason(status);
        }

        public String stage() {
            return stage;
        }

        /** The VM's own (owner, slot, kind) identity; empty before capture. */
        public String locationKey() {
            return locationKey;
        }

        /** The INITIAL version published by a fresh selection. */
        public long initialFieldVersionId() {
            return initialFieldVersionId;
        }

        /** The raw VM envelope; empty when none was returned. */
        public JsonObject envelope() {
            return envelope == null ? new JsonObject() : envelope.deepCopy();
        }

        /** Admitted evidence row; empty after a failure or a selection. */
        public JsonObject record() {
            return ok() ? record.deepCopy() : new JsonObject();
        }

        /** Named coverage gap for a failure; empty after a success. */
        public JsonObject gap() {
            return ok() ? new JsonObject() : record.deepCopy();
        }

        @Override
        public String toString() {
            return "SharedStateResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " location=" + locationKey + "]";
        }
    }

    /**
     * Selects one exact instance or static field as a symbolic carrier, so
     * every later write to it publishes a version and every later read of it
     * resolves to an exact writer or to an explicitly guarded choice.
     */
    public static SharedStateResult selectSharedFieldCarrier(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        beginBookkeeping();
        try {
            return selectedCarrier(SharedCarrier.field(owner, declaringClass,
                    fieldName, descriptor));
        } finally {
            endBookkeeping();
        }
    }

    /** Selects one element of a fixed-shape array as a symbolic carrier. */
    public static SharedStateResult selectSharedElementCarrier(Object array,
                                                               int index) {
        beginBookkeeping();
        try {
            return selectedCarrier(SharedCarrier.element(array, index));
        } finally {
            endBookkeeping();
        }
    }

    /** Selects one map as a symbolic carrier of its own whole state. */
    public static SharedStateResult selectSharedMapCarrier(
            Object map, String declaringClass, String fieldName,
            String descriptor) {
        beginBookkeeping();
        try {
            return selectedCarrier(SharedCarrier.map(map, declaringClass,
                    fieldName, descriptor));
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Selects one carrier of any shape, publishing the same select-stage
     * evidence for a refused shape, an unavailable VM, a failed invoke and a
     * negative answer whichever shape asked.
     */
    private static SharedStateResult selectedCarrier(SharedCarrier carrier) {
        ActiveRegion active = activeRegion();
        carrier.bindPlannedReceiver(active == null
                ? null : active.activation);
        String missing = carrier.missing();
        if (!missing.isEmpty()) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "", missing),
                    null, active);
        }
        EngineApi api = engine();
        long initial;
        try {
            initial = carrier.select(api);
        } catch (Throwable throwable) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, active);
        }
        // The VM returns zero when this exact location is already selected in
        // the current session.  Selection is idempotent: this activation must
        // still retain the carrier so it can read the shared version ledger.
        if (initial < 0L) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    initial < Integer.MIN_VALUE
                            ? SharedStateEvidence.MALFORMED_ENVELOPE
                            : (int) initial, "",
                    carrier.selectApi() + " returned " + initial), null,
                    active);
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", initial, new JsonObject(),
                        new JsonObject()),
                carrier, active);
    }

    /** {@link #selectSharedMapCarrier} with no declared holding field. */
    public static SharedStateResult selectSharedMapCarrier(Object map) {
        return selectSharedMapCarrier(map, "", "", "");
    }

    /**
     * Reads back the whole-map states published for one selected map, together
     * with how every query of it was resolved.
     */
    public static SharedStateResult captureSharedMapVersions(Object map) {
        return capturedVersions(SharedCarrier.map(map, "", "", ""),
                activeRegion());
    }

    /**
     * Reads back the versions published for one selected field, together with
     * how every read of it was resolved.
     */
    public static SharedStateResult captureSharedFieldVersions(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        return capturedVersions(SharedCarrier.field(owner, declaringClass,
                fieldName, descriptor), activeRegion());
    }

    /** {@link #captureSharedFieldVersions} for one selected array element. */
    public static SharedStateResult captureSharedElementVersions(
            Object array, int index) {
        return capturedVersions(SharedCarrier.element(array, index),
                activeRegion());
    }

    /**
     * One carrier's published versions and the resolution of every access to
     * it.  The read-out is memoized per occurrence, so a second capture of the
     * same carrier never re-enters the VM.
     */
    private static SharedStateResult capturedVersions(SharedCarrier carrier,
                                                      ActiveRegion active) {
        beginBookkeeping();
        try {
            carrier.bindPlannedReceiver(active == null
                    ? null : active.activation);
            String missing = carrier.missing();
            if (!missing.isEmpty()) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.MISSING_METADATA, "", missing),
                        null, active);
            }
            EngineApi api = engine();
            String serialized = memoizedReadOut(carrier.key());
            if (serialized == null) {
                try {
                    serialized = memoizeReadOut(carrier.key(),
                            carrier.rawVersions(api));
                } catch (Throwable throwable) {
                    return recordShared(failedShared(
                            SharedStateEvidence.STAGE_VERSIONS,
                            SharedStateEvidence.INVOCATION_FAILED, "",
                            rootCause(throwable)), null, active);
                }
            }
            return recordShared(decodeVersionsEnvelope(serialized, carrier,
                    evidenceIdentity(active), active), null, active);
        } finally {
            endBookkeeping();
        }
    }

    /** Reads back the session's one event-order ledger. */
    public static SharedStateResult captureSessionEventLedger() {
        return captureSessionEventLedger(activeRegion());
    }

    private static SharedStateResult captureSessionEventLedger(
            ActiveRegion active) {
        beginBookkeeping();
        try {
            EngineApi api = engine();
            String serialized = memoizedReadOut(LEDGER_READ_OUT_KEY);
            if (serialized == null) {
                try {
                    serialized = memoizeReadOut(LEDGER_READ_OUT_KEY,
                            api.eventLedger());
                } catch (Throwable throwable) {
                    return recordShared(failedShared(
                            SharedStateEvidence.STAGE_LEDGER,
                            SharedStateEvidence.INVOCATION_FAILED, "",
                            rootCause(throwable)), null, active);
                }
            }
            return recordShared(decodeLedgerEnvelope(serialized,
                    evidenceIdentity(active)), null, active);
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Raw VM read-outs already taken while closing the selected occurrence on
     * this thread, keyed by the location they answer for.
     *
     * <p>Several evidence builders may ask for the same selected carrier.</p>
     */
    private static final ThreadLocal<Map<String, String>> READ_OUT_MEMO =
            new ThreadLocal<Map<String, String>>();

    /** Cache key for the session ledger, which names no single location. */
    private static final String LEDGER_READ_OUT_KEY = "SESSION_EVENT_LEDGER";

    // The scope discipline - open, memoize, close, never answer outside a
    // scope - is what keeps a stale read-out from being served for a live
    // location.

    /** The bytes already read for {@code key} in this close, or null. */
    private static String memoizedReadOut(String key) {
        Map<String, String> memo = READ_OUT_MEMO.get();
        return memo == null ? null : memo.get(key);
    }

    /** Files {@code serialized} under {@code key} and returns it unchanged. */
    private static String memoizeReadOut(String key, String serialized) {
        Map<String, String> memo = READ_OUT_MEMO.get();
        if (memo != null && serialized != null) memo.put(key, serialized);
        return serialized;
    }

    /** Reads one VM version envelope. */
    static SharedStateResult decodeVersionsEnvelope(
            String serialized, SharedCarrier carrier,
            RecordedEvidenceIdentity identity, ActiveRegion active) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            return failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "version read-out returned no JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        String fault = SharedStateEvidence.versionsFault(envelope);
        if (!fault.isEmpty()) {
            boolean unselected = SharedStateEvidence.VERSIONS_ENVELOPE_KIND
                    .equals(string(envelope, "kind"))
                    && !bool(envelope, "selected", false);
            int status = unselected ? SharedStateEvidence.NOT_SELECTED
                    : SharedStateEvidence
                    .expressionSerializationTruncationFault(fault)
                    ? SharedStateEvidence.EXPRESSION_SERIALIZATION_TRUNCATED
                    : SharedStateEvidence.MALFORMED_ENVELOPE;
            return failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    status,
                    SharedStateEvidence.locationKey(envelope), fault);
        }
        // The VM writes an unguarded write's guard as JSON null, which no tree
        // copy preserves.
        SharedStateEvidence.normalizeGuards(envelope);
        String locationKey = SharedStateEvidence.locationKey(envelope);
        JsonObject record = SharedStateEvidence.versionsRecord(locationKey,
                envelope, identity);
        if (carrier != null) {
            // The VM addresses a location by its own session identity; the
            // slice and the composer address one by its declared Java field.
            record.add("carrier", carrier.toJson());
        }
        // Publication can run after the owner thread has left ACTIVE.
        addActivationIdentity(object(record, "envelope"), active);
        return new SharedStateResult(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.OK, locationKey, 0L, envelope, record);
    }

    /**
     * Gives every write and read in one envelope the activation address the
     * rest of the pipeline joins on.
     *
     * <p>The VM stamps a write with the {@code taskId} of the context that
     * published it and a read with its {@code regionId}.</p>
     */
    private static void addActivationIdentity(JsonObject envelope) {
        addActivationIdentity(envelope, activeRegion());
    }

    private static void addActivationIdentity(JsonObject envelope,
                                              ActiveRegion active) {
        Configuration config = configuration();
        int versionOrdinal = 0;
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            // Wave 3 concurrency: every symbolic write of the session is a
            // version the composer may read from, so each one is addressed
            // by the write that produced it, the thread that ran it, and its
            // entry number in this location's own order.
            versionOrdinal++;
            version.addProperty("versionOrdinal", versionOrdinal);
            version.addProperty("writerEventId",
                    longInteger(version, "fieldVersionId", 0L));
            version.addProperty("threadId",
                    longInteger(version, "writerContextId", 0L));
            RuntimeTask writer = config.taskById(
                    string(version, "taskId"));
            if (writer == null) continue;
            WriterActivationIdentity exact;
            synchronized (CONTEXT_ACTIVATION_LOCK) {
                exact = CONTEXT_ACTIVATIONS.get(longInteger(version,
                        "writerContextId", 0L));
            }
            if (exact != null && exact.owns(writer)) {
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                        exact.sourceKey);
                version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                        exact.occurrenceId);
            } else if ("INITIAL".equals(string(version, "versionKind"))) {
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                        writer.sourceKey);
                version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                        writer.occurrenceId);
            } else {
                // A non-initial writer without an entry-time VM-context
                // binding has no exact activation owner.  Leave it unnamed so
                // the recorded writer universe refuses it by name instead of
                // collapsing every loop activation to the planned address.
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY, "");
                version.addProperty(
                        SharedStateEvidence.WRITER_OCCURRENCE_ID, "");
            }
        }
        for (JsonElement element : array(envelope, "reads")) {
            if (!element.isJsonObject()) continue;
            JsonObject read = element.getAsJsonObject();
            if (active == null) {
                read.addProperty(READER_AUTHORITY_FIELD,
                        READER_OUTSIDE_SELECTED_REGION);
                continue;
            }
            RuntimeTask reader = active.activation;
            // The VM addresses a read by its static region.
            if (!reader.regionId.equals(string(read, "regionId"))) {
                read.addProperty(READER_AUTHORITY_FIELD,
                        READER_FOREIGN_REGION);
                continue;
            }
            read.addProperty(SharedStateEvidence.READER_SOURCE_KEY,
                    reader.sourceKey);
            read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                    active.occurrenceId());
            read.addProperty(READER_AUTHORITY_FIELD,
                    READER_ACTIVE_REGION_AUTHORITY);
        }
    }

    /** Member naming where one read's activation address came from. */
    static final String READER_AUTHORITY_FIELD = "readerAuthority";
    /** Authority of a reader address taken from the running activation. */
    static final String READER_ACTIVE_REGION_AUTHORITY =
            "ACTIVE_REGION_READER_IDENTITY_V1";
    /** Marker for a read read out while no selected region was running. */
    static final String READER_OUTSIDE_SELECTED_REGION =
            "READER_OUTSIDE_SELECTED_REGION";
    /** Marker for a read whose static region is not the running one. */
    static final String READER_FOREIGN_REGION =
            "READER_REGION_NOT_ACTIVE_ACTIVATION";

    /** The identity every record of one read-out batch is stamped with. */
    private static RecordedEvidenceIdentity evidenceIdentity(
            ActiveRegion active) {
        if (active == null) return null;
        long session = workloadSessionId;
        return RecordedEvidenceIdentity.of(
                RecordedEvidenceIdentity.declaredRunId(),
                session != 0L ? "workload#" + session
                        : "region#" + active.token,
                active.activation.taskId,
                active.occurrenceId(),
                active.activation.sourceKey, active.evidenceSnapshot());
    }

    /**
     * Offers one compiled read-cut gate to the running activation.
     *
     * <p>The gate is admitted, recorded and left to observe.</p>
     */
    public static ReadCutGateResult installReadCutGate(JsonObject gate) {
        ActiveRegion active = activeRegion();
        // The row is judged before its context: whether a gate may be
        // installed at all is a property of the gate, and answering "no active
        // region" to one that would write a program field reports the lesser
        // finding and hides the greater.
        String unsafe = SparseReadCutGate.unsafeGateReason(gate);
        if (!unsafe.isEmpty()) {
            return recordReadCut(new ReadCutGateResult(
                    SparseReadCutGate.refusal(unsafe, gate,
                            "the offered gate was not installed"), false),
                    active);
        }
        if (active == null) {
            return recordReadCut(new ReadCutGateResult(
                    SparseReadCutGate.refusal(READ_CUT_NO_ACTIVE_REGION, gate,
                            "a read-cut gate was offered outside any region "
                                    + "activation"), false), null);
        }
        // The gate row is installed as offered: this runtime observes and
        // confirms, never parks, never writes a program field and never
        // replaces an RPC return value, so it states none of those.
        return recordReadCut(new ReadCutGateResult(gate.deepCopy(), true),
                active);
    }

    /** A read-cut gate was offered where no activation could carry it. */
    public static final String READ_CUT_NO_ACTIVE_REGION =
            "GATE_NO_ACTIVE_REGION";
    /** The selected order is observed and confirmed, never scheduled. */
    public static final String READ_CUT_ORDER_NOT_ENFORCED =
            "GATE_ORDER_NOT_ENFORCED";

    /** Files one gate outcome with the active region. */
    private static ReadCutGateResult recordReadCut(ReadCutGateResult result,
                                                   ActiveRegion active) {
        if (active != null) {
            if (result.installed) {
                active.readCutGates.add(result.record);
                active.readCutGaps.add(SparseReadCutGate.refusal(
                        READ_CUT_ORDER_NOT_ENFORCED, result.record,
                        "the gate observes and confirms the selected read; "
                                + "no wait was installed"));
            } else {
                active.readCutGaps.add(result.record);
            }
        }
        diag(result.installed ? "READ_CUT_GATE" : SparseReadCutGate.GAP_KIND,
                result.toString());
        return result;
    }

    /**
     * Outcome of one read-cut gate installation: either an admitted
     * observation-only gate or exactly one named refusal.
     */
    public static final class ReadCutGateResult {
        private final JsonObject record;
        private final boolean installed;

        private ReadCutGateResult(JsonObject record, boolean installed) {
            this.record = record;
            this.installed = installed;
        }

        /** Whether the gate was admitted as an observation. */
        public boolean installed() {
            return installed;
        }

        /** Named reason for a refusal; empty for an admitted gate. */
        public String reason() {
            return installed ? "" : string(record, "reason");
        }

        /** The admitted installation; empty after a refusal. */
        public JsonObject record() {
            return installed ? record.deepCopy() : new JsonObject();
        }

        /** Named coverage gap for a refusal; empty after an admission. */
        public JsonObject gap() {
            return installed ? new JsonObject() : record.deepCopy();
        }

        @Override
        public String toString() {
            return "ReadCutGateResult[" + (installed ? "OBSERVING "
                    + string(record, "gateId") : reason()) + "]";
        }
    }

    /** Reads one VM ledger envelope. */
    static SharedStateResult decodeLedgerEnvelope(
            String serialized, RecordedEvidenceIdentity identity) {
        JsonElement parsed = parseJson(serialized);
        if (!parsed.isJsonObject()) {
            return failedShared(SharedStateEvidence.STAGE_LEDGER,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "event ledger read-out returned no JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        String fault = SharedStateEvidence.ledgerFault(envelope);
        if (!fault.isEmpty()) {
            // README EVENT-1: truncation and saturation are their own gaps.
            return failedShared(SharedStateEvidence.STAGE_LEDGER,
                    SharedStateEvidence.ledgerFaultStatus(envelope, fault),
                    "", fault);
        }
        return new SharedStateResult(SharedStateEvidence.STAGE_LEDGER,
                SharedStateEvidence.OK, "", 0L, envelope,
                SharedStateEvidence.ledgerRecord(envelope, identity));
    }

    /** One shared location a task asked this activation to select. */
    static final class SharedCarrierRequest {
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final String sourceKind;
        private final int index;
        private final boolean element;
        private final boolean mapState;
        private final List<String> fieldPath = new ArrayList<>();

        SharedCarrierRequest(JsonObject declaration) {
            this.declaringClass = string(declaration, "declaringClass");
            this.fieldName = string(declaration, "fieldName");
            this.descriptor = string(declaration, "descriptor");
            this.sourceKind = string(declaration, "sourceKind");
            this.index = integer(declaration, "index", -1);
            this.element = "ARRAY_ELEMENT".equals(
                    string(declaration, "kind"));
            this.mapState = SharedStateEvidence.LOCATION_KIND_MAP_STATE
                    .equals(string(declaration, "kind"));
            for (JsonElement segment : array(declaration, "fieldPath")) {
                if (segment.isJsonPrimitive()) {
                    fieldPath.add(safe(segment.getAsString()));
                }
            }
        }

        /** How this declaration reads back in a gap. */
        String describe() {
            return (element ? "element " + index
                    : (mapState ? "map state of " : "")
                    + declaringClass + "#" + fieldName + ":" + descriptor)
                    + " via receiver path " + fieldPath;
        }

        /**
         * The object the selection is made on, reached from {@code receiver},
         * or {@link MissingValue#INSTANCE} when the path does not resolve.
         */
        Object resolveOwner(Object receiver) {
            if (fieldPath.isEmpty()) return receiver;
            return element || mapState
                    ? resolveFieldPathValue(receiver, fieldPath)
                    : resolveFieldPathLeafOwner(receiver, fieldPath);
        }

        boolean accessOwnerBound() {
            return "ACTIVATION_FIELD_RECEIVER".equals(sourceKind);
        }

        boolean matchesAccess(String fieldSignature) {
            // Cheapest test first: this hook now stands at every selected
            // field write as well as every selected read, and parsing a
            // signature for a carrier that is not access-bound would be work
            // done per store for nothing.
            if (!accessOwnerBound()) return false;
            DeclaredField field = FieldPathSpec.declaredField(
                    fieldSignature);
            return field != null
                    && declaringClass.equals(field.owner())
                    && fieldName.equals(field.name())
                    && (descriptor.isEmpty() || descriptor.equals(
                    javaTypeDescriptor(field.type())));
        }

        String fieldKey() {
            return RecordedReadFrom.fieldKey(declaringClass, fieldName);
        }

        /**
         * Selects this declared location on its exact access owner.
         *
         * <p>Wave 3: a declared shared location keeps EVERY symbolic write of
         * the session as a version.  There is no producer to admit and no
         * version to pick - the composer enumerates the versions the VM
         * already recorded as read-from arms - so selection is the whole of
         * what the runtime decides here.</p>
         */
        SharedStateResult selectAtAccess(Object owner,
                                         String fieldSignature) {
            if (mapState) {
                return selectSharedMapCarrier(
                        readExactField(owner, fieldSignature),
                        declaringClass, fieldName, descriptor);
            }
            return selectSharedFieldCarrier(owner, declaringClass,
                    fieldName, descriptor);
        }

        /** Selects this carrier for {@code active}, or names why it cannot. */
        SharedStateResult select(ActiveRegion active) {
            Object owner = resolveOwner(active.receiver);
            if (owner == MissingValue.INSTANCE) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.MISSING_METADATA, "",
                        "declared carrier owner is unreachable from the "
                                + "region receiver: " + describe()), null,
                        active);
            }
            if (element) return selectSharedElementCarrier(owner, index);
            if (mapState) {
                return selectSharedMapCarrier(owner, declaringClass,
                        fieldName, descriptor);
            }
            return selectSharedFieldCarrier(owner, declaringClass, fieldName,
                    descriptor);
        }
    }

    /** Selects every carrier this activation's task declared. */
    private static void selectDeclaredSharedCarriers(ActiveRegion active,
                                                    RuntimeTask claimant) {
        for (SharedCarrierRequest request : claimant.sharedCarriers) {
            // This binding is resolved by the exact instrumented field access,
            // where the actual declaring object is available.
            if (request.accessOwnerBound()) continue;
            try {
                request.select(active);
            } catch (Throwable throwable) {
                recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        request.describe() + ": " + rootCause(throwable)),
                        null, active);
            }
        }
    }

    /** Selects a demanded carrier on its exact field-access owner once. */
    private static void selectAccessOwnerSharedCarriers(
            ActiveRegion active, Object owner, String fieldSignature) {
        selectAccessOwnerSharedCarriers(active, active.activation, owner,
                fieldSignature);
        // Siblings are frozen before the activation is published.  Walk them
        // directly here instead of allocating the claimant union at every
        // selected field access.
        for (RuntimeTask claimant : active.siblingClaimants) {
            selectAccessOwnerSharedCarriers(active, claimant, owner,
                    fieldSignature);
        }
    }

    /** Selects one claimant's access-owner carriers for this activation. */
    private static void selectAccessOwnerSharedCarriers(
            ActiveRegion active, RuntimeTask claimant, Object owner,
            String fieldSignature) {
        for (SharedCarrierRequest request : claimant.sharedCarriers) {
            if (!request.matchesAccess(fieldSignature)) continue;
            String key = request.declaringClass + "#" + request.fieldName
                    + "@" + System.identityHashCode(owner);
            if (!active.accessOwnerCarrierSelections.add(key)) continue;
            try {
                request.selectAtAccess(owner, fieldSignature);
            } catch (Throwable throwable) {
                recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        request.describe() + ": " + rootCause(throwable)),
                        null, active);
            }
        }
    }

    /** One location this activation selected as a symbolic carrier. */
    static final class SharedCarrier {
        /** Selection shapes, which is the only thing a carrier varies in. */
        static final String SHAPE_FIELD = "FIELD";
        static final String SHAPE_ELEMENT = "ELEMENT";
        static final String SHAPE_MAP = "MAP";

        private final Object owner;
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final int index;
        private final String shape;
        /** Frozen trace locator from this task's selected causal edge. */
        private long plannedReceiverObjectId;

        private SharedCarrier(Object owner, String declaringClass,
                              String fieldName, String descriptor, int index,
                              String shape) {
            this.owner = owner;
            this.declaringClass = declaringClass;
            this.fieldName = fieldName;
            this.descriptor = descriptor;
            this.index = index;
            this.shape = shape;
        }

        static SharedCarrier field(Object owner, String declaringClass,
                                   String fieldName, String descriptor) {
            return new SharedCarrier(owner, safe(declaringClass),
                    safe(fieldName), safe(descriptor), -1, SHAPE_FIELD);
        }

        static SharedCarrier element(Object array, int index) {
            return new SharedCarrier(array, "", "", "", index, SHAPE_ELEMENT);
        }

        /** One map selected as the carrier of its own whole state. */
        static SharedCarrier map(Object map, String declaringClass,
                                 String fieldName, String descriptor) {
            return new SharedCarrier(map, safe(declaringClass),
                    safe(fieldName), safe(descriptor), -1, SHAPE_MAP);
        }

        boolean mapState() {
            return SHAPE_MAP.equals(shape);
        }

        void bindPlannedReceiver(RuntimeTask task) {
            if (task == null || SHAPE_ELEMENT.equals(shape)
                    || declaringClass.isEmpty() || fieldName.isEmpty()) {
                return;
            }
            bindPlannedReceiver(task.plannedReceiverObjectId(
                    declaringClass, fieldName));
        }

        void bindPlannedReceiver(long receiverObjectId) {
            plannedReceiverObjectId = Math.max(0L, receiverObjectId);
        }

        /** Activation-local dedupe key; never a cross-run address. */
        String key() {
            return shape + "/" + System.identityHashCode(owner) + "/"
                    + declaringClass + "#" + fieldName + ":" + descriptor
                    + "@" + index;
        }

        JsonObject toJson() {
            JsonObject carrier = new JsonObject();
            carrier.addProperty("kind", SHAPE_ELEMENT.equals(shape)
                    ? "ARRAY_ELEMENT"
                    : SHAPE_MAP.equals(shape)
                    ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                    : "DECLARED_FIELD");
            carrier.addProperty("declaringClass", declaringClass);
            carrier.addProperty("fieldName", fieldName);
            carrier.addProperty("descriptor", descriptor);
            carrier.addProperty("index", index);
            // A replay-local object id is not a cross-session identity.  The
            // frozen causal edge's receiver locator is the one stable name
            // every worker in this campaign shares.
            carrier.addProperty("receiverObjectId",
                    plannedReceiverObjectId);
            if (!SHAPE_ELEMENT.equals(shape) && !declaringClass.isEmpty()
                    && !fieldName.isEmpty()) {
                carrier.addProperty("fieldKey",
                        declaringClass + "#" + fieldName + ":" + descriptor);
            }
            return carrier;
        }

        /** Native read-out only; JSON decoding belongs to publication. */
        String rawVersions(EngineApi api) throws Exception {
            if (SHAPE_ELEMENT.equals(shape)) {
                return api.sharedElementVersions(owner, index);
            }
            if (SHAPE_MAP.equals(shape)) {
                return api.sharedMapVersions(owner);
            }
            return api.sharedFieldVersions(owner, declaringClass, fieldName,
                    descriptor);
        }
        /** Native selection only; the answer's meaning belongs to the caller. */
        long select(EngineApi api) throws Exception {
            if (SHAPE_ELEMENT.equals(shape)) {
                return api.selectSharedElementCarrier(owner, index);
            }
            if (SHAPE_MAP.equals(shape)) {
                return api.selectSharedMapCarrier(owner);
            }
            return api.selectSharedFieldCarrier(owner, declaringClass,
                    fieldName, descriptor);
        }

        /** The VM entry point {@link #select} calls, named for a failure. */
        String selectApi() {
            return SHAPE_ELEMENT.equals(shape) ? "selectSharedElementCarrier"
                    : SHAPE_MAP.equals(shape) ? "selectSharedMapCarrier"
                    : "selectSharedFieldCarrier";
        }

        /** Why this shape cannot name a carrier, or empty when it can. */
        String missing() {
            if (SHAPE_MAP.equals(shape)) {
                return owner == null
                        ? "a map carrier needs the map it selects" : "";
            }
            if (SHAPE_ELEMENT.equals(shape)) {
                return owner == null || index < 0
                        ? "an element carrier needs an array and a "
                        + "non-negative index" : "";
            }
            return missingCarrierMetadata(owner, declaringClass, fieldName,
                    descriptor);
        }

    }

    private static String missingCarrierMetadata(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        if (owner == null) return "shared carrier has no owner";
        return firstNonBlank(declaringClass).isEmpty()
                || firstNonBlank(fieldName).isEmpty()
                || firstNonBlank(descriptor).isEmpty()
                ? "shared carrier has no exact declaring class, field name "
                + "and type descriptor" : "";
    }

    private static SharedStateResult failedShared(String stage, int status,
                                                  String locationKey,
                                                  String detail) {
        return new SharedStateResult(stage, status, safe(locationKey), 0L,
                new JsonObject(), SharedStateEvidence.gap(stage, status,
                locationKey, detail));
    }

    /** Files one shared-state outcome with the active region. */
    private static SharedStateResult recordShared(SharedStateResult result,
                                                  SharedCarrier carrier,
                                                  ActiveRegion active) {
        fileShared(result, carrier, active);
        diag(result.ok() ? "SHARED_STATE" : SharedStateEvidence.GAP_KIND,
                result.toString());
        return result;
    }

    /** Files an already-decoded outcome without touching the closed VM. */
    private static void fileShared(SharedStateResult result,
                                   SharedCarrier carrier,
                                   ActiveRegion active) {
        if (active != null) {
            if (!result.ok()) {
                active.sharedStateGaps.add(result.record);
            } else if (carrier != null) {
                active.sharedCarriers.put(carrier.key(), carrier);
            } else if (SharedStateEvidence.STAGE_LEDGER.equals(
                    result.stage)) {
                active.sessionEventLedger = result.record;
            } else if (!result.locationKey.isEmpty()) {
                active.sharedStateRecords.put(result.locationKey,
                        result.record);
            }
        }
    }

    /**
     * Captures every native shared-state envelope while the owner thread still
     * owns the VM context.
     */
    private static RawSharedStateReadOut captureRecordedSharedStateRaw(
            ActiveRegion active, EngineApi api,
            RecordedEvidenceIdentity identity) {
        List<RawSharedCarrierReadOut> carriers = new ArrayList<>();
        for (SharedCarrier carrier
                : new ArrayList<>(active.sharedCarriers.values())) {
            try {
                String serialized = memoizedReadOut(carrier.key());
                if (serialized == null) {
                    serialized = memoizeReadOut(carrier.key(),
                            carrier.rawVersions(api));
                }
                carriers.add(new RawSharedCarrierReadOut(carrier,
                        serialized, null));
            } catch (Throwable throwable) {
                carriers.add(RawSharedCarrierReadOut.failure(carrier,
                        failedShared(SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.INVOCATION_FAILED, "",
                                rootCause(throwable))));
            }
        }

        String ledger = null;
        SharedStateResult ledgerFailure = null;
        try {
            ledger = memoizedReadOut(LEDGER_READ_OUT_KEY);
            if (ledger == null) {
                ledger = memoizeReadOut(LEDGER_READ_OUT_KEY,
                        api.eventLedger());
            }
        } catch (Throwable throwable) {
            ledgerFailure = failedShared(
                    SharedStateEvidence.STAGE_LEDGER,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable));
        }
        return new RawSharedStateReadOut(carriers, ledger, ledgerFailure,
                identity);
    }

    /** Decodes and files raw envelopes after the VM context is closed. */
    private static void assembleRecordedSharedState(
            ActiveRegion active, RawSharedStateReadOut raw) {
        if (raw == null) return;
        for (RawSharedCarrierReadOut carrier : raw.carriers) {
            SharedStateResult decoded = carrier.failure;
            if (decoded == null) {
                try {
                    decoded = decodeVersionsEnvelope(carrier.serialized,
                            carrier.carrier, raw.identity, active);
                } catch (Throwable throwable) {
                    decoded = failedShared(
                            SharedStateEvidence.STAGE_VERSIONS,
                            SharedStateEvidence.MALFORMED_ENVELOPE, "",
                            rootCause(throwable));
                }
            }
            fileShared(decoded, null, active);
        }
        SharedStateResult ledger = raw.ledgerFailure;
        if (ledger == null) {
            try {
                ledger = decodeLedgerEnvelope(raw.ledger, raw.identity);
            } catch (Throwable throwable) {
                ledger = failedShared(SharedStateEvidence.STAGE_LEDGER,
                        SharedStateEvidence.MALFORMED_ENVELOPE, "",
                        rootCause(throwable));
            }
        }
        fileShared(ledger, null, active);
    }

    /** One carrier's exact VM envelope, or the failure that replaced it. */
    private static final class RawSharedCarrierReadOut {
        private final SharedCarrier carrier;
        private final String serialized;
        private final SharedStateResult failure;

        private RawSharedCarrierReadOut(SharedCarrier carrier,
                                         String serialized,
                                         SharedStateResult failure) {
            this.carrier = carrier;
            this.serialized = serialized;
            this.failure = failure;
        }

        private static RawSharedCarrierReadOut failure(
                SharedCarrier carrier, SharedStateResult failure) {
            return new RawSharedCarrierReadOut(carrier, null, failure);
        }
    }

    /** Raw shared-state batch frozen before one VM region is finished. */
    private static final class RawSharedStateReadOut {
        private final List<RawSharedCarrierReadOut> carriers;
        private final String ledger;
        private final SharedStateResult ledgerFailure;
        private final RecordedEvidenceIdentity identity;

        private RawSharedStateReadOut(
                List<RawSharedCarrierReadOut> carriers, String ledger,
                SharedStateResult ledgerFailure,
                RecordedEvidenceIdentity identity) {
            this.carriers = carriers;
            this.ledger = ledger;
            this.ledgerFailure = ledgerFailure;
            this.identity = identity;
        }
    }

    /** Normal exit of the selected region occurrence. */
    public static void exitRegion(long token, Object returnValue,
                                  String primitiveValue) {
        finishRootInvocation(token, "NORMAL", "", returnValue);
    }

    /**
     * Invocation-exact normal cleanup used by injected roots.  This method is
     * intentionally no-throw: instrumentation bookkeeping must never turn a
     * normal program return into an exception (or let the synthetic catch-all
     * pop an enclosing frame a second time).
     */
    public static void exitRegionFrame(String instrumentationSelector,
                                       String rootMethod,
                                       Object returnValue,
                                       String primitiveValue) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    instrumentationSelector, rootMethod);
            if (frame != null && frame.token != 0L) {
                exitRegion(frame.token, returnValue, primitiveValue);
            }
        } catch (Throwable ignored) {
            // Runtime observation is fail-closed and cannot alter the return.
        }
    }

    /** Exceptional region exit. */
    public static void throwRegion(long token, Throwable throwable) {
        finishRootInvocation(token, "THROW",
                throwable == null ? "" : throwable.getClass().getName(),
                throwable);
    }

    /**
     * Invocation-exact exceptional cleanup used by the synthetic catch-all.
     * The original throwable is rethrown by injected bytecode; consequently
     * every runtime failure is swallowed here so it cannot replace it.
     */
    public static void throwRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Throwable throwable) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    instrumentationSelector, rootMethod);
            if (frame != null && frame.token != 0L) {
                if (throwable instanceof LoopBoundCut) {
                    finishRootInvocation(frame.token, "CUT", "", throwable);
                } else {
                    throwRegion(frame.token, throwable);
                }
            }
        } catch (Throwable ignored) {
            // Preserve the program's original throwable identity.
        }
    }

    private static RootInvocationFrame popRootInvocationFrame(
            String instrumentationSelector, String rootMethod) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = frames.peek();
        if (frame == null) {
            ROOT_INVOCATION_FRAMES.remove();
            return null;
        }
        boolean matches = sameSelector(frame.instrumentationSelector,
                instrumentationSelector)
                && (rootMethod == null ? frame.rootMethod == null
                : rootMethod.equals(frame.rootMethod));
        if (!matches) {
            // Never guess ownership.  In particular, do not expose or close
            // an outer selected frame when instrumentation is malformed.
            return null;
        }
        frames.pop();
        if (frames.isEmpty()) {
            ROOT_INVOCATION_FRAMES.remove();
        }
        return frame;
    }

    private static final class RootInvocationFrame {
        private final String instrumentationSelector;
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String instrumentationSelector,
                                    String rootMethod,
                                    long token) {
            this.instrumentationSelector = instrumentationSelector;
            this.rootMethod = rootMethod;
            this.token = token;
        }
    }

    /**
     * Reserves a VM-attested branch event immediately before the original
     * conditional executes.
     */
    public static long prepareBranch(String method, int unitIndex,
                                     String expression) {
        ActiveRegion active = activeRegion();
        if (active == null || !active.pathRecordingStarted) return 0L;
        try {
            PreparedBranch prepared = active.prepareBranch(method, unitIndex,
                    expression, engine());
            return prepared == null ? 0L : prepared.handle;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch event preparation failed: "
                    + rootCause(throwable));
            return 0L;
        }
    }

    /**
     * Exact-event overload carrying the id returned by the native marker that
     * the instrumented class executes immediately before its original if.
     */
    public static boolean resolveBranch(long preparedHandle, long vmEventId,
                                        String method, int unitIndex,
                                        String expression,
                                        boolean observedOutcome) {
        ActiveRegion active = activeRegion();
        if (active == null) return observedOutcome;
        String branchSite = siteId(method, unitIndex);
        if (!active.activation.declaresBranch(branchSite)) {
            active.takePreparedBranch(preparedHandle);
            return observedOutcome;
        }
        if (!active.pathRecordingStarted) {
            active.recordConcreteBranch(method, unitIndex, observedOutcome);
            return observedOutcome;
        }
        PreparedBranch prepared = active.takePreparedBranch(preparedHandle);
        if (prepared == null || !prepared.matches(method, unitIndex,
                expression)) {
            active.addUnresolvedOnce("missing or mismatched prepared branch "
                    + preparedHandle + " for " + safe(method) + "#u"
                    + unitIndex);
            // No unverified VM event may be rebound heuristically on a JDK
            // that advertised the exact API.
            return observedOutcome;
        }
        EngineApi api = engine();
        boolean paused = false;
        boolean replayContradicted = false;
        try {
            api.pausePathCondition();
            paused = true;
            boolean solverWitness = recordBranchPaused(active, api, method,
                    unitIndex, expression, prepared.occurrence,
                    observedOutcome, vmEventId);
            boolean replayTargetMatched = active.observeReplayBranch(
                    siteId(method, unitIndex), prepared.occurrence,
                    observedOutcome);
            replayContradicted = active.replayPrefixContradicted();
            if (solverWitness && replayTargetMatched
                    && !active.activation.targetBranchSite.isEmpty()
                    && active.activation.targetBranchSite.equals(
                    siteId(method, unitIndex))
                    && active.activation.targetBranchOccurrence
                    == prepared.occurrence) {
                // Reaching the target is a fact of this case, never a reason
                // to stop recording it: the RPC, state and throw effects the
                // occurrence still owes all happen after this branch.
                active.recordTargetReach(siteId(method, unitIndex),
                        prepared.occurrence, observedOutcome);
            }
            return observedOutcome;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedOutcome;
        } finally {
            if (paused) resumePathCondition(active, api);
            if (replayContradicted) {
                // Release the engine here rather than at this activation's own
                // return: the branch that just executed already decided that
                // nothing publishable can follow.
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    /** Exact multiway counterpart of {@link #resolveBranch}. */
    public static int resolveSwitchBranch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        SwitchExpectation expected;
        try {
            expected = SwitchExpectation.parse(branchKind, encodedCaseKeys,
                    observedSuccessorIndex);
        } catch (IllegalArgumentException malformed) {
            ActiveRegion active = activeRegion();
            if (active != null) {
                active.addUnresolvedOnce(safe(method) + "#u" + unitIndex
                        + ": invalid static switch contract: "
                        + rootCause(malformed));
            }
            return observedSuccessorIndex;
        }
        ActiveRegion active = activeRegion();
        if (active == null) return observedSuccessorIndex;
        String branchSite = siteId(method, unitIndex);
        if (!active.activation.declaresBranch(branchSite)) {
            active.takePreparedBranch(preparedHandle);
            return observedSuccessorIndex;
        }
        if (!active.pathRecordingStarted) {
            active.recordConcreteBranch(method, unitIndex,
                    expected.caseArm());
            return observedSuccessorIndex;
        }
        PreparedBranch prepared = active.takePreparedBranch(preparedHandle);
        if (prepared == null || !prepared.matches(method, unitIndex,
                expression)) {
            active.addUnresolvedOnce("missing or mismatched prepared switch "
                    + preparedHandle + " for " + safe(method) + "#u"
                    + unitIndex);
            return observedSuccessorIndex;
        }
        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
            recordSwitchBranchPaused(active, api, method, unitIndex,
                    expression, prepared.occurrence, expected, vmEventId);
            return observedSuccessorIndex;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("switch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedSuccessorIndex;
        } finally {
            if (paused) resumePathCondition(active, api);
        }
    }

    private static boolean recordBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        if (vmEventId <= 0L) {
            // The VM emitted no symbolic branch event.
            return false;
        }
        String siteId = safe(method) + "#u" + unitIndex;
        int baseline = active.lastPathConditionSize;
        // One read of the event stream, used by both questions asked of it.
        JsonElement events = parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        PathConditionElements conditions;
        int rawPathConditionSize;
        int attestationBaseline;
        if (noVmCondition) {
            // An exact conditionless event cannot contribute a branch guard.
            conditions = PathConditionElements.EMPTY;
            rawPathConditionSize = baseline;
            attestationBaseline = 0;
        } else if (contiguousConditionIndices(eventConditionIndices)) {
            int firstCondition = eventConditionIndices.get(0);
            int lastCondition = eventConditionIndices.get(
                    eventConditionIndices.size() - 1);
            diag("PC_READ_BEGIN", siteId + " occ=" + occurrence
                    + " range=[" + firstCondition + ","
                    + (lastCondition + 1) + ")");
            PathConditionRead read = readPathConditionRange(api,
                    firstCondition, lastCondition + 1);
            diag("PC_READ_END", siteId + " occ=" + occurrence
                    + " chars=" + read.chars + " source=" + read.source);
            conditions = read.conditions;
            rawPathConditionSize = conditions.size();
            attestationBaseline = baseline;
            diag("PC_PARSED", siteId + " occ=" + occurrence
                    + " conditions=" + rawPathConditionSize
                    + " mode=" + conditions.mode());
        } else {
            // The exact event stream is the only authority on which path
            // conditions belong to this branch.
            conditions = PathConditionElements.EMPTY;
            rawPathConditionSize = baseline;
            attestationBaseline = baseline;
        }
        VmBranchEventAttestation vmAttestation = attestVmBranchEvent(api,
                active, siteId, expression, observedOutcome, vmEventId,
                occurrence, conditions, attestationBaseline, null, events);
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence);
        // Exact VM ownership is one condition for an IfStmt.
        int mappingBaseline = conditionIndex >= 0
                ? conditionIndex : baseline;
        int mappingLimit = conditionIndex >= 0
                ? conditionIndex + 1 : rawPathConditionSize;
        mapping.addProperty("rawPathConditionSize", mappingLimit);
        mapping.addProperty("rawPathConditionBaseline", mappingBaseline);
        if (conditionIndex >= 0) {
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition = semanticBranchCondition(
                    expression, observedOutcome, condition);
            String rawOperator = binaryOperator(condition);
            String semanticOperator = binaryOperator(semanticCondition);
            if (vmAttestation.valid) {
                JsonObject metadata = new JsonObject();
                metadata.addProperty("predicateNormalization",
                        safe(rawOperator).equals(safe(semanticOperator))
                                ? BranchWitness.IDENTITY_NORMALIZATION
                                : BranchWitness.CMP_NORMALIZATION);
                BranchWitness witness = BranchWitness.vmPc(siteId,
                        safe(method), unitIndex, occurrence,
                        observedOutcome, semanticCondition, conditionIndex,
                        metadata);
                mapping.add("witness", witness.toJson());
            }
        } else if (vmAttestation.valid
                && vmAttestation.conditionIndices.isEmpty()) {
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attested(siteId,
                            safe(method), unitIndex, occurrence,
                            observedOutcome).toJson());
        }
        boolean pathConditionShrank = !noVmCondition
                && rawPathConditionSize < baseline;
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
        if (mapping.has("witness") || mapping.has("concreteObservation")) {
            // A marker without either authority carries no decision into the
            // summary, so it must not attest a recorded outcome either.
            active.witnessOutcome(siteId, observedOutcome);
        }
        return vmAttestation.valid && conditionIndex >= 0;
    }

    /** One branch hook's exact, VM-owned condition window. */
    private static final class PathConditionRead {
        private final PathConditionElements conditions;
        private final int chars;
        private final String source;

        private PathConditionRead(PathConditionElements conditions, int chars,
                                  String source) {
            this.conditions = conditions;
            this.chars = chars;
            this.source = source;
        }
    }

    /** Reads only the absolute indices named by an exact VM branch event. */
    private static PathConditionRead readPathConditionRange(
            EngineApi api, int start, int end) throws Exception {
        if (start < 0 || end <= start) {
            return new PathConditionRead(PathConditionElements.EMPTY, -1,
                    "EXACT_RANGE_UNAVAILABLE");
        }
        String windowed;
        try {
            windowed = api.pathConditionRange(start, end);
        } catch (Throwable refused) {
            windowed = null;
        }
        PathConditionElements exact =
                PathConditionElements.window(windowed, start);
        if (exact == null) {
            return new PathConditionRead(PathConditionElements.EMPTY,
                    windowed == null ? -1 : windowed.length(),
                    "EXACT_RANGE_REFUSED");
        }
        return new PathConditionRead(exact, windowed.length(),
                "EXACT_EVENT_RANGE");
    }

    private static List<Integer> vmEventConditionIndices(
            JsonElement parsed, long eventId) {
        if (!parsed.isJsonObject()) return null;
        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(
                parsed.getAsJsonObject(), "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (longInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) return null;
        JsonArray raw = array(selected, "conditionIndices");
        if (integer(selected, "conditionCount", -1) != raw.size()) {
            return null;
        }
        List<Integer> indices = new ArrayList<>();
        for (JsonElement value : raw) {
            try {
                indices.add(value.getAsInt());
            } catch (RuntimeException malformed) {
                return null;
            }
        }
        return indices;
    }

    private static boolean contiguousConditionIndices(List<Integer> indices) {
        if (indices == null || indices.isEmpty()) return false;
        int expected = indices.get(0);
        if (expected < 0) return false;
        for (Integer index : indices) {
            if (index == null || index != expected) return false;
            expected++;
        }
        return true;
    }

    private static void recordSwitchBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        String siteId = safe(method) + "#u" + unitIndex;
        int baseline = active.lastPathConditionSize;
        JsonElement events = parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        PathConditionRead read;
        if (eventConditionIndices != null
                && eventConditionIndices.isEmpty()) {
            read = new PathConditionRead(PathConditionElements.EMPTY, 0,
                    "CONDITIONLESS_EVENT");
        } else if (contiguousConditionIndices(eventConditionIndices)) {
            int firstCondition = eventConditionIndices.get(0);
            int lastCondition = eventConditionIndices.get(
                    eventConditionIndices.size() - 1);
            read = readPathConditionRange(api, firstCondition,
                    lastCondition + 1);
        } else {
            read = new PathConditionRead(PathConditionElements.EMPTY, -1,
                    "EXACT_RANGE_UNAVAILABLE");
        }
        diag("PC_READ_END", siteId + " occ=" + occurrence
                + " chars=" + read.chars + " source=" + read.source);
        PathConditionElements conditions = read.conditions;
        VmBranchEventAttestation attestation = attestVmBranchEvent(api,
                active, siteId, expression, expected.caseArm(), vmEventId,
                occurrence, conditions, baseline, expected, events);
        List<Integer> conditionIndices = attestation.valid
                ? attestation.conditionIndices
                : Collections.<Integer>emptyList();
        JsonObject mapping = branchMapping(method, unitIndex, occurrence);
        mapping.addProperty("rawPathConditionSize", conditions.size());
        mapping.addProperty("rawPathConditionBaseline", baseline);
        if (!attestation.valid) {
            active.addUnresolvedOnce(siteId
                    + ": exact switch event attestation failed: "
                    + attestation.error);
        } else if (conditionIndices.isEmpty()) {
            active.addUnresolvedOnce(siteId
                    + ": exact switch event has no symbolic selector "
                    + "conditions");
        }
        if ("EXPLORE".equals(active.activation.policy(siteId))) {
            active.addUnresolvedOnce(siteId
                    + ": multiway switch requires successor-aware path "
                    + "enumeration; Boolean outcome negation is prohibited");
        }
        active.lastPathConditionSize = conditions.size();
        active.branchMappings.add(mapping);
    }

    private static JsonObject branchMapping(
            String method, int unitIndex, int occurrence) {
        JsonObject mapping = new JsonObject();
        mapping.addProperty("siteId", siteId(method, unitIndex));
        mapping.addProperty("method", safe(method));
        mapping.addProperty("unitIndex", unitIndex);
        mapping.addProperty("occurrence", occurrence);
        return mapping;
    }

    /**
     * @param readEvents the caller's own read of the exact event stream, or
     *                   {@code null} to read it here.  A caller that has
     *                   already asked the stream a question about this event
     *                   passes what it read: a second read costs a full
     *                   serialization and decode of every event the thread has
     *                   recorded, and would let the two answers be taken from
     *                   two different observations of it.
     */
    private static VmBranchEventAttestation attestVmBranchEvent(
            EngineApi api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, PathConditionElements conditions, int baseline,
            SwitchExpectation switchExpectation, JsonElement readEvents) {
        if (eventId <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "marker returned a non-positive event id");
        }
        final JsonElement parsed;
        if (readEvents != null) {
            parsed = readEvents;
        } else {
            try {
                parsed = parseJson(api.branchEvents());
            } catch (Throwable throwable) {
                return VmBranchEventAttestation.invalid(
                        "event stream is not readable: "
                                + rootCause(throwable));
            }
        }
        if (!parsed.isJsonObject()) {
            return VmBranchEventAttestation.invalid(
                    "event stream is not a JSON object");
        }
        JsonObject envelope = parsed.getAsJsonObject();
        if (integer(envelope, "schemaVersion", -1) != 1
                || !"CONCOLIC_THREAD_BRANCH_EVENTS".equals(
                string(envelope, "kind"))
                || !bool(envelope, "active", false)) {
            return VmBranchEventAttestation.invalid(
                    "unexpected or inactive event stream");
        }
        long envelopeContext = longInteger(envelope, "contextId", 0L);
        long envelopeOwner = longInteger(envelope,
                "ownerJavaThreadId", 0L);
        long envelopeOsOwner = longInteger(envelope,
                "ownerOsThreadId", 0L);
        if (envelopeContext <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "missing positive VM thread context id");
        }
        if (envelopeOwner != active.thread.getId()) {
            return VmBranchEventAttestation.invalid(
                    "event stream belongs to Java thread " + envelopeOwner
                            + " instead of " + active.thread.getId());
        }
        if (!safe(active.activation.regionId).equals(
                string(envelope, "regionId"))
                || !safe(active.activation.taskId).equals(
                string(envelope, "taskId"))) {
            return VmBranchEventAttestation.invalid(
                    "event stream region/task does not match owner");
        }

        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(envelope, "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (longInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) {
            return VmBranchEventAttestation.invalid(
                    "event id " + eventId + " matched " + matches
                            + " records");
        }
        String authority = string(selected, "authority");
        if (!"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(authority)) {
            return VmBranchEventAttestation.invalid(
                    "unsupported event authority " + authority);
        }
        if (longInteger(selected, "contextId", 0L) != envelopeContext
                || longInteger(selected, "ownerJavaThreadId", 0L)
                != envelopeOwner
                || longInteger(selected, "ownerOsThreadId", 0L)
                != envelopeOsOwner) {
            return VmBranchEventAttestation.invalid(
                    "event owner/context differs from its thread envelope");
        }
        if (!safe(active.activation.regionId).equals(
                string(selected, "regionId"))
                || !safe(active.activation.taskId).equals(
                string(selected, "taskId"))) {
            return VmBranchEventAttestation.invalid(
                    "event region/task differs from its owner");
        }
        if (!safe(siteId).equals(string(selected, "siteId"))
                || integer(selected, "occurrence", -1) != occurrence) {
            return VmBranchEventAttestation.invalid(
                    "event site/occurrence does not match prepared branch");
        }
        if (bool(selected, "outcome", !observedOutcome)
                != observedOutcome) {
            return VmBranchEventAttestation.invalid(
                    "event outcome differs from observed branch");
        }
        JsonArray indices = array(selected, "conditionIndices");
        if (integer(selected, "conditionCount", -1) != indices.size()) {
            return VmBranchEventAttestation.invalid(
                    "event condition count differs from its index vector");
        }
        if (switchExpectation != null) {
            return attestVmSwitchConditions(selected,
                    switchExpectation, indices, conditions, baseline);
        }
        if (indices.size() > 1) {
            return VmBranchEventAttestation.invalid(
                    "instrumented IfStmt emitted multiple condition indices");
        }
        int conditionIndex = -1;
        if (indices.size() == 1) {
            try {
                conditionIndex = indices.get(0).getAsInt();
            } catch (RuntimeException exception) {
                return VmBranchEventAttestation.invalid(
                        "condition index is not an integer");
            }
            if (conditionIndex < baseline
                    || conditionIndex >= conditions.size()) {
                return VmBranchEventAttestation.invalid(
                        "condition index " + conditionIndex
                                + " is outside new path-condition suffix ["
                                + baseline + "," + conditions.size() + ")");
            }
            if (!branchConditionMatches(expression, observedOutcome,
                    conditions.get(conditionIndex))) {
                return VmBranchEventAttestation.invalid(
                        "selected VM condition does not match the original "
                                + "branch predicate");
            }
        }
        return VmBranchEventAttestation.valid(
                conditionIndex < 0
                        ? Collections.<Integer>emptyList()
                        : Collections.singletonList(conditionIndex));
    }

    private static VmBranchEventAttestation attestVmSwitchConditions(
            JsonObject event, SwitchExpectation expected,
            JsonArray rawIndices, PathConditionElements conditions,
            int baseline) {
        int expectedOpcode = "TABLE_SWITCH".equals(expected.branchKind)
                ? 170 : 171;
        if (integer(event, "opcode", -1) != expectedOpcode) {
            return VmBranchEventAttestation.invalid(
                    "event opcode does not match static "
                            + expected.branchKind);
        }
        if (string(event, "codePosition").isEmpty()) {
            return VmBranchEventAttestation.invalid(
                    "switch event has no bytecode position");
        }

        int completeSymbolicCount = expected.caseArm()
                ? 1 : expected.caseKeys.size();
        // The VM still emits an exact event when the selector is concrete.
        if (rawIndices.size() == 0) {
            if (conditions.size() != baseline) {
                return VmBranchEventAttestation.invalid(
                        "conditionless switch event does not own an empty "
                                + "path-condition suffix");
            }
            return VmBranchEventAttestation.valid(
                    Collections.<Integer>emptyList());
        }
        if (rawIndices.size() != completeSymbolicCount) {
            return VmBranchEventAttestation.invalid(
                    "switch arm owns " + rawIndices.size()
                            + " conditions; exact arm requires "
                            + completeSymbolicCount);
        }
        if (conditions.size() != baseline + completeSymbolicCount) {
            return VmBranchEventAttestation.invalid(
                    "switch conditions do not form the complete new "
                            + "path-condition suffix");
        }

        List<Integer> indices = new ArrayList<>();
        String selector = "";
        String expectedPosition = string(event, "codePosition");
        for (int offset = 0; offset < rawIndices.size(); offset++) {
            final int conditionIndex;
            try {
                conditionIndex = rawIndices.get(offset).getAsInt();
            } catch (RuntimeException malformed) {
                return VmBranchEventAttestation.invalid(
                        "switch condition index is not an integer");
            }
            if (conditionIndex != baseline + offset) {
                return VmBranchEventAttestation.invalid(
                        "switch condition indices are not the exact ordered "
                                + "new path-condition suffix");
            }
            JsonElement condition = conditions.get(conditionIndex);
            int key = expected.caseArm()
                    ? expected.caseKeys.get(
                    expected.observedSuccessorIndex)
                    : expected.caseKeys.get(offset);
            String operator = expected.caseArm() ? "==" : "!=";
            String matchedSelector = switchSelectorIfMatches(condition,
                    operator, key);
            if (matchedSelector.isEmpty()) {
                return VmBranchEventAttestation.invalid(
                        "switch condition " + offset
                                + " is not selector " + operator + " "
                                + key);
            }
            if (selector.isEmpty()) {
                selector = matchedSelector;
            } else if (!selector.equals(matchedSelector)) {
                return VmBranchEventAttestation.invalid(
                        "switch conditions do not share one selector");
            }
            String conditionPosition = condition.isJsonObject()
                    ? string(condition.getAsJsonObject(), "_code_position")
                    : "";
            if (!conditionPosition.isEmpty()
                    && !expectedPosition.equals(conditionPosition)) {
                return VmBranchEventAttestation.invalid(
                        "switch condition bytecode position differs from "
                                + "its exact event");
            }
            indices.add(conditionIndex);
        }
        return VmBranchEventAttestation.valid(indices);
    }

    private static String switchSelectorIfMatches(
            JsonElement condition, String expectedOperator, int expectedKey) {
        if (condition == null || !condition.isJsonObject()) return "";
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))
                || !expectedOperator.equals(string(object, "_op"))) {
            return "";
        }
        JsonElement left = object.get("_left");
        JsonElement right = object.get("_right");
        if (left == null || !left.isJsonObject()
                || right == null || !right.isJsonObject()
                || "ConstExpr".equals(string(left.getAsJsonObject(),
                "_type"))) {
            return "";
        }
        JsonObject constant = right.getAsJsonObject();
        if (!"ConstExpr".equals(string(constant, "_type"))) return "";
        Matcher encoded = Pattern.compile("^Y_I_(-?(?:0|[1-9][0-9]*))$")
                .matcher(string(constant, "_exp"));
        if (!encoded.matches()) return "";
        final int key;
        try {
            key = Integer.parseInt(encoded.group(1));
        } catch (NumberFormatException malformed) {
            return "";
        }
        return key == expectedKey ? left.toString() : "";
    }

    /** Marks one selected occurrence unusable before its VM close. */
    private static void abandonOccurrence(
            ActiveRegion active, String skipKind, String reason) {
        active.releaseActivationOrdinal();
        active.abandoned = true;
        endLiveSelectedRegion();
        writeSkipped(active.activation, skipKind, reason, null);
    }

    /** Releases an incomplete candidate so a later invocation can answer. */
    /** Ends one selected occurrence at its declared boundary. */
    private static void finish(long token, String exitKind,
                               String exceptionType, Object output) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return;
        finishOccurrence(active, exitKind, exceptionType, output);
    }

    /** Root-invocation exit for whichever activation owns {@code token}. */
    private static void finishRootInvocation(long token, String exitKind,
                                             String exceptionType,
                                             Object output) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return;
        finishOccurrence(active, exitKind, exceptionType, output);
    }

    private static void finishOccurrence(ActiveRegion active, String exitKind,
                                         String exceptionType, Object output) {
        if (!active.finished.compareAndSet(false, true)) return;
        beginSelectedResultPublication();
        boolean publicationDeferred = false;
        // Judgement and publication are bookkeeping, not workload control
        // flow, so they remain muted until this occurrence's VM context is
        // closed.
        beginBookkeeping();
        try {
            try {
                // Exact call-site traps normally close every accessor scope
                // first.
                AccessorCallContext scope =
                        CURRENT_ACCESSOR_CALL_CONTEXT.get();
                if (scope != null && scope.regionToken == active.token) {
                    CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                }
                diag("REGION_FINISH", "token=" + active.token
                        + " task=" + safe(active.activation.taskId)
                        + " source=" + active.attributedSourceKeys()
                        + " exit=" + safe(exitKind) + " captures="
                        + active.outputCaptures.size());
                active.exitKind = safe(exitKind);
                active.exceptionType = safe(exceptionType);
                active.exitOutput = output;
                judgeFinishedOccurrence(active);
                suppressDuplicateRelationResult(active);
                releaseUnanchoredLoopTurn(active);
            } finally {
                publicationDeferred = closeOccurrence(active);
            }
        } finally {
            endBookkeeping();
            if (!publicationDeferred) endSelectedResultPublication();
        }
    }

    /**
     * Gives back a bounded loop-body turn that carried none of its region's
     * selected causal anchors once the prefix quota is spent.
     *
     * <p>The turn ran -- Hadoop's own iteration is untouched -- and it
     * published nothing, so its ordinal returns to the address and the
     * reserved slots stay open for the turns the plan selected this region
     * for.  An address with no anchor never reaches here.</p>
     */
    private static void releaseUnanchoredLoopTurn(ActiveRegion active) {
        if (active.abandoned) return;
        if (!active.activation.addressesOccurrencesByCausalAnchor()) return;
        Set<String> newlyCarried = active.activation.newSemanticAnchorIds(
                active.carriedSemanticAnchorIds());
        if (!active.activation.releasesUnanchoredLoopTurn(
                !newlyCarried.isEmpty())) {
            active.retainedSemanticAnchorIds.addAll(newlyCarried);
            return;
        }
        diag("LOOP_TURN_UNANCHORED", "task="
                + safe(active.activation.taskId) + " ordinal="
                + active.activationOrdinal + " anchors="
                + active.activation.causalAnchorPorts());
        active.releaseActivationOrdinal();
        active.abandoned = true;
        endLiveSelectedRegion();
    }

    /**
     * Hands this activation to another open occurrence of the same root whose
     * demanded boundary it did reach.
     *
     * @return {@code true} when the region was re-keyed to a claimant that
     *         answers, leaving it to publish under that occurrence
     */
    private static boolean answerSiblingClaimant(ActiveRegion active) {
        for (int index = 0; index < active.siblingClaimants.size(); index++) {
            RuntimeTask claimant = active.siblingClaimants.get(index);
            // The bounded-traversal budget and the replay prefix were built
            // from the task this activation entered under, so only an
            // occurrence that would have been bounded and replayed the same
            // way may take its evidence.
            if (claimant.replayContract != null
                    || active.activation.replayContract != null
                    || !claimant.loopBound.identity().equals(
                    active.activation.loopBound.identity())) {
                continue;
            }
            if (incompleteRelationOnlyBoundary(claimant,
                    active.outputCaptures, active.exitKind)) {
                continue;
            }
            RuntimeTask entered = active.activation;
            entered.noteUnaddressedCandidate(
                    "compatible root ended before every demanded semantic "
                            + "output boundary was observed; missing "
                            + unobservedOutputBoundaries(entered,
                            active.outputCaptures)
                            + "; its boundary was answered by "
                            + claimant.occurrenceId);
            configuration().releaseCandidate(entered);
            // The ordinal belongs to the address that publishes the row.
            active.releaseActivationOrdinal();
            active.activationOrdinal = claimant.nextActivationOrdinal();
            active.siblingClaimants.remove(index);
            active.siblingClaimants.add(entered);
            active.activation = claimant;
            updateContextActivation(active);
            diag("OCCURRENCE_RE_KEYED", "from=" + safe(entered.taskId)
                    + " to=" + safe(claimant.taskId));
            return true;
        }
        return false;
    }

    /**
     * Applies the admission gates a finished occurrence must pass before its
     * relation may be built.
     */
    private static void judgeFinishedOccurrence(ActiveRegion active) {
        // First, because it is the only gate that asks whether this activation
        // is the addressed occurrence at all.
        String unaddressed =
                active.activation.rootContextSelector.unconfirmed(
                        active.attributedSourceKeys());
        if (!unaddressed.isEmpty()) {
            // A candidate that is not the addressed occurrence is the
            // candidate loop working, not a finding, so it is released without
            // a durable row.
            active.activation.noteUnaddressedCandidate(unaddressed);
            active.releaseActivationOrdinal();
            active.abandoned = true;
            endLiveSelectedRegion();
            return;
        }
        // A target address that several activations of one region on one
        // source answer is separated by the only thing that distinguishes
        // them: whether this activation reached the declared target event.
        // One that did not has not answered the address, so it releases it by
        // name and the next candidate is tried - which is what README OCC-1
        // means by treating each target occurrence as a candidate.
        // An activation that did not take the declared target event is not a
        // rejected candidate: it is an occurrence of this address that did
        // something else, and it publishes with targetReached:false so the
        // importer never selects it as THE target case.

        if (active.replayPrefixContradicted()) {
            abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                    "activation contradicts the recorded replay prefix: "
                            + active.replayProgress.failure());
            return;
        }
        if (incompleteRelationOnlyBoundary(active.activation,
                active.outputCaptures, active.exitKind)) {
            // The boundary this activation reached, and not the order the
            // plan happens to list its occurrences in, decides which of them
            // it answered: an activation admitted under one occurrence may be
            // the only one that ever reaches another's boundary.  When none
            // of them is complete the row still publishes, carrying
            // relationallyComplete:false and the missing bindings by name -
            // README OCC-1: the boundary describes an occurrence, it does not
            // gate admission of one.
            if (!answerSiblingClaimant(active)) {
                active.addUnresolvedOnce(
                        "compatible root ended before every demanded semantic "
                                + "output boundary was observed; missing "
                                + unobservedOutputBoundaries(active.activation,
                                active.outputCaptures));
            }
        }
        // Replay progress is frozen at this terminal.
        if (active.activation.replayContract != null) {
            if (!active.replayProgress.complete()) {
                abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                        "no compatible activation matched replay prefix: "
                                + active.replayProgress.failure());
                return;
            }
            List<String> unapplied = new ArrayList<>();
            for (ModelAssignment assignment
                    : active.activation.modelAssignments) {
                if (!active.appliedModelAssignments.contains(
                        assignment.key)) {
                    unapplied.add(assignment.key);
                }
            }
            if (!unapplied.isEmpty()) {
                // A completed replay may publish only after every model row
                // actually changed its exact Java input.
                abandonOccurrence(active, SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                        "terminal reached with unapplied model assignment "
                                + "keys " + unapplied);
            }
            return;
        }
        // The occurrence has stopped running, so its witnessed outcome set
        // cannot widen any further.
        String conflict = seedOutcomeConflict(active.activation.seedOutcomes,
                active.witnessedOutcomes);
        if (!conflict.isEmpty()) {
            abandonOccurrence(active, SKIP_SEED_OUTCOME_CONFLICT,
                    "activation contradicts a recorded seed outcome: "
                            + conflict);
        }
    }

    /**
     * Keeps later producer activations live long enough to propagate their
     * symbolic state, but discards their duplicate durable relation row once
     * this non-loop address has already published one complete relation.
     */
    private static void suppressDuplicateRelationResult(ActiveRegion active) {
        if (active.abandoned
                || !active.activation.suppressesDuplicateRelationResult()) {
            return;
        }
        diag("DUPLICATE_RELATION_RESULT_SUPPRESSED", "task="
                + safe(active.activation.taskId) + " ordinal="
                + active.activationOrdinal);
        active.releaseActivationOrdinal();
        active.abandoned = true;
        endLiveSelectedRegion();
    }

    /**
     * Reads one occurrence and closes its VM region on the owner thread, then
     * transfers JSON decoding and durable publication to the daemon pool.
     *
     * @return true only when the publication executor owns the in-flight
     *         publication counter
     */
    private static boolean closeOccurrence(ActiveRegion active) {
        if (!active.beginClose()) return false;
        // Whatever this activation answered, the occurrences that rode it and
        // were not answered go back on offer for the next one.
        for (RuntimeTask claimant : active.siblingClaimants) {
            configuration().releaseCandidate(claimant);
        }
        active.siblingClaimants.clear();
        EngineApi api = engine();
        boolean engineFinished = false;
        String rawEngineSummary = null;
        RawSharedStateReadOut rawSharedState = null;
        JsonObject result = null;
        try {
            // Everything below is observational bookkeeping.
            api.pausePathCondition();
            READ_OUT_MEMO.set(new HashMap<String, String>());
            try {
                if (!active.abandoned) {
                    result = new JsonObject();
                    // One ordinal names every row assembled for this close.
                    active.evidenceSnapshot =
                            EVIDENCE_SNAPSHOTS.incrementAndGet();
                    RecordedEvidenceIdentity identity =
                            evidenceIdentity(active);
                    try {
                        buildCompletedResult(result, active, identity);
                    } catch (Throwable throwable) {
                        result.addProperty("engineSummaryError",
                                rootCause(throwable));
                    }
                    try {
                        rawSharedState = captureRecordedSharedStateRaw(active,
                                api, identity);
                    } catch (Throwable throwable) {
                        active.sharedStateGaps.add(SharedStateEvidence.gap(
                                SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.INVOCATION_FAILED, "",
                                rootCause(throwable)));
                    }
                }
            } finally {
                READ_OUT_MEMO.remove();
            }
            String summary = api.finish();
            engineFinished = true;
            if (jsonObjectEnvelope(summary)) {
                // The VM already serialized this large object.
                rawEngineSummary = summary;
            } else if (result != null) {
                result.addProperty("engineSummaryError",
                        "VM summary is not a JSON object");
            }
        } catch (Throwable throwable) {
            if (result != null) {
                result.addProperty("engineSummaryError", rootCause(throwable));
            }
        } finally {
            if (!engineFinished) {
                api.cleanupAfterFailure();
            }
            ACTIVE.remove(active.token, active);
            CURRENT_TOKEN.remove();
            if (!active.abandoned) endLiveSelectedRegion();
        }
        if (result == null) {
            configuration().releaseCandidate(active.activation);
            return false;
        }
        if (!result.has("event")) {
            addResultIdentity(result, active, active.exitKind,
                    active.exceptionType);
        }
        return submitCompletedResultPublication(active, result,
                rawEngineSummary, rawSharedState);
    }

    /** Test-only gate run immediately before asynchronous JSON decoding. */
    private static volatile Runnable beforePublicationDecodeForTests;

    static void setBeforePublicationDecodeForTests(Runnable gate) {
        beforePublicationDecodeForTests = gate;
    }

    /** Transfers one completed native read-out to the bounded daemon pool. */
    private static boolean submitCompletedResultPublication(
            final ActiveRegion active, final JsonObject result,
            final String rawEngineSummary,
            final RawSharedStateReadOut rawSharedState) {
        // The VM context and its raw read-out are complete.  Do not keep the
        // task's admission slot hostage while the daemon performs the much
        // larger JSON decode: a later loop-body turn may be the exact next
        // source phase this bounded address reserved.  Reserve the retained
        // loop evidence before reopening admission, so that next turn sees
        // phase n+1 and cannot claim the same semantic anchor.  Publication
        // remains fail-closed: an enqueue/decode/append failure terminates
        // the task instead of rolling this reservation back underneath a
        // later activation that may already depend on it.
        active.activation.reserveCompletedOccurrence(
                active.configuredSourcePhaseOrdinals,
                active.retainedSemanticAnchorIds);
        active.activation.reserveCompletedEvidence(
                targetReachedByActivation(active),
                bool(result, "relationallyComplete", false));
        configuration().releaseCandidate(active.activation);
        try {
            RESULT_PUBLICATION_EXECUTOR.execute(new Runnable() {
                @Override
                public void run() {
                    publishCompletedResult(active, result, rawEngineSummary,
                            rawSharedState);
                }
            });
            return true;
        } catch (RejectedExecutionException rejected) {
            // Never run a large decode on the RPC owner as a rejection
            // fallback.
            diagAfterVmClose("RESULT_PUBLICATION_REJECTED",
                    rootCause(rejected));
            haltWhenCampaignSettled(active.activation.taskId, 2);
            return false;
        }
    }

    /** Decodes, assembles, appends, and settles one already-closed region. */
    private static void publishCompletedResult(
            ActiveRegion active, JsonObject result,
            String rawEngineSummary, RawSharedStateReadOut rawSharedState) {
        try {
            Runnable gate = beforePublicationDecodeForTests;
            if (gate != null) gate.run();
            assembleRecordedSharedState(active, rawSharedState);
            addRecordedSharedStateToResult(result, active,
                    rawSharedState == null ? evidenceIdentity(active)
                            : rawSharedState.identity);
            boolean written = appendResult(result, rawEngineSummary);
            if (written) {
                configuration().markOccurrencePublished(active.activation);
            }
            haltWhenCampaignSettled(active.activation.taskId,
                    written ? 0 : 2);
        } catch (Throwable failure) {
            // Admission was already reopened after the VM raw read-out.  A
            // failure is terminal because a later activation may have used
            // the reserved loop phase; silently rolling back would make its
            // identity false.
            diagAfterVmClose("RESULT_PUBLICATION_FAILED",
                    rootCause(failure));
            haltWhenCampaignSettled(active.activation.taskId, 2);
        } finally {
            endSelectedResultPublication();
        }
    }

    /** Builds one occurrence result before the VM summary is spliced in. */
    private static void buildCompletedResult(
            JsonObject result, ActiveRegion active,
            RecordedEvidenceIdentity identity) {
        EngineApi api = engine();
        String exitKind = active.exitKind;
        // A loop-bound cut is itself the end of the bounded path.
        boolean boundedPathOutputExit = "CUT".equals(exitKind)
                && active.activation.capturesOutputRelation
                && active.loopBoundCut != null
                && active.replayResourceCut == null;
        boolean boundedResourceOutputExit = "CUT".equals(exitKind)
                && active.activation.capturesOutputRelation
                && active.replayResourceCut != null
                && ReplayLoopResourceCut.valid(active.replayResourceCut)
                && active.replayProgress.complete()
                && active.demandedOutputRelationComplete();
        boolean boundedOutputExit = boundedPathOutputExit
                || boundedResourceOutputExit;
        String completedExitKind = boundedOutputExit
                ? "BOUNDED" : exitKind;
        if (!active.activation.symbolize.isEmpty()
                && !active.pathRecordingStarted
                && !(active.activation.relationOnlySeed()
                && active.demandedOutputRelationComplete())) {
            active.addUnresolvedOnce("NO_SELECTED_INPUT_MATERIALIZED");
        }
        if ("NORMAL".equals(completedExitKind)
                || "BOUNDED".equals(completedExitKind)
                && !boundedResourceOutputExit) {
            captureTrackedFieldOutputs(active);
        }
        populateCompletedResult(result, active, completedExitKind,
                active.exceptionType, active.exitOutput, identity);
        if (!"CUT".equals(completedExitKind)
                && !"BOUNDED".equals(completedExitKind)) {
            try {
                String expression = api.expression(active.exitOutput);
                JsonElement observation = parseJson(expression);
                result.add("rootOutputExpression", observation);
            } catch (Throwable readOutFailed) {
                // A missing rootOutputExpression on a NORMAL or THROW exit
                // already says the read-out did not answer.
            }
        }
    }

    /**
     * Ends the workload once every campaign task has reached a terminal
     * outcome, when the caller asked for that.
     */
    private static void haltWhenCampaignSettled(String taskId, int status) {
        int campaignStatus = configuration().settle(taskId, status);
        if (campaignStatus >= 0 && Boolean.getBoolean(
                HALT_AFTER_SELECTED_RESULT_PROPERTY)) {
            // A halt runs no shutdown hook, so the run's totals are
            // published here or never.
            publishRunTotals();
            Runtime.getRuntime().halt(campaignStatus);
        }
    }

    /**
     * Captures outputs rooted at a nested heap object observed during the
     * region.
     */
    private static void captureTrackedFieldOutputs(ActiveRegion active) {
        for (OutputCaptureSpec request : active.demandedCaptures()) {
            if (!request.capturesRegionExitField()) continue;
            if (active.hasOutputCapture(request.captureBindingId())
                    || active.outputCaptureOccurrences.observed(
                    request.captureBindingId(),
                    request.outputSiteId()) > 0) {
                continue;
            }
            if (request.occurrenceScoped()) {
                active.addUnresolvedOnce(request.captureBindingId()
                        + ": exact bounded heap-write occurrence requires a "
                        + "mutation-site output capture hook");
                continue;
            }
            String rootPort = safe(request.accessRootInputPort());
            Object owner = active.ambiguousFieldAccessOwners.contains(
                    rootPort) ? null
                    : active.fieldAccessOwners.get(rootPort);
            if (owner == null) continue;
            Object value = readExactField(owner, request.fieldSignature());
            if (value == MissingValue.INSTANCE) {
                active.addUnresolvedOnce(request.captureBindingId()
                        + ": exact nested output field is unavailable");
                continue;
            }
            int occurrence = active.nextOutputCaptureOccurrence(request);
            if (active.boundedOutputVersionSlot(request, occurrence)) {
                recordRegionExitFieldOutput(active, request, owner, value,
                        occurrence);
            }
        }
    }

    /**
     * The activation's symbolic inputs, one mint row each: the plain input
     * symbols it minted, then one row per entry of a declared mint site.
     */
    private static JsonArray symbolizedInputs(ActiveRegion active) {
        JsonArray rows = new JsonArray();
        for (String symbol : active.symbolized) {
            JsonObject row = new JsonObject();
            row.addProperty(SymbolicSourceEvidence.SYMBOL, symbol);
            // A locally minted input symbol is a root by construction; only a
            // declared mint site can observe an already-propagated read.
            row.addProperty(SymbolicSourceEvidence.REUSED, false);
            rows.add(row);
        }
        for (JsonObject row : active.symbolizedRows) {
            rows.add(row.deepCopy());
        }
        return rows;
    }

    /** Copies {@code rows} with the identity stamp applied to each. */
    private static JsonArray stamped(List<JsonObject> rows,
                                     RecordedEvidenceIdentity identity) {
        JsonArray stamped = new JsonArray();
        for (JsonObject row : rows) {
            JsonObject copy = row.deepCopy();
            if (identity != null
                    && !RecordedEvidenceIdentity.stamped(copy)) {
                identity.stamp(copy);
            }
            stamped.add(copy);
        }
        return stamped;
    }

    private static void populateCompletedResult(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType, Object output,
            RecordedEvidenceIdentity identity) {
        addResultIdentity(result, active, exitKind, exceptionType);
        if (output instanceof Throwable && !"CUT".equals(exitKind)) {
            result.add("exceptionChain", exceptionChain((Throwable) output));
        }
        if (active.loopBoundCut != null) {
            result.add("pathCut", active.loopBoundCut.deepCopy());
        }
        if (active.replayResourceCut != null) {
            result.add("replayResourceCut",
                    active.replayResourceCut.deepCopy());
        }
        result.add("loopBackedgeTraversals",
                active.loopBackedges.toJson());
        result.add("replayLoopBodies",
                active.loopBackedges.bodiesToJson());
        if (!active.loopCardinalities.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITIES,
                    GSON.toJsonTree(active.loopCardinalities));
        }
        if (!active.loopCardinalityGaps.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITY_GAPS,
                    GSON.toJsonTree(active.loopCardinalityGaps));
        }
        active.validateRegionExitFieldCaptures(exitKind);
        active.nameUnreachedTargetBranch();
        if (active.targetReach != null) {
            result.add("targetReach", active.targetReach);
        }
        result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
        if (!active.outputVersionGaps.isEmpty()) {
            result.add("outputVersionGaps", GSON.toJsonTree(
                    new ArrayList<>(active.outputVersionGaps.values())));
        }
        result.add("symbolizedInputs", symbolizedInputs(active));
        // C2: a read with no recorded lineage is an unconstrained variable
        // this activation named, not a hole in the evidence.  The array is
        // published even when empty: its emptiness is the proof that free
        // symbols did not fire where lineage exists.
        result.add("freeSymbols", GSON.toJsonTree(active.freeSymbols));
        SymbolicSourceEvidence.writeTo(result,
                new ArrayList<>(active.symbolicSources.values()));
        if (!active.activation.configuredSourcePhases.isEmpty()) {
            result.add(CONFIGURED_SOURCE_PHASE_OBSERVATIONS,
                    GSON.toJsonTree(
                            active.configuredSourcePhaseObservations));
            result.add(CONFIGURED_SOURCE_PHASE_GAPS,
                    GSON.toJsonTree(active.configuredSourcePhaseGaps));
        }
        result.add("branchMappings", GSON.toJsonTree(active.branchMappings));
        if (!active.concreteBranchWitnesses.isEmpty()) {
            result.add("concreteBranchWitnesses",
                    GSON.toJsonTree(active.concreteBranchWitnesses));
        }
        result.add("outputCaptures", GSON.toJsonTree(active.outputCaptures));
        // Every evidence row this activation publishes names the run, the
        // session, the activation, and the read-out batch it came from.
        VmHandoffEvidence.writeTo(result, active.vmHandoffEvents);
        if (!active.rpcHandoffGaps.isEmpty()) {
            result.add("rpcHandoffGaps",
                    stamped(active.rpcHandoffGaps, identity));
        }
        if (!active.readCutGates.isEmpty()) {
            result.add("readCutGates",
                    GSON.toJsonTree(active.readCutGates));
        }
        if (!active.readCutGaps.isEmpty()) {
            result.add("readCutGaps", GSON.toJsonTree(active.readCutGaps));
        }
    }

    /** Adds decoded shared-state evidence to an otherwise complete result. */
    private static void addRecordedSharedStateToResult(
            JsonObject result, ActiveRegion active,
            RecordedEvidenceIdentity identity) {
        if (!active.sharedStateRecords.isEmpty()) {
            // Map states travel in this same member, and deliberately: the
            // importer admits a MAP_STATE location through the code path a
            // field location takes, so publishing them in a second member
            // would be the first step towards a second admission rule.
            result.add("sharedFieldVersions", stamped(
                    new ArrayList<>(active.sharedStateRecords.values()),
                    identity));
        }
        JsonArray mapCarriers = new JsonArray();
        for (SharedCarrier carrier : active.sharedCarriers.values()) {
            if (carrier.mapState()) mapCarriers.add(carrier.toJson());
        }
        if (mapCarriers.size() > 0) {
            // Which maps this activation selected, beside the evidence they
            // produced.
            result.add("sharedMapCarriers", mapCarriers);
        }
        if (active.sessionEventLedger != null) {
            result.add("sessionEventLedger",
                    active.sessionEventLedger.deepCopy());
        }
        if (!active.sharedStateGaps.isEmpty()) {
            result.add("sharedStateGaps",
                    stamped(active.sharedStateGaps, identity));
        }
    }

    private static void addResultIdentity(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType) {
        RuntimeTask task = active.activation;
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", task.taskId);
        result.addProperty("exitKind", exitKind);
        result.addProperty("exceptionType", safe(exceptionType));
        // README OCC-1 result-row contract, consumed by the importer:
        // one row per activation of the address, each naming which activation
        // it is and what it did or did not reach.
        result.addProperty("plannedOccurrenceId", task.occurrenceId);
        result.addProperty("occurrenceId", active.occurrenceId());
        result.addProperty("activationOrdinal", active.activationOrdinal);
        result.addProperty("relationallyComplete",
                relationallyComplete(task, active.outputCaptures));
        if (task.capturesTargetReach) {
            // Only a target-reach address selects on this.
            result.addProperty("targetReached",
                    targetReachedByActivation(active));
        }
    }

    private static void symbolizeReceiverFields(ActiveRegion active,
                                               RuntimeTask claimant,
                                               EngineApi api) {
        for (SymbolizeAction action : claimant.symbolize) {
            // Nested/shared heap fields are materialized on their real owner
            // at the field-access hook.
            if (!"RECEIVER_FIELD".equals(action.location)) {
                continue;
            }
            if (!action.fieldPath.isEmpty()) {
                symbolizeFieldPath(active, action, active.receiver,
                        action.fieldPath, api);
                continue;
            }
            DeclaredField declared = FieldPathSpec.declaredField(
                    firstNonBlank(action.accessFieldSignature, action.cell));
            if (declared == null) {
                active.unresolved.add(action.symbol
                        + ": exact receiver field is unavailable");
                continue;
            }
            symbolizeField(active, action, active.receiver,
                    declared.name(), Collections.singletonList(
                            declared.name()), api);
        }
    }

    private static void symbolizeField(ActiveRegion active,
                                       SymbolizeAction action,
                                       Object owner, String symbolicPath,
                                       List<String> exactFieldPath,
                                       EngineApi api) {
        String symbol = action.symbol + "." + safe(symbolicPath);
        try {
            Object value = readExactField(owner,
                    action.exactLeafFieldSignature(exactFieldPath));
            if (value != null && value != MissingValue.INSTANCE
                    && containerValue(value)) {
                if (!trackContainerOrObserveConcrete(active, api, value,
                        action)) {
                    return;
                }
                ensurePathRecordingStarted(active);
                active.recordSymbolizedInputPort(action.symbol, value);
                active.symbolized.add(action.symbol);
            } else {
                api.symbolizeExactField(owner,
                        action.exactLeafFieldSignature(exactFieldPath),
                        symbol);
                ensurePathRecordingStarted(active);
                active.symbolized.add(symbol);
            }
        } catch (Throwable throwable) {
            active.unresolved.add(symbol + ": shallow field symbolize failed: "
                    + rootCause(throwable));
        }
    }

    private static void symbolizeFieldPath(ActiveRegion active,
                                           SymbolizeAction action,
                                           Object root,
                                           List<String> path,
                                           EngineApi api) {
        String label = joinFieldPath(path);
        if (path == null || path.isEmpty() || label.isEmpty()) {
            active.unresolved.add(action.symbol
                    + ": selective argument contains an empty field path");
            return;
        }
        Object leafOwner = resolveFieldPathLeafOwner(root, path);
        if (leafOwner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + label
                    + ": projected field owner is missing");
            return;
        }
        if (leafOwner == null) {
            active.unresolved.add(action.symbol + "." + label
                    + ": projected field owner is null");
            return;
        }
        symbolizeField(active, action, leafOwner, label, path, api);
    }

    private static void applyFieldPathModel(ActiveRegion active,
                                            SymbolizeAction action,
                                            Object root,
                                            List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null || path == null || path.isEmpty()) return;
        Object owner = resolveFieldPathLeafOwner(root, path);
        if (owner == null || owner == MissingValue.INSTANCE) {
            active.unresolved.add(action.symbol + "." + joinFieldPath(path)
                    + ": solver-model field owner is unavailable");
            return;
        }
        applyFieldModel(active, action, owner, path);
    }

    private static void applyFieldModel(ActiveRegion active,
                                        SymbolizeAction action,
                                        Object owner, List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        if (assignment == null) return;
        if (!writeModeledField(owner, action.exactLeafFieldSignature(path),
                assignment, MissingValue.INSTANCE)) {
            active.unresolved.add(action.symbol + "." + joinFieldPath(path)
                    + ": solver model could not be written to real field");
            return;
        }
        active.recordModelAssignment(assignment);
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            List<String> path) {
        ModelAssignment assignment = active.assignment(action, path);
        ModelAssignment applied = null;
        Object modeled = concrete;
        if (assignment != null) {
            modeled = coerceModelValue(assignment.valueType,
                    assignment.value, concrete == null
                            ? null : concrete.getClass());
            if (modeled == UnsupportedReplayValue.INSTANCE) {
                active.unresolved.add(action.symbol
                        + ": unsupported primitive model "
                        + assignment.valueType + "=" + assignment.value);
                modeled = concrete;
            } else {
                applied = assignment;
            }
        }
        Object fresh = freshPrimitiveBox(modeled);
        try {
            EngineApi api = engine();
            api.symbolizeField(fresh, "value", action.symbol);
            ensurePathRecordingStarted(active);
            active.symbolized.add(action.symbol);
            if (applied != null) {
                active.recordModelAssignment(applied);
            }
            return fresh;
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol
                    + ": primitive materialization failed: "
                    + rootCause(throwable));
            return concrete;
        }
    }

    static boolean writeModeledField(
            Object owner, String fieldSignature,
            ModelAssignment assignment,
            Object referenceAlias) {
        Field field = declaredInstanceField(owner, fieldSignature);
        if (field == null) return false;
        try {
            Object value = assignment.referenceAlias()
                    ? referenceAlias
                    : coerceModelValue(assignment.valueType,
                    assignment.value, field.getType());
            if (value == UnsupportedReplayValue.INSTANCE) return false;
            field.set(owner, value);
            return true;
        } catch (Throwable ignored) {
            return false;
        }
    }

    static boolean writeIndexedContainerElement(
            Object container, int index, String valueType, String value) {
        if (container == null || container == MissingValue.INSTANCE
                || index < 0) {
            return false;
        }
        try {
            if (container.getClass().isArray()) {
                if (index >= Array.getLength(container)) return false;
                Object modeled = coerceModelValue(valueType, value,
                        container.getClass().getComponentType());
                if (modeled == UnsupportedReplayValue.INSTANCE
                        || modeled == null
                        && container.getClass().getComponentType()
                        .isPrimitive()) {
                    return false;
                }
                Array.set(container, index, modeled);
                return true;
            }
            if (container instanceof List) {
                List<Object> values = (List<Object>) container;
                if (index >= values.size()) return false;
                Object current = values.get(index);
                Object modeled = "NULL".equals(valueType)
                        ? null : current == null
                        ? UnsupportedReplayValue.INSTANCE
                        : coerceModelValue(valueType, value,
                                current.getClass());
                if (modeled == UnsupportedReplayValue.INSTANCE) {
                    return false;
                }
                values.set(index, modeled);
                return true;
            }
        } catch (Throwable ignored) {
            return false;
        }
        return false;
    }

    static boolean writeContainerTarget(
            Object container, ModelAssignment assignment,
            Object referenceAlias) {
        if ("INDEXED".equals(assignment.containerShape)) {
            if (assignment.containerReferenceAlias()) {
                return referenceAlias != null
                        && referenceAlias != MissingValue.INSTANCE
                        && referenceAlias
                        != UnsupportedReplayValue.INSTANCE
                        && writeIndexedReference(container,
                        assignment.containerIndex, referenceAlias);
            }
            return writeIndexedContainerElement(container,
                    assignment.containerIndex,
                    assignment.valueType, assignment.value);
        }
        if (!"ASSOCIATIVE".equals(assignment.containerShape)) return false;
        if (assignment.iterationTarget()) {
            return writeOrderedIterationTarget(container, assignment,
                    referenceAlias);
        }
        if (assignment.dynamicAssociativeTarget()) return false;
        if (!(container instanceof Map<?, ?>)) return false;
        Object key = containerKey(assignment.containerKeyJavaType,
                assignment.containerKeyValue);
        if (key == UnsupportedReplayValue.INSTANCE) return false;
        return writeAssociativeContainerTarget(container, key, assignment,
                referenceAlias);
    }

    @SuppressWarnings("unchecked")
    static boolean writeAssociativeContainerTarget(
            Object container, Object key, ModelAssignment assignment,
            Object referenceAlias) {
        if (!(container instanceof Map<?, ?>)
                || !"ASSOCIATIVE".equals(assignment.containerShape)) {
            return false;
        }
        Map<Object, Object> map = (Map<Object, Object>) container;
        if (assignment.containerReferenceAlias()) {
            if (referenceAlias == null
                    || referenceAlias == MissingValue.INSTANCE
                    || referenceAlias == UnsupportedReplayValue.INSTANCE
                    || !map.containsKey(key)) {
                return false;
            }
            map.put(key, referenceAlias);
            return true;
        }
        if (!map.containsKey(key)) {
            // Map.get on an absent key already yields null.  Replaying that
            // observation must not turn it into a present-null entry.
            return "NULL".equals(assignment.valueType);
        }
        Object current = map.get(key);
        Object modeled = "NULL".equals(assignment.valueType)
                ? null : current == null
                ? UnsupportedReplayValue.INSTANCE
                : coerceModelValue(assignment.valueType,
                        assignment.value, current.getClass());
        if (modeled == UnsupportedReplayValue.INSTANCE) return false;
        map.put(key, modeled);
        return true;
    }

    @SuppressWarnings("unchecked")
    private static boolean writeOrderedIterationTarget(
            Object container, ModelAssignment assignment,
            Object referenceAlias) {
        int index = assignment.containerIndex;
        if (index < 0) return false;
        try {
            if (container instanceof LinkedHashSet<?>
                    && "KEY".equals(assignment.containerProjection)) {
                List<Object> values = new ArrayList<>(
                        (Set<Object>) container);
                if (index >= values.size()) return false;
                Object current = values.get(index);
                Object modeled = modeledContainerValue(current, assignment,
                        referenceAlias);
                if (modeled == UnsupportedReplayValue.INSTANCE) return false;
                if (!(current == null ? modeled == null
                        : current.equals(modeled))
                        && ((Set<?>) container).contains(modeled)) {
                    return false;
                }
                values.set(index, modeled);
                LinkedHashSet<Object> target =
                        (LinkedHashSet<Object>) container;
                target.clear();
                target.addAll(values);
                return target.size() == values.size();
            }
            if (!(container instanceof LinkedHashMap<?, ?>)) return false;
            LinkedHashMap<Object, Object> target =
                    (LinkedHashMap<Object, Object>) container;
            List<Map.Entry<Object, Object>> entries = new ArrayList<>(
                    target.entrySet());
            if (index >= entries.size()) return false;
            Map.Entry<Object, Object> selected = entries.get(index);
            if ("VALUE".equals(assignment.containerProjection)) {
                Object current = selected.getValue();
                Object modeled = modeledContainerValue(current, assignment,
                        referenceAlias);
                if (modeled == UnsupportedReplayValue.INSTANCE) return false;
                target.put(selected.getKey(), modeled);
                return true;
            }
            if (!"KEY".equals(assignment.containerProjection)) return false;
            Object current = selected.getKey();
            Object modeled = modeledContainerValue(current, assignment,
                    referenceAlias);
            if (modeled == UnsupportedReplayValue.INSTANCE) return false;
            if (!(current == null ? modeled == null
                    : current.equals(modeled))
                    && target.containsKey(modeled)) {
                return false;
            }
            target.clear();
            for (int cursor = 0; cursor < entries.size(); cursor++) {
                Map.Entry<Object, Object> entry = entries.get(cursor);
                target.put(cursor == index ? modeled : entry.getKey(),
                        entry.getValue());
            }
            return target.size() == entries.size();
        } catch (Throwable ignored) {
            return false;
        }
    }

    private static Object modeledContainerValue(
            Object current, ModelAssignment assignment,
            Object referenceAlias) {
        if (assignment.containerReferenceAlias()) {
            return referenceAlias == null
                    || referenceAlias == MissingValue.INSTANCE
                    || referenceAlias == UnsupportedReplayValue.INSTANCE
                    ? UnsupportedReplayValue.INSTANCE : referenceAlias;
        }
        if ("NULL".equals(assignment.valueType)) return null;
        return current == null ? UnsupportedReplayValue.INSTANCE
                : coerceModelValue(assignment.valueType,
                assignment.value, current.getClass());
    }

    private static Object indexedContainerElement(
            Object container, int index) {
        if (container == null || index < 0) return MissingValue.INSTANCE;
        try {
            if (container.getClass().isArray()) {
                return index < Array.getLength(container)
                        ? Array.get(container, index)
                        : MissingValue.INSTANCE;
            }
            if (container instanceof List<?>) {
                List<?> values = (List<?>) container;
                return index < values.size()
                        ? values.get(index) : MissingValue.INSTANCE;
            }
        } catch (Throwable ignored) {
            return MissingValue.INSTANCE;
        }
        return MissingValue.INSTANCE;
    }

    private static Object containerSourceElement(
            Object container, ModelAssignment assignment) {
        if ("INDEXED".equals(assignment.containerSourceShape)) {
            return indexedContainerElement(container,
                    assignment.containerSourceIndex);
        }
        if (!"ASSOCIATIVE".equals(assignment.containerSourceShape)
                || !(container instanceof Map<?, ?>)) {
            return MissingValue.INSTANCE;
        }
        Object key = containerKey(
                assignment.containerSourceKeyJavaType,
                assignment.containerSourceKeyValue);
        Map<?, ?> values = (Map<?, ?>) container;
        return key != UnsupportedReplayValue.INSTANCE
                && values.containsKey(key)
                ? values.get(key) : MissingValue.INSTANCE;
    }

    private static boolean writeIndexedReference(
            Object container, int index, Object value) {
        if (container == null || index < 0) return false;
        try {
            if (container.getClass().isArray()) {
                Class<?> component = container.getClass().getComponentType();
                if (component.isPrimitive()
                        || value != null && !component.isInstance(value)
                        || index >= Array.getLength(container)) {
                    return false;
                }
                Array.set(container, index, value);
                return true;
            }
            if (container instanceof List<?>) {
                List<Object> values = (List<Object>) container;
                if (index >= values.size()) return false;
                values.set(index, value);
                return true;
            }
        } catch (Throwable ignored) {
            return false;
        }
        return false;
    }

    private static Object containerKey(String javaType, String value) {
        String descriptor = javaTypeDescriptor(javaType);
        if ("Z".equals(descriptor)) {
            return coerceModelValue("BOOL", value, Boolean.class);
        }
        if (descriptor.length() == 1
                && "BCSIJ".contains(descriptor)) {
            Class<?> target = "B".equals(descriptor) ? Byte.class
                    : "C".equals(descriptor) ? Character.class
                    : "S".equals(descriptor) ? Short.class
                    : "J".equals(descriptor) ? Long.class : Integer.class;
            return coerceModelValue("INT", value, target);
        }
        if ("Ljava/lang/String;".equals(descriptor)) {
            return unquoteSmtString(value);
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    static Object coerceModelValue(String valueType, String value,
                                   Class<?> requestedType) {
        String type = safe(valueType).toUpperCase();
        String raw = safe(value).trim();
        try {
            // Reference null must be decided before type-specific String
            // decoding.
            if ((requestedType == null || !requestedType.isPrimitive())
                    && ("NULL".equals(type)
                    || "null".equalsIgnoreCase(raw))) {
                return null;
            }
            if (requestedType == boolean.class
                    || requestedType == Boolean.class
                    || "BOOL".equals(type)) {
                return "true".equalsIgnoreCase(raw) || "1".equals(raw);
            }
            if (requestedType == byte.class || requestedType == Byte.class) {
                return Byte.valueOf(raw);
            }
            if (requestedType == short.class || requestedType == Short.class) {
                return Short.valueOf(raw);
            }
            if (requestedType == char.class
                    || requestedType == Character.class) {
                return raw.length() == 1 ? raw.charAt(0)
                        : (char) Integer.parseInt(raw);
            }
            if (requestedType == int.class || requestedType == Integer.class) {
                return Integer.valueOf(raw);
            }
            if (requestedType == long.class || requestedType == Long.class
                    || "INT".equals(type) && requestedType == null) {
                return Long.valueOf(raw);
            }
            if (requestedType == float.class || requestedType == Float.class) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Float.valueOf(decimal);
            }
            if (requestedType == double.class || requestedType == Double.class
                    || "REAL".equals(type) && requestedType == null) {
                String decimal = SmtModelValueCodec.realToJavaLiteral(raw);
                return decimal == null ? UnsupportedReplayValue.INSTANCE
                        : Double.valueOf(decimal);
            }
            if (requestedType == String.class || "STRING".equals(type)) {
                return SmtModelValueCodec.decodeString(raw);
            }
        } catch (RuntimeException ignored) {
            return UnsupportedReplayValue.INSTANCE;
        }
        return UnsupportedReplayValue.INSTANCE;
    }

    private static String unquoteSmtString(String value) {
        return SmtModelValueCodec.decodeString(value);
    }

    private static boolean isPrimitiveBox(Object value) {
        return value instanceof Boolean || value instanceof Byte
                || value instanceof Short || value instanceof Character
                || value instanceof Integer || value instanceof Long
                || value instanceof Float || value instanceof Double;
    }

    /** The value at the end of {@code path}, starting from {@code root}. */
    static Object resolveFieldPathValue(Object root, List<String> path) {
        Object owner = resolveFieldPathLeafOwner(root, path);
        if (owner == null || owner == MissingValue.INSTANCE) return owner;
        return readPathSegment(owner, safe(path.get(path.size() - 1)).trim());
    }

    static Object resolveFieldPathLeafOwner(Object root, List<String> path) {
        if (root == null || path == null || path.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Object current = root;
        for (int index = 0; index + 1 < path.size(); index++) {
            String field = safe(path.get(index)).trim();
            if (field.isEmpty()) {
                return MissingValue.INSTANCE;
            }
            current = readPathSegment(current, field);
            if (current == null || current == MissingValue.INSTANCE) {
                return current;
            }
        }
        String leaf = safe(path.get(path.size() - 1)).trim();
        return leaf.isEmpty() ? MissingValue.INSTANCE : current;
    }

    private static Object readPathSegment(Object receiver, String segment) {
        if (receiver == null || segment == null || segment.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Integer index = pathIndex(segment);
        if (index != null && receiver.getClass().isArray()) {
            return index >= 0 && index < Array.getLength(receiver)
                    ? Array.get(receiver, index) : MissingValue.INSTANCE;
        }
        if (index != null && receiver instanceof List) {
            List<?> values = (List<?>) receiver;
            return index >= 0 && index < values.size()
                    ? values.get(index) : MissingValue.INSTANCE;
        }
        return readField(receiver, segment);
    }

    private static Integer pathIndex(String segment) {
        String value = safe(segment).trim();
        if (value.startsWith("[") && value.endsWith("]")) {
            value = value.substring(1, value.length() - 1).trim();
        }
        if (!value.matches("[0-9]+")) return null;
        try {
            return Integer.valueOf(value);
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private static String joinFieldPath(List<String> path) {
        if (path == null || path.isEmpty()) {
            return "";
        }
        StringBuilder result = new StringBuilder();
        for (String segment : path) {
            String value = safe(segment).trim();
            if (value.isEmpty()) {
                return "";
            }
            if (result.length() > 0) {
                result.append('.');
            }
            result.append(value);
        }
        return result.toString();
    }

    private static void symbolize(ActiveRegion active, SymbolizeAction action,
                                  Object value, EngineApi api) {
        try {
            boolean liveArray = value != null && value.getClass().isArray();
            boolean declaredArray = action.declaresArrayInput(
                    Collections.<String>emptyList());
            if (declaredArray && !liveArray) return;
            if (containerValue(value)) {
                if (!trackContainerOrObserveConcrete(active, api, value,
                        action)) {
                    return;
                }
            } else {
                api.symbolize(value, action.symbol);
            }
            ensurePathRecordingStarted(active);
            active.symbolized.add(action.symbol);
            if (value != null && !liveArray) {
                active.recordSymbolizedInputPort(action.symbol, value);
            }
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol + ": symbolize failed: "
                    + rootCause(throwable));
        }
    }

    private static boolean containerValue(Object value) {
        return value != null && (value.getClass().isArray()
                || value instanceof Map<?, ?>
                || value instanceof Set<?>
                || value instanceof Collection<?>);
    }

    private static void requireTrackedContainer(
            EngineApi api, Object value, String symbol) throws Exception {
        if (!api.trackContainer(value, symbol)) {
            throw new UnsupportedOperationException(
                    "custom VM has no symbolic model for container "
                            + value.getClass().getName());
        }
    }

    /**
     * A bounded container port describes the concrete receiver/cardinality
     * that scopes separately symbolized leaves.
     */
    private static boolean trackContainerOrObserveConcrete(
            ActiveRegion active, EngineApi api, Object value,
            SymbolizeAction action) throws Exception {
        if (api.trackContainer(value, action.symbol)) return true;
        if (!"BOUNDED_CONTAINER_STATE".equals(action.symbolicDemand)) {
            requireTrackedContainer(api, value, action.symbol);
        }
        active.observedInputSlots.add(action.symbol);
        active.recordSymbolizedInputPort(action.symbol, value);
        return false;
    }

    private static Object readField(Object receiver, String name) {
        if (receiver == null || name == null || name.isEmpty()) {
            return MissingValue.INSTANCE;
        }
        Class<?> type = receiver.getClass();
        while (type != null) {
            try {
                Field field = type.getDeclaredField(name);
                if (Modifier.isStatic(field.getModifiers())) {
                    return MissingValue.INSTANCE;
                }
                if (!field.isAccessible()) {
                    field.setAccessible(true);
                }
                return field.get(receiver);
            } catch (NoSuchFieldException ignored) {
                type = type.getSuperclass();
            } catch (Throwable throwable) {
                return MissingValue.INSTANCE;
            }
        }
        return MissingValue.INSTANCE;
    }

    private static Object readExactField(
            Object receiver, String fieldSignature) {
        Field field = declaredInstanceField(receiver, fieldSignature);
        if (field == null) return MissingValue.INSTANCE;
        try {
            return field.get(receiver);
        } catch (Throwable ignored) {
            return MissingValue.INSTANCE;
        }
    }

    private static Field declaredInstanceField(
            Object owner, String fieldSignature) {
        DeclaredField declared = FieldPathSpec.declaredField(fieldSignature);
        return declared == null ? null
                : declaredInstanceField(owner, declared.owner(),
                declared.name(), javaTypeDescriptor(declared.type()), true);
    }

    /** Exact live field named by a VM handoff export. */
    private static Field declaredInstanceField(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        return declaredInstanceField(owner, declaringClass, fieldName,
                descriptor, false);
    }

    /**
     * The one non-static {@code declaringClass#fieldName} of {@code owner}
     * whose type descriptor matches, made accessible.  {@code inherited} also
     * accepts a field the declaring class inherits - which the field-signature
     * form resolves and an exact VM export must not.
     */
    private static Field declaredInstanceField(
            Object owner, String declaringClass, String fieldName,
            String descriptor, boolean inherited) {
        if (owner == null || safe(declaringClass).isEmpty()
                || safe(fieldName).isEmpty() || safe(descriptor).isEmpty()) {
            return null;
        }
        Class<?> type = owner.getClass();
        while (type != null && !declaringClass.equals(type.getName())) {
            type = type.getSuperclass();
        }
        while (type != null) {
            try {
                Field field = type.getDeclaredField(fieldName);
                if (Modifier.isStatic(field.getModifiers())
                        || !descriptor.equals(javaTypeDescriptor(
                        field.getType().getTypeName()))) {
                    return null;
                }
                if (!field.isAccessible()) field.setAccessible(true);
                return field;
            } catch (NoSuchFieldException absent) {
                if (!inherited) return null;
                type = type.getSuperclass();
            } catch (Throwable inaccessible) {
                return null;
            }
        }
        return null;
    }

    private static String exactFieldSignature(Field field) {
        return "<" + field.getDeclaringClass().getName() + ": "
                + field.getType().getTypeName() + " " + field.getName()
                + ">";
    }

    private static ActiveRegion activeRegion() {
        Long token = CURRENT_TOKEN.get();
        return token == null ? null : ownerRegion(token);
    }

    /** Returns null only when no lightweight accessor scope is active. */
    private static Boolean lightweightAccessorContextMatches(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object fieldOwner) {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (context == null) return null;
        ActiveRegion active = activeRegion();
        if (active == null || context.regionToken != active.token
                || context.thread != Thread.currentThread()) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
            return Boolean.FALSE;
        }
        return context.matches(callerMethod, callUnitIndex, callSiteId,
                declaredCallee, fieldOwner);
    }

    private static int lightweightAccessorContextOccurrence() {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        ActiveRegion active = activeRegion();
        if (context == null || active == null
                || context.regionToken != active.token
                || context.thread != Thread.currentThread()) {
            return -1;
        }
        return context.occurrence;
    }

    private static ActiveRegion ownerRegion(long token) {
        ActiveRegion active = ACTIVE.get(token);
        return active != null && active.thread == Thread.currentThread()
                ? active : null;
    }

    @SuppressWarnings("deprecation")
    private static Object freshPrimitiveBox(Object value) {
        if (value instanceof Integer) {
            return new Integer(((Integer) value).intValue());
        }
        if (value instanceof Boolean) {
            return new Boolean(((Boolean) value).booleanValue());
        }
        if (value instanceof Long) {
            return new Long(((Long) value).longValue());
        }
        if (value instanceof Byte) {
            return new Byte(((Byte) value).byteValue());
        }
        if (value instanceof Short) {
            return new Short(((Short) value).shortValue());
        }
        if (value instanceof Character) {
            return new Character(((Character) value).charValue());
        }
        if (value instanceof Float) {
            return new Float(((Float) value).floatValue());
        }
        if (value instanceof Double) {
            return new Double(((Double) value).doubleValue());
        }
        if (value instanceof String) {
            return new String((String) value);
        }
        return value;
    }

    private static boolean instanceOfName(Class<?> type, String expected) {
        if (type == null || expected == null || expected.isEmpty()) {
            return expected == null || expected.isEmpty();
        }
        if (expected.equals(type.getName())) {
            return true;
        }
        for (Class<?> iface : type.getInterfaces()) {
            if (instanceOfName(iface, expected)) {
                return true;
            }
        }
        return instanceOfName(type.getSuperclass(), expected);
    }

    static boolean branchConditionMatches(String expression, boolean outcome,
                                          JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return false;
        }
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(string(object, "_type"))) {
            Boolean requiredValue = booleanValueRequiredByZeroBranch(
                    expression, outcome);
            Boolean representedValue = representedBooleanValue(object);
            return requiredValue != null && representedValue != null
                    && requiredValue.equals(representedValue);
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return false;
        }
        String declared = matcher.group(1);
        String expected = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        String observed = string(object, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))) {
            return false;
        }
        if (safe(expression).matches(".*\\bnull\\b.*")) {
            return symbolicNull(object.get("_left"))
                    || symbolicNull(object.get("_right"));
        }
        return true;
    }

    /** Resolves the Java boolean value selected by a Jimple zero test. */
    private static Boolean booleanValueRequiredByZeroBranch(
            String expression, boolean outcome) {
        String rendered = safe(expression).trim();
        Matcher matcher = BRANCH_OPERATOR.matcher(rendered);
        if (!matcher.find()) return null;
        String declared = matcher.group(1);
        if (!("==".equals(declared) || "!=".equals(declared))) {
            return null;
        }
        String left = rendered.substring(0, matcher.start()).trim();
        String right = rendered.substring(matcher.end()).trim();
        boolean leftZero = "0".equals(left);
        boolean rightZero = "0".equals(right);
        if (leftZero == rightZero) return null;
        String effective = outcome ? declared
                : BranchPredicateAlgebra.complementOperator(declared);
        return "!=".equals(effective);
    }

    /**
     * Returns the underlying Java boolean represented by an asserted engine
     * condition, or {@code null} when the IR node is value-producing or its
     * semantics are not part of the exact codec.
     */
    private static Boolean representedBooleanValue(JsonObject condition) {
        if (!"OpStrExpression".equals(string(condition, "_type"))) {
            return null;
        }
        String operation = string(condition, "_name");
        int expectedArity;
        if ("isEmpty".equals(operation)) {
            expectedArity = 1;
        } else if ("contains".equals(operation)
                || "equals".equals(operation)
                || "startsWith".equals(operation)
                || "endsWith".equals(operation)) {
            expectedArity = 2;
        } else {
            return null;
        }
        if (array(condition, "_param_list").size() != expectedArity) {
            return null;
        }
        return !bool(condition, "_is_not", false);
    }

    /**
     * Soot may describe one selected Jimple edge as {@code >=}/{@code <=}
     * while the asserted VM relation for that concrete edge is the stronger
     * {@code >}, {@code <}, or {@code ==}.  Admit only that forward
     * implication, then canonicalize the retained condition to the actual
     * Jimple predicate below.  Numeric {@code *cmp*} bytecodes now propagate
     * their symbolic trichotomy result to the consuming branch; this is not a
     * fallback to the removed concrete compare-witness mechanism.
     */
    private static boolean observedOperatorImpliesBranch(
            String expected, String observed, boolean nullComparison) {
        if (expected.equals(observed)) {
            return true;
        }
        if (nullComparison) {
            return false;
        }
        return ">=".equals(expected)
                && (">".equals(observed) || "==".equals(observed))
                || "<=".equals(expected)
                && ("<".equals(observed) || "==".equals(observed));
    }

    /** Returns the branch-level predicate while retaining the VM operands. */
    private static JsonElement semanticBranchCondition(
            String expression, boolean outcome, JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return condition;
        }
        JsonObject original = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(string(original, "_type"))) {
            return condition;
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return condition;
        }
        String expected = outcome ? matcher.group(1)
                : BranchPredicateAlgebra.complementOperator(
                matcher.group(1));
        String observed = string(original, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))
                || expected.equals(observed)) {
            return condition;
        }
        JsonObject normalized = original.deepCopy();
        normalized.addProperty("_op", expected);
        return normalized;
    }

    private static String binaryOperator(JsonElement condition) {
        return condition != null && condition.isJsonObject()
                ? string(condition.getAsJsonObject(), "_op") : "";
    }

    private static boolean symbolicNull(JsonElement element) {
        if (element == null || !element.isJsonObject()) {
            return false;
        }
        JsonObject object = element.getAsJsonObject();
        return "SymbolExpression".equals(string(object, "_type"))
                && "N".equals(string(object, "_exp"));
    }

    private static Configuration configuration() {
        Configuration current = configuration;
        if (current != null) {
            return current;
        }
        synchronized (CONFIG_LOCK) {
            if (configuration == null) {
                configuration = Configuration.load();
            }
            return configuration;
        }
    }

    private static EngineApi engine() {
        EngineApi current = engineApi;
        if (current != null) {
            return current;
        }
        synchronized (CONFIG_LOCK) {
            if (engineApi == null) {
                engineApi = EngineApi.load();
            }
            return engineApi;
        }
    }

    private static void resumePathCondition(ActiveRegion active,
                                            EngineApi api) {
        try {
            api.resumePathCondition();
        } catch (Throwable throwable) {
            active.unresolved.add("path-condition recording resume failed: "
                    + rootCause(throwable));
        }
    }

    /**
     * Opens the Java-side branch-observation gate when the first selected
     * input becomes symbolic.
     */
    private static void ensurePathRecordingStarted(ActiveRegion active) {
        if (active.pathRecordingStarted) return;
        active.pathRecordingStarted = true;
    }

    /**
     * Reports the first recorded branch outcome an activation drove the other
     * way.
     */
    static String seedOutcomeConflict(
            Map<String, Set<Boolean>> recorded,
            Map<String, Set<Boolean>> witnessed) {
        for (Map.Entry<String, Set<Boolean>> site : recorded.entrySet()) {
            Set<Boolean> found = witnessed.get(site.getKey());
            if (found == null || found.isEmpty()) continue;
            for (Boolean outcome : site.getValue()) {
                if (!found.contains(outcome)) {
                    return site.getKey() + ": recorded " + site.getValue()
                            + " but witnessed " + found;
                }
            }
        }
        return "";
    }

    /** Records that an activation published nothing, and why. */
    private static void writeSkipped(RuntimeTask activation, String skipKind,
                                     String reason, JsonObject evidence) {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_SKIPPED");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", activation.taskId);
        result.addProperty("skipKind", skipKind);
        result.addProperty("reason", reason);
        if (evidence != null) {
            for (Map.Entry<String, JsonElement> entry
                    : evidence.entrySet()) {
                result.add(entry.getKey(), entry.getValue());
            }
        }
        appendResult(result);
    }

    private static boolean appendResult(JsonObject result) {
        return appendResult(result, null);
    }

    private static boolean appendResult(
            JsonObject result, String rawEngineSummary) {
        return appendResultLine(configuration().resultFile, result,
                rawEngineSummary);
    }

    /**
     * Appends one durable result without depending on interruptible NIO
     * channels.
     */
    static boolean appendResultLine(Path output, JsonObject result,
                                    String rawEngineSummary) {
        synchronized (WRITE_LOCK) {
            try {
                Path parent = output.toAbsolutePath().getParent();
                if (parent != null) {
                    Files.createDirectories(parent);
                }
                String metadata = GSON.toJson(result);
                int close = metadata.lastIndexOf('}');
                if (close < 0) {
                    throw new IOException("result metadata is not a JSON object");
                }
                try (BufferedWriter writer = new BufferedWriter(
                        new OutputStreamWriter(new FileOutputStream(
                                output.toFile(), true),
                                StandardCharsets.UTF_8))) {
                    writer.write(metadata, 0, close);
                    if (rawEngineSummary != null) {
                        if (result.size() > 0) writer.write(',');
                        writer.write("\"engineSummary\":");
                        writer.write(rawEngineSummary);
                    }
                    writer.write(metadata, close,
                            metadata.length() - close);
                    writer.newLine();
                }
                return true;
            } catch (IOException exception) {
                System.err.println("Causynth could not write concolic result: "
                        + exception);
                return false;
            }
        }
    }

    private static boolean jsonObjectEnvelope(String value) {
        if (value == null) return false;
        int start = 0;
        int end = value.length() - 1;
        while (start <= end && Character.isWhitespace(value.charAt(start))) {
            start++;
        }
        while (end >= start && Character.isWhitespace(value.charAt(end))) {
            end--;
        }
        return start <= end && value.charAt(start) == '{'
                && value.charAt(end) == '}';
    }

    private static boolean diagnosticsEnabled() {
        Boolean cached = diagnostics;
        if (cached != null) return cached;
        boolean enabled;
        try {
            enabled = Boolean.parseBoolean(
                    safe(System.getProperty(DIAGNOSTICS_PROPERTY)));
        } catch (Throwable ignored) {
            enabled = false;
        }
        diagnostics = enabled;
        return enabled;
    }

    /**
     * Writes one diagnostic line with path-condition recording paused, so the
     * trace can never manufacture a condition of the program under test.
     */
    static void diag(String event, String detail) {
        if (!diagnosticsEnabled()) return;
        EngineApi api = engine();
        boolean paused = false;
        try {
            api.pausePathCondition();
            paused = true;
        } catch (Throwable ignored) {
            // A missing engine still leaves the line worth printing.
        }
        try {
            diagLine(event, detail);
        } finally {
            if (paused) {
                try {
                    api.resumePathCondition();
                } catch (Throwable ignored) {
                    // Resume failure is already reported by the real hooks.
                }
            }
        }
    }

    /** Diagnostic for daemon publication, where no VM context may be called. */
    private static void diagAfterVmClose(String event, String detail) {
        if (diagnosticsEnabled()) diagLine(event, detail);
    }

    /** The line itself, which never fails the replay or the publication. */
    private static void diagLine(String event, String detail) {
        try {
            System.err.println("CAUSYNTH-DIAG|"
                    + System.currentTimeMillis() + "|t"
                    + Thread.currentThread().getId() + "|heapMB"
                    + (Runtime.getRuntime().totalMemory()
                    - Runtime.getRuntime().freeMemory()) / 1048576L + "|"
                    + safe(event) + "|" + safe(detail));
        } catch (Throwable ignored) {
        }
    }

    /**
     * Indexed access to a serialized path condition without materializing
     * every element.
     *
     * <p>A branch hook needs exactly two facts from that document: how many
     * conditions the VM has accumulated, and the one element the VM's exact
     * event says this branch owns - an index the event stream, a few kilobytes
     * wide, already carries.</p>
     */
    static final class PathConditionElements {
        static final PathConditionElements EMPTY =
                new PathConditionElements(new JsonArray());
        private static final String SCAN_MODE = "SCAN";
        private static final String TREE_MODE = "TREE";
        private static final String WINDOW_MODE = "WINDOW_SCAN";

        private final String raw;
        private final int[] bounds;
        private final JsonArray tree;
        /** Absolute index of element 0, and the exclusive end of the window. */
        private final int base;
        private final int windowEnd;
        /** Conditions the thread has accumulated, window or not. */
        private final int size;
        private final boolean windowed;
        /** One hook may attest and then consume the same exact condition. */
        private final JsonElement[] parsed;

        private PathConditionElements(String raw, int[] bounds) {
            this(raw, bounds, null, 0, bounds.length / 2, bounds.length / 2,
                    false);
        }

        private PathConditionElements(JsonArray tree) {
            this(null, null, tree, 0, tree.size(), tree.size(), false);
        }

        private PathConditionElements(String raw, int[] bounds, JsonArray tree,
                                      int base, int windowEnd, int size,
                                      boolean windowed) {
            this.raw = raw;
            this.bounds = bounds;
            this.tree = tree;
            this.base = base;
            this.windowEnd = windowEnd;
            this.size = size;
            this.windowed = windowed;
            this.parsed = raw == null ? null
                    : new JsonElement[bounds.length / 2];
        }

        /** Reads a serialized path condition. */
        static PathConditionElements of(String raw) {
            if (raw == null) return EMPTY;
            char[] document = raw.toCharArray();
            int[] bounds = scanElements(document, 0, document.length);
            if (bounds != null) return new PathConditionElements(raw, bounds);
            JsonElement parsed = parseJson(raw);
            return parsed.isJsonArray()
                    ? new PathConditionElements(parsed.getAsJsonArray())
                    : EMPTY;
        }

        /**
         * Reads one {@code CONCOLIC_PATH_CONDITION_RANGE} envelope as the
         * conditions at absolute indices {@code [startIndex, endIndex)}.
         */
        static PathConditionElements window(String envelope, int expectedStart) {
            if (envelope == null) return null;
            char[] document = envelope.toCharArray();
            int[] members = members(document, WINDOW_MEMBERS);
            if (members == null) return null;
            int start = integerMember(document, members, 0, -1);
            int end = integerMember(document, members, 1, -1);
            int watermark = integerMember(document, members, 2, -1);
            int declaredCount = integerMember(document, members, 3, -1);
            if (start != expectedStart || end < start || watermark < 0) {
                return null;
            }
            if (members[8] < 0) return null;
            int[] bounds = scanElements(document, members[8], members[9]);
            if (bounds == null) return null;
            int count = bounds.length / 2;
            // The window's own indices are the authority on what it holds.
            if (count != end - start || declaredCount != count) return null;
            return new PathConditionElements(envelope, bounds, null, start,
                    end, watermark, true);
        }

        /** Conditions the thread has accumulated, not just this window's. */
        int size() {
            return size;
        }

        JsonElement get(int index) {
            if (index < base || index >= windowEnd) {
                throw new IndexOutOfBoundsException(
                        "path condition index " + index + " outside ["
                                + base + "," + windowEnd + ") of " + size);
            }
            int offset = index - base;
            if (tree != null) return tree.get(offset);
            JsonElement cached = parsed[offset];
            if (cached == null) {
                cached = parseJson(raw.substring(
                        bounds[2 * offset], bounds[2 * offset + 1]));
                parsed[offset] = cached;
            }
            return cached;
        }

        /** Which reader answered, for the replay's own diagnostics. */
        String mode() {
            if (windowed) return WINDOW_MODE;
            return tree == null ? SCAN_MODE : TREE_MODE;
        }

        /** The members {@link #window} needs, in the order it reads them. */
        private static final String[] WINDOW_MEMBERS = {
                "startIndex", "endIndex", "pathConditionWatermark",
                "conditionCount", "conditions"};

        /**
         * Bounds of every element of the JSON array occupying
         * {@code [from, to)}, or {@code null} when that region is not one this
         * scanner can split with certainty.
         */
        private static int[] scanElements(char[] document, int from, int to) {
            if (document == null || from < 0 || to > document.length
                    || from >= to) {
                return null;
            }
            int index = skipWhitespace(document, from);
            if (index >= to || document[index] != '[') return null;
            index = skipWhitespace(document, index + 1);
            if (index >= to) return null;
            int[] bounds = new int[64];
            int count = 0;
            if (document[index] == ']') {
                index++;
            } else {
                while (true) {
                    if (!valueStart(document[index])) return null;
                    int end = skipValue(document, index);
                    if (end <= index || end > to) return null;
                    if (2 * count == bounds.length) {
                        bounds = Arrays.copyOf(bounds, 2 * bounds.length);
                    }
                    bounds[2 * count] = index;
                    bounds[2 * count + 1] = end;
                    count++;
                    index = skipWhitespace(document, end);
                    if (index >= to) return null;
                    char delimiter = document[index];
                    if (delimiter == ']') {
                        index++;
                        break;
                    }
                    if (delimiter != ',') return null;
                    index = skipWhitespace(document, index + 1);
                    if (index >= to) return null;
                }
            }
            return skipWhitespace(document, index) == to
                    ? Arrays.copyOf(bounds, 2 * count) : null;
        }

        /**
         * Bounds of the named members of one JSON object, walked once at the
         * top level, or {@code null} when the document is not one object of
         * complete members.
         *
         * <p>Searching the text for a quoted name would find one inside a
         * serialized expression - a recorded bytecode position is a string the
         * VM copied from the program - and would then read a value belonging
         * to a condition as if it were the envelope's.</p>
         *
         * @return two slots per requested name, {@code -1} when absent
         */
        private static int[] members(char[] document, String[] names) {
            int[] found = new int[2 * names.length];
            Arrays.fill(found, -1);
            int length = document.length;
            int index = skipWhitespace(document, 0);
            if (index >= length || document[index] != '{') return null;
            index = skipWhitespace(document, index + 1);
            if (index >= length) return null;
            if (document[index] == '}') return found;
            while (true) {
                if (document[index] != '"') return null;
                int keyEnd = skipString(document, index);
                if (keyEnd < 0) return null;
                int nameStart = index + 1;
                int nameEnd = keyEnd - 1;
                index = skipWhitespace(document, keyEnd);
                if (index >= length || document[index] != ':') return null;
                int valueStart = skipWhitespace(document, index + 1);
                if (valueStart >= length || !valueStart(document[valueStart])) {
                    return null;
                }
                int valueEnd = skipValue(document, valueStart);
                if (valueEnd <= valueStart) return null;
                for (int slot = 0; slot < names.length; slot++) {
                    if (found[2 * slot] >= 0
                            || !nameEquals(document, nameStart, nameEnd,
                            names[slot])) {
                        continue;
                    }
                    found[2 * slot] = valueStart;
                    found[2 * slot + 1] = valueEnd;
                }
                index = skipWhitespace(document, valueEnd);
                if (index >= length) return null;
                if (document[index] == '}') return found;
                if (document[index] != ',') return null;
                index = skipWhitespace(document, index + 1);
                if (index >= length) return null;
            }
        }

        /** Whether an unescaped member key spells {@code name}. */
        private static boolean nameEquals(char[] document, int from, int to,
                                          String name) {
            if (to - from != name.length()) return false;
            for (int offset = 0; offset < name.length(); offset++) {
                if (document[from + offset] != name.charAt(offset)) {
                    return false;
                }
            }
            return true;
        }

        /** One member read as a plain JSON integer, or {@code fallback}. */
        private static int integerMember(char[] document, int[] members,
                                         int slot, int fallback) {
            int from = members[2 * slot];
            int to = members[2 * slot + 1];
            if (from < 0 || to <= from) return fallback;
            boolean negative = document[from] == '-';
            int index = negative ? from + 1 : from;
            if (index >= to) return fallback;
            long value = 0L;
            for (; index < to; index++) {
                char digit = document[index];
                if (digit < '0' || digit > '9') return fallback;
                value = value * 10L + (digit - '0');
                if (value > Integer.MAX_VALUE) return fallback;
            }
            return (int) (negative ? -value : value);
        }

        /** The characters a strict JSON value may begin with. */
        private static boolean valueStart(char first) {
            return first == '{' || first == '[' || first == '"'
                    || first == '-' || (first >= '0' && first <= '9')
                    || first == 't' || first == 'f' || first == 'n';
        }

        /**
         * End of the value starting at {@code start}, or a non-positive
         * distance when the document ends inside it.
         */
        private static int skipValue(char[] document, int start) {
            int length = document.length;
            int index = start;
            int depth = 0;
            while (index < length) {
                char current = document[index];
                if (current == '"') {
                    index = skipString(document, index);
                    if (index < 0) return -1;
                    if (depth == 0) return index;
                    continue;
                }
                if (current == '{' || current == '[') {
                    depth++;
                    index++;
                    continue;
                }
                if (current == '}' || current == ']') {
                    if (depth == 0) return index;
                    depth--;
                    index++;
                    if (depth == 0) return index;
                    continue;
                }
                if (depth == 0 && (current == ','
                        || Character.isWhitespace(current))) {
                    return index;
                }
                index++;
            }
            return -1;
        }

        /** Index after the string starting at its opening quote. */
        private static int skipString(char[] document, int start) {
            int length = document.length;
            for (int index = start + 1; index < length; index++) {
                char current = document[index];
                if (current == '\\') {
                    index++;
                    continue;
                }
                if (current == '"') return index + 1;
            }
            return -1;
        }

        private static int skipWhitespace(char[] document, int start) {
            int index = start;
            int length = document.length;
            while (index < length
                    && Character.isWhitespace(document[index])) {
                index++;
            }
            return index;
        }
    }

    private static JsonElement parseJson(String value) {
        if (value == null || value.trim().isEmpty()) {
            return new JsonObject();
        }
        try {
            return new JsonParser().parse(value);
        } catch (RuntimeException ignored) {
            return GSON.toJsonTree(value);
        }
    }

    private static String rootCause(Throwable throwable) {
        Throwable current = throwable;
        while (current instanceof InvocationTargetException
                && ((InvocationTargetException) current).getTargetException() != null) {
            current = ((InvocationTargetException) current).getTargetException();
        }
        return current == null ? "unknown" : current.toString();
    }

    private static JsonArray exceptionChain(Throwable throwable) {
        JsonArray result = new JsonArray();
        Set<Throwable> seen = Collections.newSetFromMap(
                new java.util.IdentityHashMap<Throwable, Boolean>());
        Throwable current = throwable;
        while (current != null && result.size() < 16 && seen.add(current)) {
            JsonObject item = new JsonObject();
            item.addProperty("type", current.getClass().getName());
            item.addProperty("message", safe(current.getMessage()));
            result.add(item);
            current = current.getCause();
        }
        return result;
    }

    private static String safe(String value) {
        return value == null ? "" : value;
    }

    enum MissingValue { INSTANCE }

    private enum UnsupportedReplayValue { INSTANCE }

    private static final class AccessorCallContext {
        private final long contextToken;
        private final long regionToken;
        private final Thread thread;
        private final String callerMethod;
        private final int callUnitIndex;
        private final String callSiteId;
        private final String declaredCallee;
        private final Object receiver;
        private final int occurrence;
        private final AccessorCallContext previous;

        private AccessorCallContext(
                long contextToken, long regionToken, Thread thread,
                String callerMethod, int callUnitIndex, String callSiteId,
                String declaredCallee, Object receiver,
                int occurrence,
                AccessorCallContext previous) {
            this.contextToken = contextToken;
            this.regionToken = regionToken;
            this.thread = thread;
            this.callerMethod = callerMethod;
            this.callUnitIndex = callUnitIndex;
            this.callSiteId = callSiteId;
            this.declaredCallee = declaredCallee;
            this.receiver = receiver;
            this.occurrence = occurrence;
            this.previous = previous;
        }

        private boolean matches(
                String actualCallerMethod, int actualCallUnitIndex,
                String actualCallSiteId, String actualDeclaredCallee,
                Object actualFieldOwner) {
            return callerMethod.equals(safe(actualCallerMethod))
                    && callUnitIndex == actualCallUnitIndex
                    && callSiteId.equals(safe(actualCallSiteId))
                    && declaredCallee.equals(safe(actualDeclaredCallee))
                    && receiver == actualFieldOwner;
        }
    }

    private static final class SwitchExpectation {
        private final String branchKind;
        private final List<Integer> caseKeys;
        private final int observedSuccessorIndex;

        private SwitchExpectation(String branchKind, List<Integer> caseKeys,
                                  int observedSuccessorIndex) {
            this.branchKind = branchKind;
            this.caseKeys = Collections.unmodifiableList(
                    new ArrayList<>(caseKeys));
            this.observedSuccessorIndex = observedSuccessorIndex;
        }

        private static SwitchExpectation parse(
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

        private boolean caseArm() {
            return observedSuccessorIndex < caseKeys.size();
        }
    }

    private static final class VmBranchEventAttestation {
        private final List<Integer> conditionIndices;
        private final boolean valid;
        private final String error;

        private VmBranchEventAttestation(List<Integer> conditionIndices,
                                         boolean valid,
                                         String error) {
            this.conditionIndices = Collections.unmodifiableList(
                    new ArrayList<>(conditionIndices));
            this.valid = valid;
            this.error = safe(error);
        }

        private static VmBranchEventAttestation valid(
                List<Integer> conditionIndices) {
            return new VmBranchEventAttestation(conditionIndices, true, "");
        }

        private static VmBranchEventAttestation invalid(String error) {
            return new VmBranchEventAttestation(
                    Collections.<Integer>emptyList(), false, error);
        }
    }

    private static final class PreparedBranch {
        private final long handle;
        private final String method;
        private final int unitIndex;
        private final String expression;
        private final int occurrence;

        private PreparedBranch(long handle, String method, int unitIndex,
                               String expression, int occurrence) {
            this.handle = handle;
            this.method = safe(method);
            this.unitIndex = unitIndex;
            this.expression = safe(expression);
            this.occurrence = occurrence;
        }

        private boolean matches(String actualMethod, int actualUnitIndex,
                                String actualExpression) {
            return method.equals(safe(actualMethod))
                    && unitIndex == actualUnitIndex
                    && expression.equals(safe(actualExpression));
        }
    }

    /**
     * Activation-local ordinals for repeated executions of one hook.  A new
     * region activation owns a new counter, so no runtime event id or
     * process-global invocation ordinal becomes replay identity.
     */
    static final class OccurrenceCounter {
        private final Map<String, Integer> occurrences =
                new LinkedHashMap<>();

        int local(String method, int unitIndex, String local) {
            return observe("LOCAL\u0000" + safe(method) + "#u"
                    + unitIndex + "::" + safe(local));
        }

        int methodArgument(String method, int argumentIndex) {
            return observe("ARGUMENT\u0000" + safe(method) + "#arg"
                    + argumentIndex);
        }

        int observedMethodArgument(String method, int argumentIndex) {
            return observed("ARGUMENT\u0000" + safe(method) + "#arg"
                    + argumentIndex);
        }

        int field(String method, int unitIndex) {
            return observe("FIELD\u0000" + safe(method) + "#u" + unitIndex);
        }

        int observe(String captureBindingId, String outputSiteId) {
            return observe(captureKey(captureBindingId, outputSiteId));
        }

        int observed(String captureBindingId, String outputSiteId) {
            return observed(captureKey(captureBindingId, outputSiteId));
        }

        private static String captureKey(String captureBindingId,
                                         String outputSiteId) {
            String binding = safe(captureBindingId);
            return binding + "\u0000"
                    + firstNonBlank(outputSiteId, binding);
        }

        private int observe(String key) {
            int occurrence = observed(key) + 1;
            occurrences.put(key, occurrence);
            return occurrence;
        }

        private int observed(String key) {
            return occurrences.getOrDefault(key, 0);
        }
    }

    /** One selected mutator receiver waiting for its method completion. */
    static final class PendingMutationCapture {
        private final OutputCaptureSpec request;
        private final Object container;
        private final int occurrence;
        private final int versionOrdinal;

        PendingMutationCapture(OutputCaptureSpec request,
                               Object container, MutationCaptureIndex index) {
            this.request = request;
            this.container = container;
            this.occurrence = index.selection;
            this.versionOrdinal = index.version;
        }
    }

    /** The two indices a selected mutation carries. */
    static final class MutationCaptureIndex {
        private final int selection;
        private final int version;

        MutationCaptureIndex(int selection, int version) {
            this.selection = selection;
            this.version = version;
        }
    }

    /** One nested invocation of a method that owns a selected mutator. */
    static final class MutationMethodScope {
        private int observed;
        private int versionOrdinal;
        private PendingMutationCapture pending;
        private boolean ambiguousContainer;
        private Object atomicPreparedReceiver;

        /** How this invocation absorbed one selected mutation. */
        enum Selection { ANCHORED, FOLDED, AMBIGUOUS, IGNORED }

        /**
         * A mutation relation denotes the container state at the definition
         * invocation's normal exit.
         */
        Selection offer(PendingMutationCapture candidate) {
            if (ambiguousContainer) return Selection.IGNORED;
            if (pending == null) {
                pending = candidate;
                return Selection.ANCHORED;
            }
            if (pending.container == candidate.container) {
                return Selection.FOLDED;
            }
            pending = null;
            ambiguousContainer = true;
            return Selection.AMBIGUOUS;
        }

        /** The first selected Atomic call owns this invocation's pre-state. */
        boolean claimAtomicPreparation(Object receiver) {
            if (atomicPreparedReceiver != null) return false;
            atomicPreparedReceiver = receiver;
            return true;
        }

    }

    private static final class ActiveRegion {
        private final long token;
        /**
         * The task this activation is currently answering.
         *
         * <p>Not final.  One region root may carry several selected
         * occurrences of the same region -- HDFS-11741 plans occurrence
         * {@code #1} and {@code #9} of the balancer's {@code Dispatcher$1}
         * -- and which of them an activation can answer is only knowable at
         * its exit, from the boundary it actually reached.  The claimants
         * share one VM region context; this names the one that answered.</p>
         */
        private RuntimeTask activation;
        /**
         * This activation's ordinal within its address, taken at admission so
         * every symbol, mint row and handoff lineage it publishes can name
         * the occurrence it belongs to rather than the planned address.
         */
        private int activationOrdinal;
        /** VM context whose writes belong to this materialized activation. */
        private long vmContextId;
        /**
         * Other open occurrences of this same root that this one activation
         * may answer instead, in plan order.
         */
        private final List<RuntimeTask> siblingClaimants = new ArrayList<>();
        private final Object receiver;
        private final Thread thread;
        private final AtomicBoolean finished = new AtomicBoolean();
        private boolean prepared;
        /**
         * The declared target branch event this occurrence decided, or {@code
         * null} while it has not decided one.
         */
        private JsonObject targetReach;
        /** Terminal outcome, frozen when the occurrence stops running. */
        private boolean abandoned;
        private boolean closed;
        /** A selected response input attached; later requests are new hops. */
        /** Loop bodies this activation has charged. */
        private volatile long chargedLoopBodies;
        /**
         * The stable causal context this candidate observed while it was live:
         * the logical sources it ran on and the external request scopes it ran
         * inside.
         */
        private final Set<String> observedSourceKeys = new LinkedHashSet<>();
        /**
         * Every stable source this occurrence can be attributed to by the
         * application's own registration.
         *
         * <p>Two kinds of evidence, both produced by the replay itself.</p>
         */
        private Set<String> attributedSourceKeys() {
            Set<String> keys = new LinkedHashSet<>(observedSourceKeys);
            SourceRef registered = RuntimeTraceContext.sourceFor(receiver);
            if (registered != null) keys.add(registered.key());
            return keys;
        }

        private synchronized boolean beginClose() {
            if (closed) return false;
            closed = true;
            return true;
        }

        private String exitKind = "";
        private String exceptionType = "";
        private Object exitOutput;
        private final List<String> symbolized = new ArrayList<>();
        /**
         * One published row per entry of a declared mint site: what was
         * minted, or which propagated expression was kept instead.
         */
        private final List<JsonObject> symbolizedRows = new ArrayList<>();
        /** Reads that found no expression and were freed instead of gapped. */
        private final List<JsonObject> freeSymbols = new ArrayList<>();
        /** Per-(activation, read site) free-symbol entry count. */
        private final Map<String, Integer> freeSymbolOrdinals =
                new LinkedHashMap<>();
        /** Exact configured source roots materialized by this activation. */
        private final Map<String, JsonObject> symbolicSources =
                new LinkedHashMap<>();
        /** Replay ordinal of each exact configured-source hook site. */
        /**
         * Mint sites, and the fields they mint, this activation reached.
         *
         * <p>A configured source mints one symbol per element of the walk it
         * runs, and those occurrences are recorded here rather than in
         * {@link #observedInputSlots}: the mint hook is a call-site phase, not
         * an instrumented field access.  A capture anchored on one of those
         * per-element ports is answered by the site having run.</p>
         */
        private final Set<String> reachedConfiguredSourceSites =
                new LinkedHashSet<>();
        private final Set<String> mintedConfiguredSourceFields =
                new LinkedHashSet<>();
        /** Phase entries used by this activation; committed on publication. */
        private final Map<String, Integer> configuredSourcePhaseOrdinals =
                new LinkedHashMap<>();
        /** Ordered, structured replay ledger emitted with the raw result. */
        private final List<JsonObject> configuredSourcePhaseObservations =
                new ArrayList<>();
        /** Structured fail-closed phase replay gaps. */
        private final List<JsonObject> configuredSourcePhaseGaps =
                new ArrayList<>();
        private final Set<String> configuredSourcePhaseGapIdentities =
                new LinkedHashSet<>();
        /** Exact semantic anchors this activation will commit if published. */
        private final Set<String> retainedSemanticAnchorIds =
                new LinkedHashSet<>();
        private final Set<String> unresolved = new LinkedHashSet<>();
        private final List<JsonObject> branchMappings = new ArrayList<>();
        /**
         * Branches this activation executed before its symbolic gate opened.
         */
        private final List<JsonObject> concreteBranchWitnesses =
                new ArrayList<>();
        private final List<JsonObject> outputCaptures = new ArrayList<>();
        /** One named gap per output site that ran past its version cap. */
        private final Map<String, JsonObject> outputVersionGaps =
                new LinkedHashMap<>();
        /**
         * Case-local references into the VM's own handoff ledger: the
         * declared port an attach landed on and the export event the
         * {@code VALUE_HANDOFF} edge relates it to.
         */
        private final List<JsonObject> vmHandoffEvents = new ArrayList<>();
        /**
         * VM export event most recently published at each declared port.
         *
         * <p>README {@code RPC-1}: written down from the VM's own export
         * answer so the producer's interaction row can name it.</p>
         */
        private final Map<String, Long> exportEventByPort =
                new LinkedHashMap<>();
        private final Set<String> stagedCommunicationPorts =
                new LinkedHashSet<>();
        private final List<JsonObject> rpcHandoffGaps = new ArrayList<>();

        /**
         * Whether this turn carried one of its region's selected causal
         * anchors: the VM answered the declared attach of an exchange the
         * plan selected this region for.
         *
         * <p>The witness is the VM's own answer at the declared attach.
         * Nothing here consults the plan for
         * what "should" have arrived; a turn the exchange did not reach is
         * simply not anchored.  This evidence exists only once the exchange
         * has landed, which is inside the turn, not at its entry.</p>
         */
        private synchronized Set<String> carriedSemanticAnchorIds() {
            Set<String> carried = new LinkedHashSet<>();
            for (JsonObject observation
                    : configuredSourcePhaseObservations) {
                String phaseId = string(observation, "matchedPhaseId");
                if (!phaseId.isEmpty()) {
                    carried.add(activation.sourcePhaseAnchorId(phaseId));
                }
            }
            Set<String> anchors = activation.causalAnchorPorts();
            for (JsonObject handoff : vmHandoffEvents) {
                String portId = string(handoff, "portId");
                if (anchors.contains(portId)) {
                    carried.add(activation.attachAnchorId(portId));
                }
            }
            carried.remove("");
            return carried;
        }
        /**
         * Shared locations this activation selected as symbolic carriers, and
         * the evidence read back from them.
         */
        private final Map<String, SharedCarrier> sharedCarriers =
                new LinkedHashMap<>();
        /** Exact access-owner carrier declarations already selected here. */
        private final Set<String> accessOwnerCarrierSelections =
                new LinkedHashSet<>();
        private final Map<String, JsonObject> sharedStateRecords =
                new LinkedHashMap<>();
        private final List<JsonObject> sharedStateGaps = new ArrayList<>();

        /**
         * Read-cut gates this activation admitted as observations, and the
         * named gaps of the ones it refused.
         */
        private final List<JsonObject> readCutGates = new ArrayList<>();
        private final List<JsonObject> readCutGaps = new ArrayList<>();
        private JsonObject sessionEventLedger;
        /** Read-out batch every record of this activation is stamped with. */
        private long evidenceSnapshot;
        private final Set<String> materialized = new LinkedHashSet<>();
        private final Set<String> observedInputSlots =
                new LinkedHashSet<>();
        private final Set<String> appliedModelAssignments =
                new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        // Outcomes this activation actually witnessed at each static branch
        // site, restricted to the mappings a summary keeps.
        private final Map<String, Set<Boolean>> witnessedOutcomes =
                new LinkedHashMap<>();
        private final OccurrenceCounter
                materializationOccurrences =
                new OccurrenceCounter();
        private final Map<String, Integer> accessorCallOccurrences =
                new LinkedHashMap<>();
        private final OccurrenceCounter outputCaptureOccurrences =
                new OccurrenceCounter();
        private final Map<String, List<String>> guardedOutputCaptureFailures =
                new LinkedHashMap<>();
        private final Map<String, PendingMutationCapture>
                pendingMutationCaptures = new LinkedHashMap<>();
        private final Map<String, Deque<MutationMethodScope>>
                mutationMethodScopes = new LinkedHashMap<>();
        private final Deque<Long> loopBudgetScopes = new ArrayDeque<>();
        private final LoopBackedgeBudget loopBackedges;
        /** Current fixed-count invocation by runtime natural-loop id. */
        private final Map<String, DynamicLoopCardinality>
                activeLoopCardinalities = new LinkedHashMap<>();
        /** Next occurrence ordinal by runtime natural-loop id. */
        private final Map<String, Integer> loopCardinalityOccurrences =
                new LinkedHashMap<>();
        /** Exact N for every dynamic fixed-count invocation in this path. */
        private final List<JsonObject> loopCardinalities = new ArrayList<>();
        /** Ambiguous/malformed cardinality observations remain coverage. */
        private final List<JsonObject> loopCardinalityGaps =
                new ArrayList<>();
        private final Map<Long, PreparedBranch> preparedBranches =
                new LinkedHashMap<>();
        private final IdentityHashMap<Object, String>
                symbolizedInputPorts = new IdentityHashMap<>();
        private final IdentityHashMap<Object, Map<String, Object>>
                referenceAliasSnapshots = new IdentityHashMap<>();
        private final ReplayFieldWrites writtenFields =
                new ReplayFieldWrites();
        private final Map<String, Object> fieldAccessOwners =
                new LinkedHashMap<>();
        private final Set<String> ambiguousFieldAccessOwners =
                new LinkedHashSet<>();
        private final Map<String, Integer> associativeAccessOccurrences =
                new LinkedHashMap<>();
        private final ReplayProgress replayProgress;
        private int replayCaptureWatermark = -1;
        private long preparedBranchSequence;
        private long loopBudgetScopeSequence;
        private int lastPathConditionSize;
        private JsonObject loopBoundCut;
        private JsonObject replayResourceCut;
        private boolean pathRecordingStarted;

        private ActiveRegion(long token, RuntimeTask activation,
                             Object receiver, Thread thread) {
            this.token = token;
            this.activation = activation;
            this.receiver = receiver;
            this.thread = thread;
            this.loopBackedges = new LoopBackedgeBudget(
                    activation.loopBound);
            this.replayProgress = new ReplayProgress(
                    activation.replayContract);
        }

        /**
         * Every output boundary this activation must record a row for: the
         * bindings of the task it entered under and of every other open
         * occurrence it may answer instead.
         *
         * <p>Capture rows are keyed by {@code captureBindingId}, which is
         * per-task, so a row recorded only for the entered task can never
         * satisfy a sibling's boundary.  Recording the union is what makes
         * the exit-time settlement below a decision rather than a guess.</p>
         */
        /** Gives back this activation's ordinal; it published nothing. */
        private void releaseActivationOrdinal() {
            if (activationOrdinal <= 0) return;
            activation.releaseActivationOrdinal(activationOrdinal);
            activationOrdinal = 0;
        }

        /** This activation's own occurrence identity: address plus ordinal. */
        private String occurrenceId() {
            return activationOrdinal <= 0 ? safe(activation.occurrenceId)
                    : safe(activation.occurrenceId) + "#a" + activationOrdinal;
        }

        /** The occurrences riding this activation, entered one first. */
        private List<RuntimeTask> claimants() {
            if (siblingClaimants.isEmpty()) {
                return Collections.singletonList(activation);
            }
            List<RuntimeTask> all = new ArrayList<>();
            all.add(activation);
            all.addAll(siblingClaimants);
            return all;
        }

        /** One demanded binding of this activation, from any claimant. */
        private OutputCaptureSpec demandedCapture(String captureBindingId) {
            OutputCaptureSpec request =
                    activation.outputCapture(captureBindingId);
            if (request != null) return request;
            for (RuntimeTask sibling : siblingClaimants) {
                request = sibling.outputCapture(captureBindingId);
                if (request != null) return request;
            }
            return null;
        }

        /** Every live-in action of every occurrence riding this
         *  activation, entered one first. */
        private List<SymbolizeAction> claimantSymbolize() {
            if (siblingClaimants.isEmpty()) return activation.symbolize;
            List<SymbolizeAction> union =
                    new ArrayList<>(activation.symbolize);
            for (RuntimeTask sibling : siblingClaimants) {
                union.addAll(sibling.symbolize);
            }
            return union;
        }

        /** As {@link #claimantSymbolize()}, for declared-only slots. */
        private List<SymbolizeAction> claimantDeclaredSymbolize() {
            if (siblingClaimants.isEmpty()) {
                return activation.declaredSymbolize;
            }
            List<SymbolizeAction> union =
                    new ArrayList<>(activation.declaredSymbolize);
            for (RuntimeTask sibling : siblingClaimants) {
                union.addAll(sibling.declaredSymbolize);
            }
            return union;
        }

        private List<OutputCaptureSpec> demandedCaptures() {
            if (siblingClaimants.isEmpty()) return activation.outputCaptures;
            List<OutputCaptureSpec> union =
                    new ArrayList<>(activation.outputCaptures);
            for (RuntimeTask sibling : siblingClaimants) {
                union.addAll(sibling.outputCaptures);
            }
            return union;
        }

        /**
         * Charges one body of this loop to the replay resource cap, returning
         * the cut that ends the activation once the cap is spent.
         */
        private ReplayLoopResourceCut chargeLoopBody(String loopId) {
            int maxBodies = activation.maxLoopBodies(loopId);
            chargedLoopBodies++;
            long entered = loopBackedges.recordBody(loopId);
            if (entered <= maxBodies) return null;
            ReplayLoopResourceCut cut = new ReplayLoopResourceCut(
                    loopId, maxBodies, entered);
            if (replayResourceCut == null) {
                replayResourceCut = cut.toJson();
            }
            return cut;
        }

        private synchronized void recordLoopCardinality(
                String loopId, int cardinality) {
            if (loopId.isEmpty() || cardinality < 0) {
                loopCardinalityGap(
                        LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS,
                        loopId, 0,
                        "fixed-count array observation has no valid loop id "
                                + "or non-negative cardinality");
                return;
            }
            DynamicLoopCardinality current =
                    activeLoopCardinalities.get(loopId);
            if (current == null) {
                int occurrence = loopCardinalityOccurrences
                        .getOrDefault(loopId, 0) + 1;
                loopCardinalityOccurrences.put(loopId, occurrence);
                current = new DynamicLoopCardinality(
                        occurrence, cardinality);
                activeLoopCardinalities.put(loopId, current);
                JsonObject row = new JsonObject();
                row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, loopId);
                row.addProperty(LoopBoundPolicy.DYNAMIC_OCCURRENCE,
                        occurrence);
                row.addProperty(LoopBoundPolicy.LOOP_CARDINALITY,
                        cardinality);
                row.addProperty("cardinalityAuthority",
                        LoopBoundPolicy.PATH_CARDINALITY_AUTHORITY);
                loopCardinalities.add(row);
                return;
            }
            if (current.cardinality != cardinality) {
                loopCardinalityGap(
                        LoopBoundPolicy.PATH_LOOP_COUNT_AMBIGUOUS,
                        loopId, current.occurrence,
                        "one dynamic fixed-count occurrence observed N="
                                + current.cardinality + " and N="
                                + cardinality);
            }
        }

        private synchronized void completeLoopCardinality(String loopId) {
            if (!loopId.isEmpty()) activeLoopCardinalities.remove(loopId);
        }

        private void loopCardinalityGap(String reason, String loopId,
                                        int occurrence, String detail) {
            JsonObject row = new JsonObject();
            row.addProperty("kind", "LOOP_CARDINALITY_COVERAGE_GAP");
            row.addProperty("authority", "RUNTIME_LOOP_CARDINALITY_GAP_V1");
            row.addProperty("reason", reason);
            row.addProperty(LoopBoundPolicy.RUNTIME_LOOP_ID, loopId);
            if (occurrence > 0) {
                row.addProperty(LoopBoundPolicy.DYNAMIC_OCCURRENCE,
                        occurrence);
            }
            row.addProperty("detail", detail);
            loopCardinalityGaps.add(row);
        }

        /**
         * Whether a replay-resource cut happened strictly after the VM had
         * captured the whole demanded output relation.
         *
         * <p>README TERM-1: <em>every</em> demanded port, not any one of
         * them.</p>
         */
        private LoopBoundCut loopBoundCut(
                String backedgeId, int maxTraversals, String reason) {
            LoopBoundCut cut = new LoopBoundCut(backedgeId, maxTraversals,
                    reason);
            if (loopBoundCut == null) {
                loopBoundCut = cut.toJson();
                if (!activation.capturesOutputRelation) {
                    addUnresolvedOnce("LOOP_BOUND_PATH_CUT:"
                            + cut.backedgeId + ':' + cut.reason);
                }
            }
            return cut;
        }

        private int nextBranchOccurrence(String siteId) {
            Integer previous = branchOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            branchOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        private void witnessOutcome(String siteId, boolean outcome) {
            Set<Boolean> outcomes = witnessedOutcomes.get(siteId);
            if (outcomes == null) {
                outcomes = new LinkedHashSet<>();
                witnessedOutcomes.put(siteId, outcomes);
            }
            outcomes.add(outcome);
        }

        /** Records a branch while the symbolic gate is closed. */
        private void recordConcreteBranch(
                String method, int unitIndex, boolean outcome) {
            try {
                String site = siteId(method, unitIndex);
                if (!activation.declaresBranch(site)) {
                    Set<Boolean> seen = witnessedOutcomes.get(site);
                    if (seen == null || !seen.contains(outcome)) {
                        witnessOutcome(site, outcome);
                        concreteBranchWitnesses.add(concreteBranchWitness(
                                method, unitIndex, outcome));
                    }
                    return;
                }
                int occurrence = nextBranchOccurrence(site);
                JsonObject mapping = branchMapping(method, unitIndex,
                        occurrence);
                mapping.addProperty("rawPathConditionSize", 0);
                mapping.addProperty("rawPathConditionBaseline", 0);
                mapping.add("concreteObservation",
                        ExactConcreteBranchObservation.attested(site,
                                safe(method), unitIndex, occurrence, outcome)
                                .toJson());
                branchMappings.add(mapping);
                witnessOutcome(site, outcome);
                if (activation.targetBranchSite.equals(site)
                        && activation.targetBranchOccurrence == occurrence) {
                    recordTargetReach(site, occurrence, outcome);
                }
            } catch (Throwable ignored) {
                // Observation must never alter the workload's own outcome.
            }
        }

        private String seedOutcomeConflict() {
            return ConcolicRegionRuntime.seedOutcomeConflict(
                    activation.seedOutcomes, witnessedOutcomes);
        }

        private boolean observeReplayBranch(
                String siteId, int occurrence, boolean outcome) {
            boolean matched = replayProgress.observe(
                    siteId, occurrence, outcome);
            diag("REPLAY_OBSERVE", siteId + " occ=" + occurrence
                    + " outcome=" + outcome + " matched=" + matched
                    + " complete=" + replayProgress.complete()
                    + " failed=" + replayProgress.failed()
                    + " watermark=" + replayCaptureWatermark
                    + " captures=" + outputCaptures.size());
            if (replayProgress.failed()) {
                addUnresolvedOnce("REPLAY_PREFIX_MISMATCH:"
                        + replayProgress.failure());
            }
            if (activation.replayContract != null
                    && replayCaptureWatermark < 0
                    && replayProgress.complete()) {
                // The demanded decision has only just been made.
                replayCaptureWatermark = outputCaptures.size();
            }
            return matched;
        }

        /**
         * Whether this activation has already walked a branch the recorded
         * replay prefix forbids.
         */
        private boolean replayPrefixContradicted() {
            return activation.replayContract != null
                    && replayProgress.failed();
        }

        private int nextLocalMaterializationOccurrence(
                String method, int unitIndex, String local) {
            return materializationOccurrences.local(method, unitIndex,
                    local);
        }

        private int nextOutputCaptureOccurrence(OutputCaptureSpec request) {
            return outputCaptureOccurrences.observe(
                    request.captureBindingId(), request.outputSiteId());
        }

        private void beginMutationMethodStateOutput(
                OutputCaptureSpec request) {
            mutationMethodScopes.computeIfAbsent(
                    request.captureBindingId(), ignored -> new ArrayDeque<>())
                    .push(new MutationMethodScope());
            loopBudgetScopes.push(++loopBudgetScopeSequence);
        }

        private boolean claimAtomicMutationPreparation(
                OutputCaptureSpec request, Object receiver) {
            if (!request.definitionInvocationScoped()) return true;
            Deque<MutationMethodScope> scopes = mutationMethodScopes.get(
                    request.captureBindingId());
            MutationMethodScope scope = scopes == null
                    ? null : scopes.peek();
            if (scope == null) {
                addUnresolvedOnce(request.captureBindingId()
                        + ": atomic mutation hook executed outside its "
                        + "definition invocation scope");
                return false;
            }
            return scope.claimAtomicPreparation(receiver);
        }

        private MutationCaptureIndex nextMutationOutputCaptureOccurrence(
                OutputCaptureSpec request) {
            if (!request.definitionInvocationScoped()) {
                int occurrence = nextOutputCaptureOccurrence(request);
                return new MutationCaptureIndex(occurrence, occurrence);
            }
            Deque<MutationMethodScope> scopes = mutationMethodScopes.get(
                    request.captureBindingId());
            MutationMethodScope scope = scopes == null ? null : scopes.peek();
            if (scope == null) {
                addUnresolvedOnce(request.captureBindingId()
                        + ": mutation hook executed outside its definition "
                        + "invocation scope");
                return null;
            }
            // One completed definition invocation publishes one state version.
            if (scope.versionOrdinal == 0) {
                scope.versionOrdinal = outputCaptureOccurrences.observe(
                        request.captureBindingId(), request.outputSiteId());
            }
            return new MutationCaptureIndex(++scope.observed,
                    scope.versionOrdinal);
        }

        private void deferMutationStateOutput(
                OutputCaptureSpec request, Object container,
                MutationCaptureIndex index) {
            PendingMutationCapture pending = new PendingMutationCapture(
                    request, container, index);
            if (request.definitionInvocationScoped()) {
                Deque<MutationMethodScope> scopes = mutationMethodScopes.get(
                        request.captureBindingId());
                MutationMethodScope scope = scopes == null
                        ? null : scopes.peek();
                if (scope == null) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": selected mutation has no definition "
                            + "invocation scope");
                    return;
                }
                if (scope.offer(pending)
                        == MutationMethodScope.Selection.AMBIGUOUS) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": selected mutations of different containers "
                            + "in one definition invocation");
                }
                return;
            }
            PendingMutationCapture previous = pendingMutationCaptures.put(
                    request.captureBindingId(), pending);
            if (previous != null) {
                // A method completion cannot be attributed unambiguously when
                // the same logical capture is pending twice (for example via
                // recursion).  Drop both instead of exporting either state.
                pendingMutationCaptures.remove(request.captureBindingId());
                addUnresolvedOnce(request.captureBindingId()
                        + ": multiple selected mutations pending before "
                        + "method completion");
            }
        }

        private PendingMutationCapture takeMutationStateOutput(
                OutputCaptureSpec request) {
            String captureBindingId = request.captureBindingId();
            if (request.definitionInvocationScoped()) {
                Deque<MutationMethodScope> scopes = mutationMethodScopes.get(
                        captureBindingId);
                MutationMethodScope scope = scopes == null
                        ? null : scopes.poll();
                if (scope == null) {
                    addUnresolvedOnce(captureBindingId
                            + ": mutation method completion has no matching "
                            + "entry");
                    return null;
                }
                if (!loopBudgetScopes.isEmpty()) {
                    loopBudgetScopes.pop();
                }
                if (scopes.isEmpty()) {
                    mutationMethodScopes.remove(captureBindingId);
                }
                return scope.pending;
            }
            PendingMutationCapture pending = pendingMutationCaptures.remove(
                    safe(captureBindingId));
            if (pending != null && !pending.request.captureBindingId().equals(
                    safe(captureBindingId))) {
                addUnresolvedOnce(safe(captureBindingId)
                        + ": mutation completion binding mismatch");
                return null;
            }
            return pending;
        }

        /**
         * A CFG loop bound is local to the dynamic definition invocation that
         * executes it.
         */
        private PreparedBranch prepareBranch(
                String method, int unitIndex, String expression,
                EngineApi api) throws Exception {
            String site = safe(method) + "#u" + unitIndex;
            int occurrence = nextBranchOccurrence(site);
            long sequence = ++preparedBranchSequence;
            if (sequence > Integer.MAX_VALUE) {
                addUnresolvedOnce(site + "#" + occurrence
                        + ": prepared branch sequence overflow");
                return null;
            }
            long handle = (sequence << 32)
                    | (occurrence & 0xffffffffL);
            PreparedBranch prepared = new PreparedBranch(handle, method,
                    unitIndex, expression, occurrence);
            preparedBranches.put(handle, prepared);
            return prepared;
        }

        private PreparedBranch takePreparedBranch(long handle) {
            return handle <= 0L ? null : preparedBranches.remove(handle);
        }

        private void validateRegionExitFieldCaptures(String exitKind) {
            boolean normal = "NORMAL".equals(exitKind)
                    || activation.capturesOutputRelation
                    && "BOUNDED".equals(exitKind);
            for (OutputCaptureSpec request : activation.outputCaptures) {
                String observedUnit = request.definitionInvocationScoped()
                        ? "definition invocation(s)"
                        : "hook occurrence(s)";
                int matches = 0;
                for (JsonObject capture : outputCaptures) {
                    if (successfulExactOutputCapture(request, capture)) {
                        matches++;
                    }
                }
                if (normal && matches < 1) {
                    // Only now is a failed occurrence a real gap: no
                    // occurrence of this binding produced the relation.
                    for (String failure : guardedOutputCaptureFailures
                            .getOrDefault(request.captureBindingId(),
                                    Collections.<String>emptyList())) {
                        addUnresolvedOnce(failure);
                    }
                    addUnresolvedOnce(request.captureBindingId()
                            + ": bounded replay produced no output relation; "
                            + "observed " + outputCaptureOccurrences.observed(
                            request.captureBindingId(), request.outputSiteId())
                            + " " + observedUnit + " and captured " + matches);
                } else if (!normal && matches != 0) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": field output captured on " + exitKind
                            + " exit");
                }
                // The size of the bound this site actually needed, stated
                // once now that both counts are final.
                int observed = outputCaptureOccurrences.observed(
                        request.captureBindingId(), request.outputSiteId());
                int capacity = activation.loopBound.maxBackedgeTraversals();
                if (observed > capacity) {
                    boundedOutputVersionGap(request, capacity, observed,
                            matches);
                }
            }
            if (!normal) outputCaptures.clear();
        }

        private boolean hasOutputCapture(String captureBindingId) {
            for (JsonObject capture : outputCaptures) {
                if (safe(captureBindingId).equals(
                        string(capture, "captureBindingId"))) {
                    return true;
                }
            }
            return false;
        }

        /** The occurrence that declared one demanded binding. */
        private RuntimeTask owningClaimant(String captureBindingId) {
            if (activation.outputCapture(captureBindingId) != null) {
                return activation;
            }
            for (RuntimeTask sibling : siblingClaimants) {
                if (sibling.outputCapture(captureBindingId) != null) {
                    return sibling;
                }
            }
            return activation;
        }

        /**
         * Whether the counted occurrence still has a bounded version slot.
         *
         * <p>README's resource rule applies to the versions past it: they are
         * named once per port and never silently absent.</p>
         */
        private boolean boundedOutputVersionSlot(
                OutputCaptureSpec request, int occurrence) {
            int capacity = activation.loopBound.maxBackedgeTraversals();
            if (occurrence >= 1 && occurrence <= capacity) return true;
            boundedOutputVersionGap(request, capacity, occurrence, 0);
            return false;
        }

        /**
         * Names one output site that ran past its bounded version capacity.
         *
         * <p>README's resource rule: truncation of selected evidence is a
         * named gap and is never read as the evidence being absent.  The row
         * is stated structurally at the only layer that knows the counts, so
         * no later layer reconstructs it from prose.</p>
         */
        private void boundedOutputVersionGap(
                OutputCaptureSpec request, int capacity, int observed,
                int captured) {
            String binding = safe(request.captureBindingId());
            JsonObject gap = outputVersionGaps.get(binding);
            if (gap == null) {
                gap = new JsonObject();
                gap.addProperty("schemaVersion", 1);
                gap.addProperty("kind", "OUTPUT_VERSION_ALIGNMENT_GAP");
                gap.addProperty("authority",
                        "BOUNDED_OUTPUT_VERSION_CAPACITY_V1");
                gap.addProperty("captureBindingId", binding);
                gap.addProperty("outputSiteId", request.outputSiteId());
                gap.addProperty("versionCapacity", capacity);
                gap.addProperty("versionsObserved", 0);
                gap.addProperty("versionsCaptured", 0);
                outputVersionGaps.put(binding, gap);
            }
            int versions = Math.max(observed,
                    integer(gap, "versionsObserved", 0));
            int held = Math.max(captured,
                    integer(gap, "versionsCaptured", 0));
            gap.addProperty("versionsObserved", versions);
            gap.addProperty("versionsCaptured", held);
            gap.addProperty("reason", binding + " ran past its bounded output"
                    + " version capacity " + capacity + " at "
                    + request.outputSiteId() + "; " + held + " of " + versions
                    + " observed version(s) were captured, so this relation"
                    + " is a bounded prefix of the run and not a closed one");
        }

        /**
         * Whether every demanded output relation of this occurrence produced
         * at least one admitted version by now.
         */
        private boolean demandedOutputRelationComplete() {
            List<JsonObject> captures = replayCaptureWatermark < 0
                    ? outputCaptures
                    : outputCaptures.subList(replayCaptureWatermark,
                    outputCaptures.size());
            return completeExactOutputBoundary(
                    activation.capturesOutputRelation,
                    activation.outputCaptures, captures);
        }

        /**
         * A relation-only seed that reached every demanded semantic output is
         * still a valid witnessed constant relation when none of its optional
         * solver dimensions materialized on this replay.
         */
        /**
         * Names a declared target branch event this occurrence never decided.
         */
        private void nameUnreachedTargetBranch() {
            if (targetReach != null || !activation.declaresTargetBranch()) {
                return;
            }
            addUnresolvedOnce("TARGET_BRANCH_NOT_REACHED: "
                    + activation.targetBranchLabel()
                    + " was not decided before this occurrence ended at "
                    + safe(exitKind));
        }

        /**
         * Records the declared target branch event this occurrence decided.
         */
        private void recordTargetReach(String siteId, int occurrence,
                                       boolean outcome) {
            if (targetReach != null) return;
            JsonObject reach = new JsonObject();
            reach.addProperty("kind", "TARGET_REACH_EVENT");
            reach.addProperty("siteId", safe(siteId));
            reach.addProperty("occurrence", occurrence);
            reach.addProperty("outcome", outcome);
            targetReach = reach;
            diag("TARGET_REACHED", "token=" + token + " site=" + safe(siteId)
                    + "#" + occurrence);
        }

        private void recordFieldAccessOwner(String symbol, Object owner) {
            if (safe(symbol).isEmpty() || owner == null) return;
            if (ambiguousFieldAccessOwners.contains(symbol)) return;
            Object previous = fieldAccessOwners.putIfAbsent(symbol, owner);
            if (previous != null && previous != owner) {
                fieldAccessOwners.remove(symbol);
                ambiguousFieldAccessOwners.add(symbol);
                addUnresolvedOnce(symbol
                        + ": multiple nested field owners observed");
            }
        }

        private void addUnresolvedOnce(String detail) {
            String value = safe(detail);
            if (!value.isEmpty()) unresolved.add(value);
        }

        /**
         * Counts one entry of one declared mint site.
         *
         * <p>The catalog is a list of mint SITES, not a selection: any entry
         * of a known site mints, and the ordinal is the entry count.  A hook
         * that fires at a site the catalog does not name is still a gap -
         * that is a plan/instrumentation disagreement, not a free
         * occurrence.</p>
         */
        private synchronized SourceSiteEntry observeConfiguredSourceEntry(
                String sourceId, String runtimeFieldSignature) {
            CausynthTraceRecorder.ActiveCallSiteContext context =
                    CausynthTraceRecorder.currentCallSiteContext();
            List<ConfiguredSourcePhaseContract.Occurrence> declaration =
                    new ArrayList<>();
            String site = context == null ? "" : context.siteId();
            for (ConfiguredSourcePhaseContract.Occurrence candidate
                    : activation.configuredSourcePhases) {
                if (candidate.phase()
                        == ConfiguredSourcePhaseContract.Phase.PUBLISH
                        && candidate.sourceId().equals(safe(sourceId))
                        && (site.isEmpty()
                        || candidate.siteId().equals(site))) {
                    declaration.add(candidate);
                }
            }
            if (context == null) {
                addSourcePhaseGap("ACTIVE_CALL_SITE_MISSING",
                        declaration.isEmpty() ? null : declaration.get(0),
                        "PUBLISH hook for " + safe(sourceId)
                                + " has no active call-site context");
                return null;
            }
            if (declaration.isEmpty()) {
                addSourcePhaseGap("EXTRA", null,
                        "PUBLISH " + site + " is outside the replay-call "
                                + "catalog");
                return null;
            }
            String ordinalKey = "PUBLISH\n" + safe(sourceId) + "\n" + site;
            int localOrdinal = configuredSourcePhaseOrdinals.merge(
                    ordinalKey, 1, Integer::sum);
            int ordinal = activation.configuredSourcePhaseOrdinal(
                    ordinalKey, localOrdinal);
            boolean cataloged = ordinal <= declaration.size();
            ConfiguredSourcePhaseContract.Occurrence matched = cataloged
                    ? declaration.get(ordinal - 1)
                    : declaration.get(declaration.size() - 1);
            if (!cataloged) {
                addSourcePhaseGap("EXTRA", matched,
                        "PUBLISH " + site + " occurrence " + ordinal
                                + " exceeds the frozen phase catalog size "
                                + declaration.size());
                return null;
            }
            if (!matched.fieldSignature().equals(
                    safe(runtimeFieldSignature))
                    || !matched.runtimeDeclaredCallee().equals(
                    context.declaredCallee())) {
                addSourcePhaseGap("DECLARATION_MISMATCH", matched,
                        "runtime field/callee differs from the catalog site");
                return null;
            }
            reachedConfiguredSourceSites.add(matched.siteId());
            if (!site.isEmpty()) reachedConfiguredSourceSites.add(site);
            mintedConfiguredSourceFields.add(matched.fieldSignature());
            recordConfiguredSourcePhaseObservation(matched, context);
            return new SourceSiteEntry(matched, site, ordinal, cataloged);
        }

        /**
         * Records that one named catalog entry was reached.  The row carries
         * runtime facts only: everything else about the entry is read off the
         * catalog row {@code matchedPhaseId} names.
         */
        private void recordConfiguredSourcePhaseObservation(
                ConfiguredSourcePhaseContract.Occurrence matched,
                CausynthTraceRecorder.ActiveCallSiteContext context) {
            JsonObject observation = new JsonObject();
            observation.addProperty("schemaVersion", 1);
            observation.addProperty("kind",
                    "CONFIGURED_SOURCE_PHASE_OBSERVATION");
            observation.addProperty("authority",
                    "EXACT_ACTIVE_CALL_SITE_REPLAY_V1");
            observation.addProperty("observationIndex",
                    configuredSourcePhaseObservations.size() + 1);
            observation.addProperty("matchedPhaseId", matched.phaseId());
            observation.addProperty("ownerCallId", context.ownerCallId());
            observation.addProperty("invocationId", context.invocationId());
            configuredSourcePhaseObservations.add(observation);
        }

        /** Publishes one mint row for one entry of a declared site. */
        private synchronized void recordConfiguredSourceMint(
                SourceSiteEntry entry, String sourceId,
                String fieldSignature, String symbol,
                JsonElement expression, boolean reused) {
            JsonObject row = new JsonObject();
            row.addProperty("sourceId", safe(sourceId));
            row.addProperty("occurrenceId", occurrenceId());
            row.addProperty("siteId", entry.siteId);
            row.addProperty("ordinal", entry.ordinal);
            row.addProperty("fieldSignature", safe(fieldSignature));
            row.addProperty("symbol", safe(symbol));
            row.add("expression", expression == null
                    ? JsonNull.INSTANCE : expression);
            row.addProperty("reused", reused);
            symbolizedRows.add(row);
        }

        /**
         * Mints one free symbol for a read whose value carried no expression.
         *
         * <p>C2: a read with no recorded lineage is an unconstrained variable,
         * not an unresolved gap.  Only a read that cannot be symbolized at all
         * - no owner, unsupported Java type - stays in
         * {@code unresolvedInputs}.</p>
         */
        private synchronized int nextFreeSymbolOrdinal(String siteId) {
            return freeSymbolOrdinals.merge(safe(siteId), 1, Integer::sum);
        }

        /** Names one read this activation left unconstrained, on purpose. */
        private synchronized void recordFreeSymbol(
                String symbol, String vmSymbol, String siteId, int ordinal,
                String javaType, String reason) {
            JsonObject row = new JsonObject();
            row.addProperty("symbol", safe(symbol));
            // What the composer matches a model value against: the VM never
            // saw the readable name.
            row.addProperty("vmSymbol", safe(vmSymbol));
            row.addProperty("siteId", safe(siteId));
            row.addProperty("occurrenceId", occurrenceId());
            row.addProperty("ordinal", ordinal);
            row.addProperty("javaType", safe(javaType));
            row.addProperty("reason", safe(reason));
            freeSymbols.add(row);
        }

        private synchronized void addSourcePhaseGap(
                String gapKind,
                ConfiguredSourcePhaseContract.Occurrence phase,
                String detail) {
            String phaseId = phase == null ? "" : phase.phaseId();
            String identity = safe(gapKind) + "\n" + phaseId + "\n"
                    + safe(detail);
            if (!configuredSourcePhaseGapIdentities.add(identity)) return;
            JsonObject gap = new JsonObject();
            gap.addProperty("schemaVersion", 1);
            gap.addProperty("kind", "CONFIGURED_SOURCE_PHASE_GAP");
            gap.addProperty("authority",
                    "FAIL_CLOSED_EXACT_PHASE_REPLAY_V1");
            gap.addProperty("gapKind", safe(gapKind));
            gap.addProperty("phaseId", phaseId);
            gap.addProperty("phaseKind",
                    phase == null ? "" : phase.phase().name());
            gap.addProperty("siteId",
                    phase == null ? "" : phase.siteId());
            gap.addProperty("baselineOrdinal",
                    phase == null ? 0 : phase.baselineOrdinal());
            gap.addProperty("sourceId",
                    phase == null ? "" : phase.sourceId());
            gap.addProperty("detail", safe(detail));
            configuredSourcePhaseGaps.add(gap);
            addUnresolvedOnce("CONFIGURED_SOURCE_PHASE_" + safe(gapKind)
                    + ": " + (phaseId.isEmpty() ? safe(detail)
                    : phaseId + ": " + safe(detail)));
        }

        private synchronized void recordSymbolicSource(
                String sourcePhaseId, JsonObject evidence) {
            JsonObject prior = symbolicSources.putIfAbsent(sourcePhaseId,
                    evidence.deepCopy());
            if (prior != null && !prior.equals(evidence)) {
                addUnresolvedOnce(sourcePhaseId
                        + ": configured source phase produced conflicting "
                        + "expressions");
            }
        }

        /**
         * The read-out batch this activation's evidence belongs to, allocated
         * on first use so a capture outside the exit batch still gets its own
         * comparable ordinal rather than borrowing a later one.
         */
        private long evidenceSnapshot() {
            if (evidenceSnapshot == 0L) {
                evidenceSnapshot = EVIDENCE_SNAPSHOTS.incrementAndGet();
            }
            return evidenceSnapshot;
        }

        /**
         * Holds one occurrence's capture failure without yet calling it a gap.
         */
        private void addGuardedOutputCaptureFailure(String captureBindingId,
                                                    String detail) {
            String binding = safe(captureBindingId);
            String value = safe(detail);
            if (value.isEmpty()) return;
            if (binding.isEmpty()) {
                addUnresolvedOnce(value);
                return;
            }
            List<String> failures = guardedOutputCaptureFailures
                    .computeIfAbsent(binding, ignored -> new ArrayList<>());
            if (!failures.contains(value)) failures.add(value);
        }

        private void recordSymbolizedInputPort(String symbol, Object value) {
            if (value == null) return;
            String previous = symbolizedInputPorts.get(value);
            symbolizedInputPorts.put(value, previous == null
                    || previous.equals(symbol) ? symbol : "");
        }

        private void snapshotReferenceAliasSources(Object owner) {
            if (owner == null || referenceAliasSnapshots.containsKey(owner)) {
                return;
            }
            Map<String, Object> snapshot = new LinkedHashMap<>();
            for (ModelAssignment assignment
                    : activation.modelAssignments) {
                if (!assignment.referenceAlias()) continue;
                for (SymbolizeAction action : activation.symbolize) {
                    if (!assignment.referenceSourceInputSymbol.equals(
                            action.symbol)
                            || !action.declaresReferenceInput()
                            || !action.accessOwnerClass.isEmpty()
                            && !instanceOfName(owner.getClass(),
                            action.accessOwnerClass)) {
                        continue;
                    }
                    Object sourceOwner = action.leafOwner(owner);
                    Object value = sourceOwner == null
                            || sourceOwner == MissingValue.INSTANCE
                            ? MissingValue.INSTANCE
                            : readExactField(sourceOwner,
                            action.exactLeafFieldSignature());
                    if (value != MissingValue.INSTANCE
                            && !assignment.containerSourceShape.isEmpty()) {
                        value = containerSourceElement(value, assignment);
                    }
                    snapshot.put(assignment.key, value);
                }
            }
            referenceAliasSnapshots.put(owner, snapshot);
        }

        private Object referenceAliasValue(
                ModelAssignment assignment, Object owner) {
            if (!assignment.referenceAlias()) return MissingValue.INSTANCE;
            Map<String, Object> snapshot = referenceAliasSnapshots.get(owner);
            if (snapshot == null
                    || !snapshot.containsKey(assignment.key)) {
                return UnsupportedReplayValue.INSTANCE;
            }
            Object value = snapshot.get(assignment.key);
            return value == MissingValue.INSTANCE
                    ? UnsupportedReplayValue.INSTANCE : value;
        }

        private ModelAssignment assignment(SymbolizeAction action,
                                           List<String> path) {
            ModelAssignment selected = null;
            for (ModelAssignment candidate : activation.modelAssignments) {
                if (!candidate.matches(action, path)
                        || !action.repeatedPrimitiveAccessor()
                        && appliedModelAssignments.contains(candidate.key)) {
                    continue;
                }
                if (selected != null) {
                    addUnresolvedOnce(action.symbol
                            + ": ambiguous model assignments");
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        /** One solver value for one exact configured source hook. */
        private ModelAssignment configuredSourceAssignment(
                String sourcePhaseId, String sourceId,
                String fieldSignature) {
            ModelAssignment selected = null;
            for (ModelAssignment candidate : activation.modelAssignments) {
                if (!candidate.matchesConfiguredSource(sourcePhaseId,
                        sourceId, fieldSignature)
                        || appliedModelAssignments.contains(candidate.key)) {
                    continue;
                }
                if (selected != null) {
                    addUnresolvedOnce(sourcePhaseId
                            + ": ambiguous configured source models");
                    return null;
                }
                selected = candidate;
            }
            return selected;
        }

        private boolean hasAppliedExactNullReferenceAssignment(
                SymbolizeAction action) {
            if (action == null || !action.declaresReferenceInput()) {
                return false;
            }
            int matches = 0;
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.matches(action, null)
                        && assignment.inputSymbol.equals(action.symbol)
                        && assignment.modelIsNull
                        && ("NULL".equalsIgnoreCase(assignment.valueType)
                        || "null".equalsIgnoreCase(assignment.value))
                        && appliedModelAssignments.contains(assignment.key)) {
                    matches++;
                }
            }
            return matches == 1;
        }

        private List<ModelAssignment> fieldAssignments(
                SymbolizeAction action) {
            List<ModelAssignment> result = new ArrayList<>();
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.targetsFieldAccess(action)
                        && !assignment.dynamicAssociativeTarget()
                        && !appliedModelAssignments.contains(assignment.key)) {
                    result.add(assignment);
                }
            }
            return result;
        }

        private void recordModelAssignment(ModelAssignment assignment) {
            appliedModelAssignments.add(assignment.key);
        }

        /** Solver instructions this occurrence reached terminal without using. */    }

    /** Active identity of one dynamic fixed-count loop invocation. */
    private static final class DynamicLoopCardinality {
        private final int occurrence;
        private final int cardinality;

        private DynamicLoopCardinality(int occurrence, int cardinality) {
            this.occurrence = occurrence;
            this.cardinality = cardinality;
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

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            for (Map.Entry<String, Integer> entry : traversals.entrySet()) {
                String scoped = safe(entry.getKey());
                int separator = scoped.indexOf(SCOPE_SEPARATOR);
                String loopId = separator < 0 ? scoped
                        : scoped.substring(0, separator);
                int previous = integer(encoded, loopId, 0);
                if (entry.getValue() > previous) {
                    encoded.addProperty(loopId, entry.getValue());
                }
            }
            return encoded;
        }

        JsonObject bodiesToJson() {
            JsonObject encoded = new JsonObject();
            for (Map.Entry<String, Integer> entry : bodies.entrySet()) {
                encoded.addProperty(entry.getKey(), entry.getValue());
            }
            return encoded;
        }
    }

    /**
     * Non-workload control signal aborting a replay that has spent its loop
     * resource cap.
     */
    public static final class ReplayLoopResourceCut extends Error {
        private static final long serialVersionUID = 1L;
        static final String REASON = "REPLAY_LOOP_RESOURCE_CAP";
        private final String loopId;
        private final int maxBodies;
        private final long attemptedBody;

        ReplayLoopResourceCut(String loopId, int maxBodies,
                              long attemptedBody) {
            super(REASON + " at " + safe(loopId) + ": body "
                    + attemptedBody + " exceeds " + maxBodies);
            this.loopId = safe(loopId);
            this.maxBodies = maxBodies;
            this.attemptedBody = attemptedBody;
        }

        String detail() {
            return REASON + ':' + loopId + ':' + attemptedBody + '/'
                    + maxBodies;
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("kind", REASON);
            encoded.addProperty("loopId", loopId);
            encoded.addProperty("maxLoopBodies", maxBodies);
            encoded.addProperty("attemptedBody", attemptedBody);
            encoded.addProperty("reason", REASON);
            return encoded;
        }

        private static boolean valid(JsonObject encoded) {
            if (encoded == null
                    || !REASON.equals(string(encoded, "kind"))
                    || !REASON.equals(string(encoded, "reason"))
                    || string(encoded, "loopId").isEmpty()) {
                return false;
            }
            int maxBodies = integer(encoded, "maxLoopBodies", -1);
            long attempted = longInteger(encoded, "attemptedBody", -1L);
            return maxBodies > 0 && attempted > maxBodies;
        }
    }

    /** Non-workload control signal used solely to abort a bounded path. */
    public static final class LoopBoundCut extends Error {
        private static final long serialVersionUID = 1L;
        private final String backedgeId;
        private final int maxTraversals;
        private final String reason;

        LoopBoundCut(String backedgeId, int maxTraversals, String reason) {
            super("concolic path cut at " + safe(backedgeId)
                    + " after " + maxTraversals
                    + " loop body iterations");
            this.backedgeId = safe(backedgeId);
            this.maxTraversals = maxTraversals;
            this.reason = safe(reason);
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("kind", "LOOP_BOUND");
            encoded.addProperty("backedgeId", backedgeId);
            encoded.addProperty("maxBackedgeTraversals", maxTraversals);
            encoded.addProperty("reason", reason);
            return encoded;
        }
    }

    static final class ReplayFieldWrites {
        private final IdentityHashMap<Object, Set<String>> fields =
                new IdentityHashMap<>();

        void add(Object owner, String fieldSignature) {
            if (owner == null || FieldPathSpec.declaredField(
                    safe(fieldSignature)) == null) {
                return;
            }
            fields.computeIfAbsent(owner,
                    ignored -> new LinkedHashSet<>()).add(fieldSignature);
        }

        boolean contains(Object owner, String fieldSignature) {
            Set<String> ownerFields = fields.get(owner);
            return ownerFields != null
                    && ownerFields.contains(safe(fieldSignature));
        }
    }


    private static final class SymbolizeAction {
        private final String symbol;
        private final String cell;
        private final String location;
        private final int index;
        private final int replayOccurrence;
        private final List<List<String>> fieldPaths;
        private final String bindingMode;
        private final String method;
        private final String local;
        private final String accessField;
        private final String accessOwnerClass;
        private final String accessFieldSignature;
        private final Set<String> accessSites = new LinkedHashSet<>();
        private final String accessorCallerMethod;
        private final int accessorCallUnitIndex;
        private final String accessorDeclaredCallee;
        private final String accessorImplementationMethod;
        private final String intraRegionSourceOutputPort;
        private final String intraRegionReadFromAuthority;
        private final String symbolicDemand;
        private final String rootKind;
        private final List<String> fieldPath;
        private final String javaType;
        private final String observedPrimitiveValue;
        private final String symbolicName;
        /** Whether the frozen task selected this action as a solver root. */
        private final boolean symbolic;
        private final Set<Integer> definitionUnitIndices =
                new LinkedHashSet<>();
        private final Map<String, String> leafFieldSignaturesByPath =
                new LinkedHashMap<>();

        private SymbolizeAction(JsonObject json) {
            this.symbol = string(json, "symbol");
            this.cell = string(json, "cell");
            this.location = string(json, "location");
            this.index = integer(json, "index", -1);
            this.replayOccurrence = integer(json,
                    "replayOccurrence", -1);
            this.bindingMode = string(json, "bindingMode");
            this.javaType = string(json, "javaType");
            JsonObject definition = json;
            this.method = string(definition, "method");
            this.local = string(definition, "local");
            int unitIndex = integer(definition, "unitIndex", -1);
            if (unitIndex >= 0) definitionUnitIndices.add(unitIndex);
            for (JsonElement element : array(json, "definitionSites")) {
                if (element.isJsonObject()) {
                    int definitionIndex = integer(element.getAsJsonObject(),
                            "unitIndex", -1);
                    if (definitionIndex >= 0) {
                        definitionUnitIndices.add(definitionIndex);
                    }
                }
            }
            this.fieldPath = new ArrayList<>(
                    FieldPathSpec.stringArray(json, "fieldPath"));
            this.accessField = this.fieldPath.isEmpty() ? ""
                    : this.fieldPath.get(0);
            this.accessFieldSignature = string(json,
                    "accessFieldSignature");
            DeclaredField accessDeclaration = FieldPathSpec.declaredField(
                    this.accessFieldSignature);
            this.accessOwnerClass = accessDeclaration == null ? ""
                    : accessDeclaration.owner();
            this.accessSites.addAll(
                    FieldPathSpec.stringArray(json, "accessSites"));
            this.accessorCallerMethod = string(json,
                    "accessorCallerMethod");
            this.accessorCallUnitIndex = integer(json,
                    "accessorCallUnitIndex", -1);
            this.accessorDeclaredCallee = string(json,
                    "accessorDeclaredCallee");
            this.accessorImplementationMethod = string(json,
                    "accessorImplementationMethod");
            this.intraRegionSourceOutputPort = string(json,
                    "intraRegionSourceOutputPort");
            this.intraRegionReadFromAuthority = string(json,
                    "intraRegionReadFromAuthority");
            this.symbolicDemand = string(json, "symbolicDemand");
            this.rootKind = string(json, "rootKind");
            String explicitLeafSignature = firstNonBlank(
                    string(json, "leafFieldSignature"),
                    this.accessFieldSignature);
            this.fieldPaths = new ArrayList<>(
                    FieldPathSpec.paths(json, "fieldPaths"));
            if (this.fieldPaths.isEmpty() && !this.fieldPath.isEmpty()) {
                this.fieldPaths.add(new ArrayList<>(this.fieldPath));
            }
            for (JsonElement declarationElement : array(json,
                    "fieldPathLeafDeclarations")) {
                if (!declarationElement.isJsonObject()) continue;
                JsonObject declaration = declarationElement
                        .getAsJsonObject();
                List<String> path = new ArrayList<>();
                for (JsonElement segment : array(declaration,
                        "fieldPath")) {
                    if (segment.isJsonPrimitive()) {
                        path.add(segment.getAsString());
                    }
                }
                String signature = string(declaration,
                        "fieldSignature");
                if (!path.isEmpty() && FieldPathSpec.declaredField(
                        signature) != null) {
                    leafFieldSignaturesByPath.put(joinFieldPath(path),
                            signature);
                }
            }
            // A port materialized through several hops carries one declared
            // field per hop.
            List<String> pathDeclarations = FieldPathSpec.stringArray(json,
                    "fieldPathDeclarations");
            if (pathDeclarations.size() == this.fieldPath.size()) {
                for (int hop = 0; hop < pathDeclarations.size(); hop++) {
                    String signature = pathDeclarations.get(hop);
                    DeclaredField declared = FieldPathSpec.declaredField(
                            signature);
                    if (declared == null || !declared.name().equals(
                            this.fieldPath.get(hop))) {
                        continue;
                    }
                    leafFieldSignaturesByPath.putIfAbsent(joinFieldPath(
                            this.fieldPath.subList(0, hop + 1)), signature);
                }
            }
            if (!this.fieldPath.isEmpty()
                    && FieldPathSpec.declaredField(
                    explicitLeafSignature) != null) {
                leafFieldSignaturesByPath.put(joinFieldPath(
                        this.fieldPath), explicitLeafSignature);
            }
            this.observedPrimitiveValue = string(json, "primitiveValue");
            this.symbolicName = string(json, "symbolicName");
            this.symbolic = InputActionCatalog.Mode.SYMBOLIC.name().equals(
                    string(json, "mode"));
        }

        private boolean intraRegionComposedInput() {
            return !intraRegionSourceOutputPort.isEmpty()
                    && "EXACT_RUNTIME_RECEIVER_VALUE_IDENTITY_V1".equals(
                    intraRegionReadFromAuthority);
        }

        private boolean declaresArrayInput(List<String> actualPath) {
            String pathSignature = leafFieldSignaturesByPath.get(
                    joinFieldPath(actualPath));
            DeclaredField declared = FieldPathSpec.declaredField(
                    pathSignature);
            if (declared != null
                    && javaTypeDescriptor(declared.type()).startsWith("[")) {
                return true;
            }
            for (String signature : new String[]{accessFieldSignature,
                    cell}) {
                declared = FieldPathSpec.declaredField(signature);
                if (declared != null
                        && javaTypeDescriptor(declared.type()).startsWith("[")
                        && (actualPath == null || actualPath.isEmpty()
                        || declared.name().equals(actualPath.get(
                        actualPath.size() - 1)))) {
                    return true;
                }
            }
            return javaTypeDescriptor(javaType).startsWith("[");
        }

        private boolean declaresReferenceInput() {
            String descriptor = javaTypeDescriptor(javaType);
            return descriptor.startsWith("L") || descriptor.startsWith("[");
        }

        private boolean matchesLocal(String actualMethod,
                                     int actualUnitIndex,
                                     String actualLocal) {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && (definitionUnitIndices.isEmpty()
                    || definitionUnitIndices.contains(actualUnitIndex))
                    && local.equals(safe(actualLocal));
        }

        private boolean matchesMethodArgument(String actualMethod,
                                              int actualIndex) {
            return "METHOD_ARGUMENT".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && index == actualIndex;
        }

        private boolean acceptsOccurrence(int actualOccurrence) {
            return replayOccurrence < 1
                    || replayOccurrence == actualOccurrence;
        }

        private boolean acceptsDirectFieldOccurrence(int actualOccurrence) {
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorImplementationMethod.isEmpty();
            return accessorConstrained || acceptsOccurrence(actualOccurrence);
        }

        private boolean repeatedPrimitiveAccessor() {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && "CALL_RETURN".equals(location)
                    && JavaPrimitiveBoxing.unboxReturn(cell);
        }

        private boolean matchesStaticField(String actualMethod,
                                           int actualUnitIndex,
                                           String signature,
                                           String actualField) {
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "HEAP_OBJECT_FIELD".equals(location))) {
                return false;
            }
            String exactSignature = safe(signature);
            DeclaredField declaration = FieldPathSpec.declaredField(
                    exactSignature);
            if (declaration == null
                    || !declaration.name().equals(safe(actualField))
                    || !accessField.equals(safe(actualField))) {
                return false;
            }
            if (!accessOwnerClass.isEmpty()
                    && !accessOwnerClass.equals(declaration.owner())) {
                return false;
            }
            if (!accessFieldSignature.isEmpty()
                    && !accessFieldSignature.equals(exactSignature)) {
                return false;
            }
            if (accessSites.isEmpty()) {
                return false;
            }
            return accessSites.contains(siteId(actualMethod,
                    actualUnitIndex))
                    && (cell.contains(exactSignature)
                    || accessFieldSignature.equals(exactSignature));
        }

        /**
         * Reconstructs the activation's logical path for an exact getstatic
         * materialization.
         */
        private List<String> exactStaticFieldPath(
                String signature, String actualField) {
            String exactSignature = safe(signature);
            DeclaredField declaration = FieldPathSpec.declaredField(
                    exactSignature);
            if (declaration == null
                    || !declaration.name().equals(safe(actualField))
                    || fieldPath.size() != 1
                    || !fieldPath.get(0).equals(actualField)
                    || !accessField.equals(actualField)
                    || !accessFieldSignature.isEmpty()
                    && !accessFieldSignature.equals(exactSignature)
                    || !accessOwnerClass.isEmpty()
                    && !accessOwnerClass.equals(declaration.owner())
                    || !javaType.isEmpty()
                    && !javaTypeDescriptor(javaType).equals(
                    javaTypeDescriptor(declaration.type()))) {
                return null;
            }
            return Collections.singletonList(actualField);
        }

        private boolean matchesField(String actualMethod,
                                     int actualUnitIndex, Object owner,
                                     String signature, String actualField,
                                     Boolean accessorContextOverride) {
            if (!("FIELD_ACCESS".equals(bindingMode)
                    || "HEAP_OBJECT_FIELD".equals(location))) {
                return false;
            }
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorImplementationMethod.isEmpty();
            String accessorSiteId = accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex < 0 ? ""
                    : accessorCallerMethod + "#u" + accessorCallUnitIndex;
            boolean accessSiteConstrained = !accessSites.isEmpty();
            // Accessor actions name their caller's invoke site in accessSites,
            // while this hook runs at the implementation's field read.
            if (accessSiteConstrained) {
                String constrainedSite = accessorConstrained
                        ? accessorSiteId
                        : siteId(actualMethod, actualUnitIndex);
                if (constrainedSite.isEmpty()
                        || !accessSites.contains(constrainedSite)) {
                    return false;
                }
            }
            Boolean lightweightContext = accessorContextOverride != null
                    ? null : lightweightAccessorContextMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee, owner);
            boolean accessorContextMatches = accessorContextOverride != null
                    ? accessorContextOverride
                    : lightweightContext != null
                    ? lightweightContext
                    : CausynthTraceRecorder.currentCallParentSiteMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee);
            int actualAccessorOccurrence =
                    lightweightAccessorContextOccurrence();
            if (accessorConstrained
                    && (!accessorImplementationMethod.equals(
                    safe(actualMethod))
                    || !accessorContextMatches)) {
                return false;
            }
            if (accessorConstrained
                    && !acceptsOccurrence(
                    actualAccessorOccurrence)) {
                return false;
            }
            if (!accessField.equals(safe(actualField))) {
                return false;
            }
            if (!accessOwnerClass.isEmpty()
                    && !instanceOfName(owner.getClass(), accessOwnerClass)) {
                return false;
            }
            if (accessSiteConstrained
                    && (accessOwnerClass.isEmpty()
                    || accessFieldSignature.isEmpty()
                    || !accessFieldSignature.equals(safe(signature)))) {
                return false;
            }
            // A path rooted at a method return/local may not carry a
            // statically known access owner.
            return !accessOwnerClass.isEmpty()
                    || !safe(signature).isEmpty()
                    && cell.contains(safe(signature));
        }

        private Object leafOwner(Object accessOwner) {
            return resolveFieldPathLeafOwner(accessOwner, fieldPath);
        }

        /**
         * Returns the exact declaration of the scalar/array leaf that will
         * actually be symbolized.
         */
        private String exactLeafFieldSignature() {
            return exactLeafFieldSignature(fieldPath);
        }

        private String exactLeafFieldSignature(List<String> actualPath) {
            String actualLeaf = actualPath == null || actualPath.isEmpty()
                    ? "" : actualPath.get(actualPath.size() - 1);
            String explicit = leafFieldSignaturesByPath.get(
                    joinFieldPath(actualPath));
            DeclaredField declaration = FieldPathSpec.declaredField(
                    explicit);
            if (declaration != null
                    && declaration.name().equals(actualLeaf)) {
                return explicit;
            }
            if (actualPath == null || actualPath.size() != 1) {
                return "";
            }
            String selected = "";
            for (String candidate : new String[]{accessFieldSignature,
                    cell}) {
                declaration = FieldPathSpec.declaredField(candidate);
                if (declaration == null
                        || !declaration.name().equals(actualLeaf)) {
                    continue;
                }
                if (!selected.isEmpty() && !selected.equals(candidate)) {
                    return "";
                }
                selected = candidate;
            }
            return selected;
        }
    }

    /** One scalar or reference assignment returned by a path-flip solve. */
    static final class ModelAssignment {
        private final String key;
        private final String engineSymbol;
        private final String inputSymbol;
        private final String valueType;
        private final String value;
        private final String referenceSourceInputSymbol;
        private final String configuredSourcePhaseId;
        private final String configuredSourceId;
        private final String configuredSourceFieldSignature;
        private final boolean modelIsNull;
        private final boolean containerTargetPresent;
        private final String containerShape;
        private final String containerSelectorKind;
        private final String containerProjection;
        private final int containerIndex;
        private final int containerAccessOrdinal;
        private final int containerSourceIndex;
        private final String containerKeyJavaType;
        private final String containerKeyValue;
        private final String containerSourceShape;
        private final String containerSourceKeyJavaType;
        private final String containerSourceKeyValue;
        private final List<String> path = new ArrayList<>();

        ModelAssignment(JsonObject json) {
            this.engineSymbol = firstNonBlank(string(json, "engineSymbol"));
            this.inputSymbol = string(json, "inputSymbol");
            this.valueType = string(json, "valueType");
            this.value = string(json, "value");
            this.referenceSourceInputSymbol = string(json,
                    "referenceSourceInputSymbol");
            this.configuredSourcePhaseId = string(json,
                    "configuredSourcePhaseId");
            this.configuredSourceId = string(json,
                    "configuredSourceId");
            this.configuredSourceFieldSignature = string(json,
                    "configuredSourceFieldSignature");
            this.modelIsNull = bool(json, "modelIsNull", false);
            JsonElement encodedContainerTarget = json.get("containerTarget");
            this.containerTargetPresent = encodedContainerTarget != null;
            JsonObject containerTarget = object(json, "containerTarget");
            this.containerShape = string(containerTarget, "shape");
            this.containerSelectorKind = string(containerTarget,
                    "selectorKind");
            this.containerProjection = string(containerTarget,
                    "projection");
            this.containerIndex = integer(containerTarget, "index", -1);
            this.containerAccessOrdinal = integer(containerTarget,
                    "accessOrdinal", -1);
            this.containerSourceIndex = integer(containerTarget,
                    "sourceIndex", -1);
            this.containerKeyJavaType = string(containerTarget,
                    "keyJavaType");
            this.containerKeyValue = string(containerTarget, "keyValue");
            this.containerSourceShape = string(containerTarget,
                    "sourceShape");
            this.containerSourceKeyJavaType = string(containerTarget,
                    "sourceKeyJavaType");
            this.containerSourceKeyValue = string(containerTarget,
                    "sourceKeyValue");
            for (JsonElement element : array(json,
                    "materializationPath")) {
                if (element.isJsonPrimitive()) {
                    path.add(element.getAsString());
                }
            }
            this.key = firstNonBlank(string(json, "modelAssignmentKey"),
                    engineSymbol);
        }

        private boolean configuredSourceAssignment() {
            return !configuredSourcePhaseId.isEmpty()
                    || !configuredSourceId.isEmpty()
                    || !configuredSourceFieldSignature.isEmpty();
        }

        private boolean matchesConfiguredSource(String sourcePhaseId,
                                                 String sourceId,
                                                 String fieldSignature) {
            return configuredSourcePhaseId.equals(safe(sourcePhaseId))
                    && configuredSourceId.equals(safe(sourceId))
                    && configuredSourceFieldSignature.equals(
                            safe(fieldSignature))
                    && inputSymbol.equals("SOURCE_PHASE:"
                    + safe(sourcePhaseId));
        }

        private boolean referenceAlias() {
            return ("REFERENCE_ALIAS".equals(valueType)
                    || "CONTAINER_REFERENCE_ALIAS".equals(valueType))
                    && !referenceSourceInputSymbol.isEmpty();
        }

        private boolean hasContainerTarget() {
            return containerTargetPresent;
        }

        private boolean containerReferenceAlias() {
            return "CONTAINER_REFERENCE_ALIAS".equals(valueType);
        }

        private boolean iterationTarget() {
            return "ASSOCIATIVE".equals(containerShape)
                    && "ITERATION_INDEX".equals(containerSelectorKind);
        }

        private boolean dynamicAssociativeTarget() {
            return "ASSOCIATIVE".equals(containerShape)
                    && "ACCESS_ORDINAL".equals(containerSelectorKind)
                    && containerAccessOrdinal >= 1;
        }

        private boolean validContainerTarget() {
            if ("INDEXED".equals(containerShape)) {
                return containerIndex >= 0
                        && (!containerReferenceAlias()
                        || validContainerReferenceSource());
            }
            if (iterationTarget()) {
                return containerIndex >= 0
                        && ("KEY".equals(containerProjection)
                        || "VALUE".equals(containerProjection))
                        && (!containerReferenceAlias()
                        || validContainerReferenceSource());
            }
            if (dynamicAssociativeTarget()) {
                return !containerReferenceAlias()
                        || validContainerReferenceSource();
            }
            if (!"ASSOCIATIVE".equals(containerShape)
                    || containerKeyJavaType.isEmpty()
                    || containerKeyValue.isEmpty()) {
                return false;
            }
            return !containerReferenceAlias()
                    || validContainerReferenceSource();
        }

        private boolean validContainerReferenceSource() {
            if (referenceSourceInputSymbol.isEmpty()) return false;
            if (containerSourceShape.isEmpty()) return true;
            if ("INDEXED".equals(containerSourceShape)) {
                return containerSourceIndex >= 0;
            }
            return "ASSOCIATIVE".equals(containerSourceShape)
                    && !containerSourceKeyJavaType.isEmpty()
                    && !containerSourceKeyValue.isEmpty();
        }

        private boolean matches(SymbolizeAction action,
                                List<String> actualPath) {
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) {
                return actualPath == null || actualPath.isEmpty()
                        || action.fieldPath.equals(actualPath);
            }
            return actualPath != null && path.equals(actualPath);
        }

        private boolean targetsFieldAccess(SymbolizeAction action) {
            if (!inputSymbol.equals(action.symbol)) return false;
            if (path.isEmpty()) return true;
            if (action.fieldPath.isEmpty()
                    || path.size() < action.fieldPath.size()) return false;
            for (int index = 0; index < action.fieldPath.size(); index++) {
                if (!path.get(index).equals(action.fieldPath.get(index))) {
                    return false;
                }
            }
            return true;
        }

        private Object referenceValue(Object concrete) {
            if ("STRING".equalsIgnoreCase(valueType)) {
                return unquoteSmtString(value);
            }
            if ("NULL".equalsIgnoreCase(valueType)
                    || "null".equalsIgnoreCase(value)) return null;
            if ("UNCHANGED".equalsIgnoreCase(valueType)) return concrete;
            return UnsupportedReplayValue.INSTANCE;
        }

    }


    /**
     * The replay address of one planned occurrence.
     *
     * <p>Two halves, decided at two different moments because that is when
     * each becomes knowable.</p>
     */
    private static final class RootContextSelector {
        private final boolean receiverScoped;
        private final String receiverRuntimeClass;
        private final String threadName;
        private final String sourceKey;
        private final String requestApi;
        private final boolean registeredSourceAnchor;
        /**
         * The planned source was the thread's inherited context, not the
         * receiver's own registration, so replay must re-check it the same
         * way.
         */
        private final boolean inheritedContextAnchor;

        private RootContextSelector(boolean receiverScoped,
                                    String receiverRuntimeClass,
                                    String threadName, String sourceKey,
                                    String requestApi,
                                    boolean registeredSourceAnchor,
                                    boolean inheritedContextAnchor) {
            this.receiverScoped = receiverScoped;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = stableReplayThreadContext(threadName);
            this.sourceKey = safe(sourceKey);
            this.requestApi = safe(requestApi);
            this.registeredSourceAnchor = registeredSourceAnchor;
            this.inheritedContextAnchor = inheritedContextAnchor;
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = string(selector, "kind");
            boolean global = "GLOBAL_INVOCATION".equals(kind);
            String receiverClass = string(selector, "receiverClass");
            String thread = selector.has("thread")
                    ? string(selector, "thread") : "";
            JsonObject anchor = object(selector, "causalAnchor");
            String sourceKey = string(anchor, "sourceKey");
            String requestApi = string(anchor, "requestApi");
            String anchorKind = string(anchor, "kind");
            boolean registeredSource = RuntimeRegionPlanner
                    .ANCHOR_REGISTERED_SOURCE.equals(anchorKind);
            boolean unregisteredSource = RuntimeRegionPlanner
                    .ANCHOR_UNREGISTERED_SOURCE.equals(anchorKind);
            boolean inheritedContext = RuntimeRegionPlanner
                    .ANCHOR_INHERITED_CONTEXT.equals(anchorKind);
            boolean sentinelSource = RuntimeRegionPlanner.UNREGISTERED_SOURCE
                    .key().equals(sourceKey);
            if (!global && (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || !"RECEIVER_CONTEXT".equals(kind)
                    || selector.has("thread") && (thread.isEmpty()
                    || !thread.equals(thread.trim())))
                    || sourceKey.isEmpty()
                    || !sourceKey.equals(sourceKey.trim())) {
                throw new IllegalArgumentException(
                        "rootSelector requires an exact receiver context and "
                                + "a causal anchor naming its source");
            }
            if (!registeredSource && !unregisteredSource && !inheritedContext
                    || unregisteredSource != sentinelSource) {
                throw new IllegalArgumentException(
                        "rootSelector causalAnchor.kind must be exactly "
                                + RuntimeRegionPlanner
                                .ANCHOR_REGISTERED_SOURCE + " or "
                                + RuntimeRegionPlanner
                                .ANCHOR_INHERITED_CONTEXT + " for a named "
                                + "source or " + RuntimeRegionPlanner
                                .ANCHOR_UNREGISTERED_SOURCE + " for "
                                + RuntimeRegionPlanner.UNREGISTERED_SOURCE
                                .key());
            }
            return new RootContextSelector(!global, receiverClass, thread,
                    sourceKey, requestApi, registeredSource,
                    inheritedContext);
        }

        /**
         * Whether two selectors name the same replay address for one root
         * invocation that entered {@code actualRequestApi}.
         *
         * <p>The request API is a gate on the invocation, not a component of
         * the address: {@link Configuration#select} admits a selector that
         * names no API under any API and one that names an API only under
         * that API.  Comparing the two selectors' APIs to each other instead
         * made two occurrences of one region whose plans state the demand at
         * different scopes -- one addressed by the request it serves, one by
         * a shared location it must produce -- permanent strangers, so
         * neither could ever ride the other's activation.  That is exactly
         * how a once-only heap write goes uncaptured: the write runs in the
         * first activation, whichever occurrence claimed that activation
         * declares no capture binding for it, and the occurrence that does
         * declare one is admitted later, after the guard that made the write
         * once-only has closed.  Applying {@code select}'s own gate keeps the
         * claim exact -- the sibling is admitted here only when {@code
         * select} itself would have admitted it on this very invocation.</p>
         */
        private boolean sameAddress(RootContextSelector other,
                                    String actualRequestApi) {
            return other != null
                    && receiverScoped == other.receiverScoped
                    && receiverRuntimeClass.equals(other.receiverRuntimeClass)
                    && threadName.equals(other.threadName)
                    && sourceKey.equals(other.sourceKey)
                    && admitsRequestApi(actualRequestApi)
                    && registeredSourceAnchor == other.registeredSourceAnchor
                    && inheritedContextAnchor == other.inheritedContextAnchor;
        }

        /**
         * Whether a root invocation that entered {@code actualRequestApi}
         * satisfies this selector's local-scope gate.
         */
        private boolean admitsRequestApi(String actualRequestApi) {
            return requestApi.isEmpty()
                    || requestApi.equals(safe(actualRequestApi));
        }

        /** Whether this root invocation is a candidate for the occurrence. */
        private boolean matches(Object receiver, String actualThreadName) {
            if (!receiverScoped) return true;
            return receiver != null
                    && receiverRuntimeClass.equals(receiver.getClass().getName())
                    && (threadName.isEmpty()
                    || threadName.equals(stableReplayThreadContext(
                    actualThreadName)));
        }

        /**
         * Why the candidate that just ran is not the addressed occurrence, or
         * {@code ""} when it is.
         */
        private String unconfirmed(Set<String> attributedSourceKeys) {
            if (attributedSourceKeys.isEmpty()) {
                if (!OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(
                        sourceKey)) {
                    return "occurrence is attributed to no registered trace "
                            + "source, but its anchor names " + sourceKey;
                }
                return "";
            }
            boolean sameSource = false;
            for (String attributed : attributedSourceKeys) {
                if (RuntimeTraceContext.sameSourceIdentity(
                        sourceKey, attributed)) {
                    sameSource = true;
                    break;
                }
            }
            if (!sameSource) {
                return "occurrence ran on " + attributedSourceKeys
                        + ", but its anchor names " + sourceKey;
            }
            return "";
        }

        /** This address on one line, for a named gap. */
        private String describe() {
            return requestApi.isEmpty()
                    ? sourceKey : sourceKey + "/requestApi=" + requestApi;
        }

        /**
         * Whether the anchored source was never registered in this run, which
         * makes the address unsatisfiable here rather than merely unmatched.
         */
        private boolean anchorSourceNeverExisted() {
            return !OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(sourceKey)
                    && !RuntimeTraceContext.sourceIdentityRegistered(sourceKey);
        }

        private static String stableReplayThreadContext(String value) {
            String thread = safe(value);
            Matcher executor = DEFAULT_EXECUTOR_THREAD_NAME.matcher(thread);
            if (executor.matches()) {
                return "pool-*-thread-" + executor.group(1);
            }
            Matcher objectIdentity =
                    DEFAULT_OBJECT_IDENTITY_THREAD_NAME.matcher(thread);
            return objectIdentity.matches()
                    ? objectIdentity.group(1) + "@*" : thread;
        }

    }

    private static final class RootArgumentSelector {
        private final boolean present;
        private final List<RootArgumentTypePredicate> predicates;

        private RootArgumentSelector(boolean present,
                                     List<RootArgumentTypePredicate> predicates) {
            this.present = present;
            this.predicates = predicates;
        }

        private static RootArgumentSelector from(JsonObject rootSelector) {
            if (!rootSelector.has("arguments")) {
                return new RootArgumentSelector(false,
                        Collections.emptyList());
            }
            JsonElement raw = rootSelector.get("arguments");
            if (raw == null || !raw.isJsonObject()) {
                return invalid("rootSelector.arguments must be an object");
            }
            JsonObject json = raw.getAsJsonObject();
            JsonElement rawPredicates = json.get("predicates");
            if (rawPredicates == null || !rawPredicates.isJsonArray()
                    || rawPredicates.getAsJsonArray().size() == 0) {
                return invalid("predicates must be a non-empty array");
            }
            List<RootArgumentTypePredicate> predicates = new ArrayList<>();
            Set<Integer> indices = new LinkedHashSet<>();
            for (JsonElement rawPredicate
                    : rawPredicates.getAsJsonArray()) {
                if (rawPredicate == null || !rawPredicate.isJsonObject()) {
                    return invalid("each predicate must be an object");
                }
                JsonObject predicate = rawPredicate.getAsJsonObject();
                if (!ROOT_ARGUMENT_PREDICATE_KIND.equals(
                        string(predicate, "kind"))) {
                    return invalid("predicate kind must be exact runtime type");
                }
                int index = integer(predicate, "argumentIndex", -1);
                String runtimeType = string(predicate, "runtimeType");
                if (index < 0 || runtimeType.isEmpty()
                        || !runtimeType.equals(runtimeType.trim())
                        || !indices.add(index)) {
                    return invalid("predicate index/type is malformed or duplicate");
                }
                predicates.add(new RootArgumentTypePredicate(index,
                        runtimeType));
            }
            predicates.sort((left, right) -> Integer.compare(
                    left.argumentIndex, right.argumentIndex));
            return new RootArgumentSelector(true,
                    Collections.unmodifiableList(predicates));
        }

        private static RootArgumentSelector invalid(String error) {
            throw new IllegalArgumentException(error);
        }

        /** No argument predicate: every activation of the root is admitted. */
        private boolean matches(Object[] rootArguments) {
            if (!present || rootArguments == null) return false;
            for (RootArgumentTypePredicate predicate : predicates) {
                if (predicate.argumentIndex >= rootArguments.length) {
                    return false;
                }
                Object value = rootArguments[predicate.argumentIndex];
                if (value == null || !predicate.runtimeType.equals(
                        value.getClass().getName())) {
                    return false;
                }
            }
            return true;
        }

    }

    private static final class RootArgumentTypePredicate {
        private final int argumentIndex;
        private final String runtimeType;

        private RootArgumentTypePredicate(int argumentIndex,
                                          String runtimeType) {
            this.argumentIndex = argumentIndex;
            this.runtimeType = runtimeType;
        }
    }

    /** Activation-local matcher for a solver replay. */
    static final class ReplayProgress {
        private final List<ReplayEvent> expected = new ArrayList<>();
        private int next;
        private String failure = "prefix not yet observed";

        ReplayProgress(BranchReplayContract contract) {
            if (contract == null) return;
            for (BranchWitness witness : contract.orderedPrefix()) {
                // Several VM predicates may belong to one source branch.
                if (!witness.isPcPredicateDecision()) {
                    add(witness.siteId(), witness.occurrence(),
                            witness.sourceTakenOutcome(), false);
                }
            }
            BranchWitness source = contract.source();
            if (source.isPcPredicateDecision()) {
                throw new IllegalArgumentException(
                        "replay source must be a source-level branch event");
            }
            add(source.siteId(), source.occurrence(),
                    contract.requiredTakenOutcome(), true);
        }

        private void add(String siteId, int occurrence, boolean outcome,
                         boolean source) {
            ReplayEvent event = new ReplayEvent(siteId, occurrence,
                    outcome, source);
            if (!expected.isEmpty()
                    && expected.get(expected.size() - 1).sameIdentity(event)) {
                ReplayEvent prior = expected.get(expected.size() - 1);
                if (prior.outcome != outcome || prior.source != source) {
                    throw new IllegalArgumentException(
                            "conflicting replay events at " + siteId + '#'
                                    + occurrence);
                }
                return;
            }
            expected.add(event);
        }

        boolean observe(String siteId, int occurrence, boolean outcome) {
            if (expected.isEmpty()) return true;
            if (failed() || complete()) return complete();
            ReplayEvent actual = new ReplayEvent(siteId, occurrence,
                    outcome, false);
            ReplayEvent wanted = expected.get(next);
            if (wanted.sameIdentity(actual)) {
                if (wanted.outcome != outcome) {
                    failure = "wrong outcome at " + siteId + '#'
                            + occurrence;
                    return false;
                }
                next++;
                failure = complete() ? "" : "prefix not yet complete";
                return complete() && wanted.source;
            }
            for (int index = next + 1; index < expected.size(); index++) {
                if (expected.get(index).sameIdentity(actual)) {
                    failure = "reached " + siteId + '#' + occurrence
                            + " before replay prefix event "
                            + wanted.siteId + '#' + wanted.occurrence;
                    return false;
                }
            }
            return false;
        }

        boolean complete() {
            return expected.isEmpty() || next == expected.size();
        }

        boolean failed() {
            return !complete()
                    && !"prefix not yet observed".equals(failure)
                    && !"prefix not yet complete".equals(failure);
        }

        String failure() {
            return failure;
        }
    }

    private static final class ReplayEvent {
        private final String siteId;
        private final int occurrence;
        private final boolean outcome;
        private final boolean source;

        private ReplayEvent(String siteId, int occurrence,
                            boolean outcome, boolean source) {
            this.siteId = safe(siteId);
            this.occurrence = occurrence;
            this.outcome = outcome;
            this.source = source;
        }

        private boolean sameIdentity(ReplayEvent other) {
            return other != null && occurrence == other.occurrence
                    && siteId.equals(other.siteId);
        }
    }

    private static final class RuntimeTask {
        private final String taskId;
        private final String instrumentationSelector;
        private final String regionId;
        /** Exact planner identity of the dynamic root activation. */
        private final String activationId;
        /** The activation this task is. */
        private final String sourceKey;
        private final String occurrenceId;
        private final String rootMethod;
        private final RootContextSelector rootContextSelector;
        private final RootArgumentSelector rootArgumentSelector;
        /** Complete planner-authored action catalog used by exact selector
         * declarations, including observation-only deferred leaf actions. */
        private final List<SymbolizeAction> declaredSymbolize;
        /** Actions that execute directly at ordinary instrumentation hooks. */
        private final List<SymbolizeAction> symbolize;
        private final Map<String, String> branchPolicies;
        private final LoopBoundPolicy loopBound;
        private final List<ModelAssignment> modelAssignments;
        private final List<OutputCaptureSpec> outputCaptures;
        private final boolean capturesOutputRelation;
        private final boolean capturesTargetReach;
        /** Whether this target task has already published its failure goal. */
        private volatile boolean completedTargetReserved;
        /** Whether this ordinary producer already published a complete row. */
        private volatile boolean completedRelationReserved;
        /**
         * Result rows this address has published in this replay.
         *
         * <p>Every admitted activation that reaches a terminal is its own
         * occurrence. This counts them so each row can name which one it is;
         * target admission stops after its failure goal; ordinary producers
         * keep running so later activations can propagate symbolic state.</p>
         */
        private int publishedActivations;
        /**
         * Whether this region is rooted on a bounded loop body.  Its published
         * occurrence set is unrolled at most {@code loopBound
         * .maxBackedgeTraversals()} (K_L) times, exactly as an inner bounded
         * loop is: the iterations past K_L run concretely and capture nothing.
         */
        private final boolean loopBodyRoot;
        /**
         * The occurrence budget of a loop-body region: its ROOT loop's own
         * K_L, not the region's global max.  The root loop is what generates
         * one occurrence per iteration; the region's inner loops (the {@code
         * allKeys} walks) are unrolled WITHIN one occurrence and their larger
         * bounds must not inflate the occurrence count.  Using the region max
         * here published up to the inner-loop bound of occurrences, each
         * re-snapshotting the growing {@code allKeys} map, which under a
         * 600-min token lifetime (no physical expiry) explodes the symbolic
         * session.
         */
        private final int loopOccurrenceBudget;
        /** Whether the one bounded-cut marker for this region was written. */
        private boolean loopBoundCutRecorded;
        /** Turns of the root loop examined for this bounded address. */
        private int admittedTurns;
        /** Kept occurrences that carried the selected causal anchor. */
        private int anchoredOccurrences;
        /** Exact phase/exchange identities committed by published turns. */
        private final Set<String> observedSemanticAnchorIds =
                new LinkedHashSet<>();
        /** Turns run and given back for carrying no selected anchor. */
        private int unanchoredTurnsReleased;
        private final boolean hasExplicitFaultInput;
        private final Set<String> executionScopeMethods;
        private final BranchReplayContract replayContract;
        private final Map<String, Set<Boolean>> seedOutcomes;
        /** The declared target branch event of a target-reach task. */
        private final String targetBranchSite;
        private final int targetBranchOccurrence;
        /** Solver-selected outcome that reaches the annotated failure. */
        private final boolean targetBranchRequiredOutcome;
        /**
         * Declared communication ports this occurrence hands to the VM, by
         * port id.
         */
        private final Map<String, CommunicationHandoffSpec>
                communicationHandoffs = new LinkedHashMap<>();
        /** Exact baseline hook executions, in recorded event order. */
        private final List<ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhases;
        /** Reserved source-hook ordinal across one LOOP_BODY_ROOT address. */
        private final Map<String, Integer> configuredSourcePhaseOrdinals =
                new LinkedHashMap<>();
        /** Strict phase lookup; phase ids never alias source ids. */
        private final Map<String, ConfiguredSourcePhaseContract.Occurrence>
                configuredSourcePhasesById = new LinkedHashMap<>();
        /** Every protocol input this occurrence attaches from the VM. */
        private final Set<String> attachPortIds = new LinkedHashSet<>();
        /**
         * Planner-selected producer occurrence of each response attach port.
         */
        private final Map<String, String> attachProducerOccurrenceByPort =
                new LinkedHashMap<>();
        /** Read-cut gates the solver selected for this replay, if any. */
        private final List<JsonObject> readCutGates = new ArrayList<>();
        /** Shared locations this task selects as carriers at region entry. */
        private final List<SharedCarrierRequest> sharedCarriers =
                new ArrayList<>();
        /** Frozen runtime bindings used to resolve exact Map producers. */
        private final JsonArray edgeBindings;
        /** Declared field -> unique frozen receiver locator for this task. */
        private final Map<String, Long> plannedReceiverObjectIdByField =
                new LinkedHashMap<>();
        /**
         * Activations that ran as candidates for this address and were not the
         * addressed occurrence, and every distinct reason they were not.
         */
        private int unaddressedCandidates;
        private final Set<String> unaddressedReasons = new LinkedHashSet<>();

        private RuntimeTask(ExecutionTask task) {
            if (!task.executable()) {
                throw new IllegalArgumentException(
                        "runtime task must be executable");
            }
            JsonObject rootSelector = task.rootSelector();
            this.taskId = task.taskId();
            this.instrumentationSelector = task.instrumentationSelector();
            this.regionId = task.regionId();
            this.activationId = string(task.json(), "activationId");
            this.sourceKey = task.sourceKey();
            this.occurrenceId = task.occurrenceId();
            this.rootMethod = task.rootMethod();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            if (!this.sourceKey.equals(rootContextSelector.sourceKey)) {
                throw new IllegalArgumentException(
                        "rootSelector causal anchor names "
                                + rootContextSelector.sourceKey
                                + " instead of task source " + this.sourceKey);
            }
            // A region rooted at a loop body binds no arguments at its
            // frame: the method's parameters were bound once, at the entry
            // above the loop.  Its activation therefore carries an empty
            // argument array, and a type predicate over arguments that do not
            // exist there would refuse every iteration without saying so.
            this.rootArgumentSelector =
                    LoopBoundPolicy.LOOP_BODY_ROOT.equals(task.rootAuthority())
                            ? new RootArgumentSelector(false,
                            Collections.<RootArgumentTypePredicate>emptyList())
                            : RootArgumentSelector.from(rootSelector);
            this.declaredSymbolize = new ArrayList<>();
            this.symbolize = new ArrayList<>();
            boolean explicitFaultInput = false;
            this.branchPolicies = new LinkedHashMap<>();
            this.seedOutcomes = new LinkedHashMap<>();
            this.loopBound = task.loopBound();
            this.loopBodyRoot = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                    task.rootAuthority());
            // The root loop's declared K_L (its loopSiteId is the key its
            // bound is under); an undeclared site inherits the default.
            this.loopOccurrenceBudget = this.loopBound
                    .maxBackedgeTraversals(task.rootLoopSiteId());
            this.modelAssignments = new ArrayList<>();
            this.outputCaptures = new ArrayList<>();
            this.capturesOutputRelation =
                    task.goalKind().capturesOutputRelation();
            this.capturesTargetReach =
                    task.goalKind().capturesTargetReach();
            this.executionScopeMethods = new LinkedHashSet<>();
            this.edgeBindings = task.edgeBindings().deepCopy();
            indexPlannedReceiverObjectIds(edgeBindings);
            // The plan row decoded this catalog once; phase ids are already
            // one strict ordered ledger by then, so this is an index, not a
            // second admission.
            this.configuredSourcePhases = task.configuredSourcePhases();
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                configuredSourcePhasesById.put(phase.phaseId(), phase);
            }
            Set<String> selectedOutputCells = new LinkedHashSet<>();
            if (task.outputClosure() != null) {
                this.executionScopeMethods.addAll(
                        task.outputClosure().executionScope().methods());
                for (OutputClosureContract.Member member
                        : task.outputClosure().members()) {
                    selectedOutputCells.add(member.cell());
                }
            }
            JsonElement encodedReplay = task.replayContract();
            if (encodedReplay == null) {
                this.replayContract = null;
            } else if (!encodedReplay.isJsonObject()) {
                throw new IllegalArgumentException(
                        "replayContract must be an object");
            } else {
                this.replayContract = BranchReplayContract.fromJson(
                        encodedReplay.getAsJsonObject());
            }
            JsonObject targetBranch = object(task.json(), "targetBranch");
            this.targetBranchSite = string(targetBranch, "siteId");
            this.targetBranchOccurrence = integer(targetBranch,
                    "occurrence", -1);
            this.targetBranchRequiredOutcome = targetRequiredOutcome(
                    task.branches(), targetBranchSite,
                    targetBranchOccurrence);
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                explicitFaultInput |=
                        "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1".equals(
                                string(encoded, "authority"));
                SymbolizeAction action = new SymbolizeAction(encoded);
                this.declaredSymbolize.add(action);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        string(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
            }
            this.hasExplicitFaultInput = explicitFaultInput;
            boolean seedTask = this.replayContract == null
                    && !relationOnlySeed();
            for (JsonElement element : task.branches()) {
                JsonObject branch = element.getAsJsonObject();
                String siteId = string(branch, "siteId");
                branchPolicies.put(siteId, string(branch, "policy"));
                if (seedTask) {
                    recordSeedOutcomes(siteId, branch.get("occurrences"));
                }
            }
            JsonElement encodedAssignments = task.json().get(
                    "modelAssignments");
            if (encodedAssignments != null
                    && !encodedAssignments.isJsonArray()) {
                throw new IllegalArgumentException(
                        "modelAssignments must be an array in " + taskId);
            }
            for (JsonElement element : task.modelAssignments()) {
                modelAssignments.add(new ModelAssignment(
                        element.getAsJsonObject()));
            }
            Set<String> assignmentKeys = new LinkedHashSet<>();
            for (ModelAssignment assignment : modelAssignments) {
                if (assignment.key.isEmpty()
                        || !assignmentKeys.add(assignment.key)) {
                    throw new IllegalArgumentException(
                            "model assignment keys must be nonempty and "
                                    + "unique in " + taskId);
                }
            }
            for (OutputCaptureSpec request : task.outputCaptures()) {
                outputCaptures.add(request);
            }
            for (CommunicationHandoffSpec site
                    : task.communicationHandoffs()) {
                if (!site.outgoing()) {
                    attachPortIds.add(site.portId());
                }
                // A region that holds both sides of a cut declares the same
                // port twice, once per role, and each role has its own site.
                if (communicationHandoffs.put(handoffKey(site.portId(),
                        site.outgoing()), site) != null) {
                    throw new IllegalArgumentException(
                            "communication port declares two handoff sites "
                            + "in " + taskId + ": " + site.portId());
                }
            }
            // A configured-source model names one mint SITE of the frozen
            // catalog.  There is no selected-source row to agree with any
            // more: the site is the identity.
            for (ModelAssignment assignment : modelAssignments) {
                if (!assignment.configuredSourceAssignment()) continue;
                ConfiguredSourcePhaseContract.Occurrence publish =
                        configuredSourcePhasesById.get(
                                assignment.configuredSourcePhaseId);
                if (publish == null
                        || publish.phase()
                        != ConfiguredSourcePhaseContract.Phase.PUBLISH
                        || !assignment.configuredSourceId.equals(
                        publish.sourceId())
                        || !assignment.configuredSourceFieldSignature.equals(
                        publish.fieldSignature())
                        || !assignment.matchesConfiguredSource(
                        publish.phaseId(), publish.sourceId(),
                        publish.fieldSignature())
                        || assignment.hasContainerTarget()
                        || assignment.referenceAlias()) {
                    throw new IllegalArgumentException(
                            "model assignment names an undeclared or "
                                    + "unsupported configured source in "
                                    + taskId + ": " + assignment.key);
                }
            }
            indexAttachProducerOccurrences(edgeBindings);
            // Gates travel with the task because the arm they enforce was
            // chosen by the solver for this replay and no other.
            for (JsonElement element : array(
                    SelectedReadCut.planOf(task.json()), "gates")) {
                if (element.isJsonObject()) {
                    readCutGates.add(element.getAsJsonObject().deepCopy());
                }
            }
            for (JsonElement element : task.sharedCarriers()) {
                if (element.isJsonObject()) {
                    sharedCarriers.add(new SharedCarrierRequest(
                            element.getAsJsonObject()));
                }
            }
            declareSymbolicFieldCarriers();
        }

        /**
         * Every SYMBOLIC field this region declares is a shared location.
         *
         * <p>Wave 3 concurrency: the manual input is WHICH FIELDS, and a
         * declared field keeps every symbolic write of the session as a
         * version.  Nothing selects a subset of the declared fields.</p>
         *
         * <p>These are added <em>beside</em> the planner's own carrier list,
         * not instead of it.  Measured on HDFS-11741 run-10's frozen plan the
         * two sets are not equal: the planner declares 12 distinct locations
         * and the SYMBOLIC actions name 1 of them ({@code allKeys}), so
         * replacing the list here would silently drop 11 locations the
         * planner still binds.  The planner owns that reconciliation.</p>
         */
        private void declareSymbolicFieldCarriers() {
            Set<String> declared = new LinkedHashSet<>();
            for (SharedCarrierRequest request : sharedCarriers) {
                declared.add(request.declaringClass + "\n"
                        + request.fieldName);
            }
            for (SymbolizeAction action : symbolize) {
                DeclaredField field = FieldPathSpec.declaredField(
                        firstNonBlank(action.exactLeafFieldSignature(),
                                action.accessFieldSignature));
                if (field == null
                        || !declared.add(field.owner() + "\n"
                        + field.name())) {
                    continue;
                }
                JsonObject declaration = new JsonObject();
                // A bounded-container demand on a Map field is a whole-state
                // location, not a reference slot: declaring it as an
                // instance field would version the reference and lose every
                // entry transition the composer reads from.
                boolean mapState = "BOUNDED_CONTAINER_STATE".equals(
                        action.symbolicDemand)
                        && javaTypeDescriptor(field.type()).startsWith("L")
                        && isMapType(field.type());
                declaration.addProperty("kind", mapState
                        ? SharedStateEvidence.LOCATION_KIND_MAP_STATE
                        : "INSTANCE_FIELD");
                declaration.addProperty("sourceKind",
                        "ACTIVATION_FIELD_RECEIVER");
                declaration.addProperty("declaringClass", field.owner());
                declaration.addProperty("fieldName", field.name());
                declaration.addProperty("descriptor",
                        javaTypeDescriptor(field.type()));
                sharedCarriers.add(new SharedCarrierRequest(declaration));
            }
        }

        /** Whether a declared field type is a Map the VM versions whole. */
        private static boolean isMapType(String javaType) {
            try {
                return Map.class.isAssignableFrom(Class.forName(
                        safe(javaType).trim()));
            } catch (Throwable notLoadable) {
                // Judge by name when the type is not on this loader: the
                // declaration is the authority, not the loaded class.
                String value = safe(javaType);
                return value.endsWith("Map") || value.contains("Map<");
            }
        }

        /** The declared handoff site of one communication port role. */
        private CommunicationHandoffSpec communicationHandoff(
                String portId, boolean exporting) {
            return communicationHandoffs.get(handoffKey(portId, exporting));
        }

        /**
         * Resolves each selected response input to its planner-authored
         * producer occurrence.
         */
        private void indexAttachProducerOccurrences(JsonArray bindings) {
            for (String portId : attachPortIds) {
                // An exchange pairing a replay recorded and the scheduler
                // absorbed stands beside the frozen plan's own row for this
                // port rather than replacing it, so one port can name two
                // senders here.  The recorded one decides: its two VM ledger
                // events name this exact send and this exact receive, which
                // is more than the plan ever stated.  Nothing else changes --
                // two plan rows that disagree are the refusal they always
                // were, and two recorded pairings that disagree are refused
                // too, because then no evidence names one sender.
                String producerOccurrence = "";
                String recordedOccurrence = "";
                for (JsonElement element : bindings) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!"RUNTIME_PROTOCOL_FLOW".equals(
                            string(binding, "kind"))
                            || !portId.equals(string(binding, "toInputPort"))) {
                        continue;
                    }
                    String receiver = PathObservation.plannedOccurrenceOf(
                            string(binding, "toOccurrenceId"));
                    if (!receiver.isEmpty()
                            && !occurrenceId.equals(receiver)) {
                        continue;
                    }
                    String candidate = PathObservation.plannedOccurrenceOf(
                            string(binding, "fromOccurrenceId"));
                    if (candidate.isEmpty()) continue;
                    boolean recorded = VmHandoffEvidence.absorbed(binding);
                    String held = recorded
                            ? recordedOccurrence : producerOccurrence;
                    if (!held.isEmpty() && !held.equals(candidate)) {
                        throw new IllegalArgumentException(
                                "communication attach port has two producer "
                                        + "occurrences in " + taskId + ": "
                                        + portId);
                    }
                    if (recorded) {
                        recordedOccurrence = candidate;
                    } else {
                        producerOccurrence = candidate;
                    }
                }
                String selected = recordedOccurrence.isEmpty()
                        ? producerOccurrence : recordedOccurrence;
                if (!selected.isEmpty()) {
                    attachProducerOccurrenceByPort.put(portId, selected);
                }
            }
        }

        private String attachProducerOccurrence(String portId) {
            return safe(attachProducerOccurrenceByPort.get(safe(portId)));
        }

        private void indexPlannedReceiverObjectIds(JsonArray bindings) {
            Map<String, Set<Long>> candidates = new LinkedHashMap<>();
            for (JsonElement element : bindings) {
                if (!element.isJsonObject()) continue;
                JsonObject binding = element.getAsJsonObject();
                if (!"RUNTIME_FIELD_FLOW".equals(string(binding, "kind"))) {
                    continue;
                }
                String from = PathObservation.plannedOccurrenceOf(
                        string(binding, "fromOccurrenceId"));
                String to = PathObservation.plannedOccurrenceOf(
                        string(binding, "toOccurrenceId"));
                if (!occurrenceId.equals(from) && !occurrenceId.equals(to)) {
                    continue;
                }
                String field = string(binding, RecordedReadFrom.EDGE_FIELD);
                long receiver = longInteger(binding, "receiverObjectId", 0L);
                if (field.isEmpty() || receiver <= 0L) continue;
                candidates.computeIfAbsent(field,
                        ignored -> new LinkedHashSet<>()).add(receiver);
            }
            for (Map.Entry<String, Set<Long>> entry : candidates.entrySet()) {
                if (entry.getValue().size() == 1) {
                    plannedReceiverObjectIdByField.put(entry.getKey(),
                            entry.getValue().iterator().next());
                }
            }
        }

        private long plannedReceiverObjectId(String declaringClass,
                                             String fieldName) {
            return plannedReceiverObjectIdByField.getOrDefault(
                    safe(declaringClass) + "#" + safe(fieldName), 0L);
        }

        private static String handoffKey(String portId, boolean exporting) {
            return (exporting ? "EXPORT\n" : "ATTACH\n") + safe(portId);
        }

        /**
         * Records that one candidate ran and was not this address, keeping
         * the last reason for the run's single statement about it.
         */
        private synchronized void noteUnaddressedCandidate(String reason) {
            unaddressedCandidates++;
            unaddressedReasons.add(safe(reason));
            registerRunTotalsHook();
        }

        /** The run's one statement about an address nothing answered. */
        private synchronized String unansweredAddress() {
            boolean neverExisted = rootContextSelector
                    .anchorSourceNeverExisted();
            return unaddressedCandidates + " compatible activation(s) did "
                    + "not answer the addressed occurrence; "
                    + unaddressedReasons + (neverExisted
                    ? "; " + rootContextSelector.describe()
                    + " was never registered in this run" : "");
        }

        private boolean relationOnlySeed() {
            // An ordinary producer can publish the one relation observed at
            // its semantic output boundary without stopping at every branch.
            return capturesOutputRelation && replayContract == null
                    && !hasExplicitFaultInput;
        }

        /** Body entries this loop may run before the replay is cut. */
        private int maxLoopBodies(String loopId) {
            int marker = safe(loopId).indexOf("#loop:");
            String method = marker > 0
                    ? loopId.substring(0, marker) : "";
            return LoopBoundPolicy.maxLoopBodies(
                    !method.isEmpty()
                            && executionScopeMethods.contains(method));
        }

        /**
         * Indexes the outcomes the recording witnessed at one static branch
         * site.
         */
        private void recordSeedOutcomes(
                String siteId, JsonElement encodedOccurrences) {
            if (siteId.isEmpty() || encodedOccurrences == null
                    || !encodedOccurrences.isJsonArray()) {
                return;
            }
            for (JsonElement element
                    : encodedOccurrences.getAsJsonArray()) {
                if (!element.isJsonObject()) continue;
                JsonObject occurrence = element.getAsJsonObject();
                int ordinal = integer(occurrence, "occurrence", -1);
                // The selected goal decision is the event this task exists
                // to flip, not part of the seed prefix it must preserve.
                // Match the full event identity: earlier turns of the same
                // loop branch remain prefix evidence.
                if (siteId.equals(targetBranchSite)
                        && ordinal == targetBranchOccurrence) {
                    continue;
                }
                JsonElement outcome = occurrence.get("outcome");
                if (outcome == null || !outcome.isJsonPrimitive()
                        || !outcome.getAsJsonPrimitive().isBoolean()) {
                    continue;
                }
                Set<Boolean> outcomes = seedOutcomes.get(siteId);
                if (outcomes == null) {
                    outcomes = new LinkedHashSet<>();
                    seedOutcomes.put(siteId, outcomes);
                }
                outcomes.add(outcome.getAsBoolean());
            }
        }

        private String policy(String siteId) {
            String policy = branchPolicies.get(siteId);
            return "EXPLORE".equals(policy)
                    || "PATH_ASSUMPTION".equals(policy) ? policy : "EXPLORE";
        }

        /** Whether the frozen plan declares a policy for this branch site. */
        private boolean declaresBranch(String siteId) {
            return branchPolicies.containsKey(safe(siteId));
        }

        /** Whether this branch event is the target this task selected. */
        /** Whether this task selected a target branch event at all. */
        /** The next activation ordinal of this address. */
        private synchronized int nextActivationOrdinal() {
            return ++publishedActivations;
        }

        /**
         * The planner numbers a source site inside one activation root.  An
         * ordinary region activation is that root and therefore restarts at
         * one.  LOOP_BODY_ROOT is different: several body activations are
         * slices of one enclosing root-loop activation, so only that address
         * carries a reserved ordinal across its retained turns.
         */
        private synchronized int configuredSourcePhaseOrdinal(
                String key, int localOrdinal) {
            return (loopBodyRoot
                    ? configuredSourcePhaseOrdinals.getOrDefault(
                    safe(key), 0) : 0) + localOrdinal;
        }

        /** Reserves the phase prefix used by one retained loop-body turn. */
        private synchronized void reserveConfiguredSourcePhaseOrdinals(
                Map<String, Integer> used) {
            if (!loopBodyRoot) return;
            for (Map.Entry<String, Integer> entry : used.entrySet()) {
                configuredSourcePhaseOrdinals.merge(entry.getKey(),
                        entry.getValue(), Integer::sum);
            }
        }

        /**
         * Settles the small occurrence ledger before asynchronous decoding.
         * A later body turn is allowed to rely on this reservation; any
         * publication failure is consequently terminal and never rolled back.
         */
        private synchronized void reserveCompletedOccurrence(
                Map<String, Integer> sourceOrdinals,
                Set<String> semanticAnchorIds) {
            reserveConfiguredSourcePhaseOrdinals(sourceOrdinals);
            if (loopBodyRoot) commitSemanticAnchorIds(semanticAnchorIds);
        }

        /**
         * Ports whose producer occurrence the frozen plan names: the
         * exchanges this occurrence was selected for, and therefore the
         * region's <em>selected causal anchor</em>.
         *
         * <p>Derived, never declared: incoming communication ports are the
         * leaves this root may attach, and {@code edgeBindings} names a
         * producer for exactly the ones an edge selected this region for.
         * A region the plan bound to no exchange has no anchor here and is
         * addressed exactly as it is today.</p>
         */
        private Set<String> causalAnchorPorts() {
            return attachProducerOccurrenceByPort.keySet();
        }

        /** Exact source phases that may address a semantic loop turn. */
        private Set<String> configuredSourceAnchorPhases() {
            Set<String> phases = new LinkedHashSet<>();
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                phases.add(phase.phaseId());
            }
            return phases;
        }

        private String sourcePhaseAnchorId(String phaseId) {
            String phase = safe(phaseId);
            return phase.isEmpty() ? "" : "SOURCE_PHASE\n" + phase;
        }

        /** Exact selected response exchange, not merely a reusable port name. */
        private String attachAnchorId(String portId) {
            String port = safe(portId);
            String producer = attachProducerOccurrenceByPort.get(port);
            return port.isEmpty() || safe(producer).isEmpty() ? ""
                    : "COMMUNICATION_EXCHANGE\n" + producer + "\n"
                    + occurrenceId + "\n" + port;
        }

        private Set<String> plannedSemanticAnchorIds() {
            Set<String> planned = new LinkedHashSet<>();
            for (String phaseId : configuredSourceAnchorPhases()) {
                planned.add(sourcePhaseAnchorId(phaseId));
            }
            for (String portId : causalAnchorPorts()) {
                planned.add(attachAnchorId(portId));
            }
            planned.remove("");
            return planned;
        }

        private synchronized Set<String> newSemanticAnchorIds(
                Set<String> carried) {
            Set<String> fresh = new LinkedHashSet<>();
            Set<String> planned = plannedSemanticAnchorIds();
            for (String identity : carried) {
                if (planned.contains(identity)
                        && !observedSemanticAnchorIds.contains(identity)) {
                    fresh.add(identity);
                }
            }
            return fresh;
        }

        private synchronized Set<String> missingSemanticAnchorIds() {
            Set<String> missing = plannedSemanticAnchorIds();
            missing.removeAll(observedSemanticAnchorIds);
            return missing;
        }

        /** Reserves identities of one retained loop turn before decode. */
        private synchronized void commitSemanticAnchorIds(Set<String> ids) {
            boolean anchored = false;
            Set<String> planned = plannedSemanticAnchorIds();
            for (String identity : ids) {
                if (planned.contains(identity)
                        && observedSemanticAnchorIds.add(identity)) {
                    anchored = true;
                }
            }
            if (anchored) anchoredOccurrences++;
        }

        /**
         * Occurrence slots this bounded set reserves for turns that carry the
         * selected causal anchor.
         *
         * <p>A raw polling ordinal is not replay identity: an occurrence is
         * addressed by its selected causal anchor, never by "the 48th turn".
         * The declared budget K_L is unchanged -- these slots are carved out
         * of it, so the kept set is still at most K_L rows; what changes is
         * <em>which</em> K_L turns fill them.  Zero here means the address
         * has no anchor to be addressed by and keeps the plain prefix.</p>
         */
        private synchronized int anchoredOccurrenceSlots() {
            // A replay must reproduce the recorded prefix exactly; re-keying
            // its occurrence set on an anchor would answer a different one.
            if (replayContract != null) return 0;
            int anchors = plannedSemanticAnchorIds().size();
            if (anchors <= 0) return 0;
            return Math.min(anchors, loopOccurrenceBudget);
        }

        /** Whether this address addresses its occurrences by an anchor. */
        private synchronized boolean addressesOccurrencesByCausalAnchor() {
            return loopBodyRoot && anchoredOccurrenceSlots() > 0;
        }

        /**
         * Whether this loop-body region has already published its bounded
         * occurrence set (K_L rows), so a further iteration is a bounded cut.
         *
         * <p>README: a bounded loop is unrolled K_L times, and OCC-1 must not
         * defeat that -- one occurrence per iteration would publish one row
         * per heartbeat (~128 for the DN {@code offerService} loop) and make
         * every iteration pay for full symbolic capture.  {@code
         * publishedActivations} is the net kept-ordinal count, so an iteration
         * whose occurrence was abandoned frees its slot and does not spend the
         * budget: the cap is on published occurrences, not admissions.</p>
         *
         * <p>While an anchored slot is still open the cut waits: the address
         * has not yet seen the exchange it was selected for, and cutting on
         * the raw ordinal would end the window before that exchange happens.
         * The raw number of polling turns is deliberately not bounded by
         * K_L: K_L bounds the <em>published symbolic cases</em>, not how many
         * concrete workload turns may be inspected before the selected RPC
         * exchange occurs.  Workload termination bounds that inspection.  If
         * the exchange never occurs, shutdown publishes a named coverage gap
         * instead of silently substituting an unrelated prefix turn.</p>
         */
        private synchronized boolean cutsBoundedLoopOccurrence() {
            if (!loopBodyRoot) return false;
            int reserved = anchoredOccurrenceSlots();
            if (reserved > 0 && !missingSemanticAnchorIds().isEmpty()
                    && anchoredOccurrences < loopOccurrenceBudget) {
                admittedTurns++;
                return false;
            }
            if (publishedActivations >= loopOccurrenceBudget) return true;
            admittedTurns++;
            return false;
        }

        /** Whether a live bounded address ended without its selected anchor. */
        private synchronized boolean missedCausalAnchor() {
            return admittedTurns > 0 && anchoredOccurrenceSlots() > 0
                    && !missingSemanticAnchorIds().isEmpty();
        }

        /** Evidence for the fail-closed missing-anchor shutdown row. */
        private synchronized JsonObject missedCausalAnchorEvidence() {
            JsonObject evidence = new JsonObject();
            evidence.addProperty("plannedOccurrenceId", occurrenceId);
            evidence.addProperty("regionId", regionId);
            JsonArray ports = new JsonArray();
            for (String portId : causalAnchorPorts()) {
                ports.add(new JsonPrimitive(portId));
            }
            evidence.add("causalAnchorPorts", ports);
            JsonArray phases = new JsonArray();
            for (String phaseId : configuredSourceAnchorPhases()) {
                phases.add(new JsonPrimitive(phaseId));
            }
            evidence.add("configuredSourceAnchorPhases", phases);
            JsonArray missingPhases = new JsonArray();
            for (String phaseId : configuredSourceAnchorPhases()) {
                if (missingSemanticAnchorIds().contains(
                        sourcePhaseAnchorId(phaseId))) {
                    missingPhases.add(new JsonPrimitive(phaseId));
                }
            }
            evidence.add("missingConfiguredSourcePhaseIds", missingPhases);
            JsonArray missingResponses = new JsonArray();
            for (String portId : causalAnchorPorts()) {
                if (!missingSemanticAnchorIds().contains(
                        attachAnchorId(portId))) {
                    continue;
                }
                JsonObject exchange = new JsonObject();
                exchange.addProperty("portId", portId);
                exchange.addProperty("producerOccurrenceId",
                        attachProducerOccurrenceByPort.get(portId));
                exchange.addProperty("consumerOccurrenceId", occurrenceId);
                missingResponses.add(exchange);
            }
            evidence.add("missingResponseExchanges", missingResponses);
            evidence.addProperty("occurrenceBudget", loopOccurrenceBudget);
            evidence.addProperty("anchoredOccurrences",
                    anchoredOccurrences);
            evidence.addProperty("unanchoredTurnsReleased",
                    unanchoredTurnsReleased);
            evidence.addProperty("turnsAdmitted", admittedTurns);
            return evidence;
        }

        /**
         * Settles one finished turn of a bounded loop body against the
         * region's selected causal anchor.
         *
         * <p>A turn that carried the anchor takes a reserved slot.  A turn
         * that carried none takes an ordinary slot while the prefix quota
         * lasts -- which is what every turn does today -- and past that it
         * gives its ordinal back, spending nothing, so the reserved slots
         * stay open for the turns the plan actually selected this region
         * for.  Nothing is fabricated: the anchor is the VM's own answer at
         * the declared attach.</p>
         *
         * @return {@code true} when this turn published no occurrence
         */
        private synchronized boolean releasesUnanchoredLoopTurn(
                boolean carriedNewSemanticAnchor) {
            if (!loopBodyRoot) return false;
            int reserved = anchoredOccurrenceSlots();
            if (reserved <= 0) return false;
            if (carriedNewSemanticAnchor
                    && anchoredOccurrences < loopOccurrenceBudget) {
                return false;
            }
            int remainingAnchorSlots = Math.min(
                    missingSemanticAnchorIds().size(),
                    loopOccurrenceBudget - anchoredOccurrences);
            int ordinaryActivations = publishedActivations
                    - anchoredOccurrences;
            if (ordinaryActivations <= loopOccurrenceBudget
                    - anchoredOccurrences - remainingAnchorSlots) {
                return false;
            }
            unanchoredTurnsReleased++;
            return true;
        }

        /** Claims the one bounded-cut marker write for this region. */
        private synchronized boolean claimLoopBoundCutMarker() {
            if (loopBoundCutRecorded) return false;
            loopBoundCutRecorded = true;
            return true;
        }

        /**
         * Gives back an ordinal whose activation published nothing, so the
         * ordinals of one address stay dense and gapless.  Only one
         * activation of an address runs at a time, so the ordinal being
         * returned is always the last one taken.
         */
        private synchronized void releaseActivationOrdinal(int ordinal) {
            if (ordinal > 0 && ordinal == publishedActivations) {
                publishedActivations--;
            }
        }

        private boolean declaresTargetBranch() {
            return !targetBranchSite.isEmpty();
        }

        /**
         * Reserves completed evidence before reopening task admission.
         *
         * <p>Loop-body roots remain governed exclusively by K_L. Replay
         * tasks remain open for the path worklist's flipped relation. A
         * complete ordinary producer also remains admissible because its
         * later activations may carry symbolic state to consumers; only their
         * duplicate result rows are suppressed.</p>
         */
        private void reserveCompletedEvidence(boolean targetReached,
                                              boolean relationComplete) {
            if (capturesTargetReach && targetReached) {
                completedTargetReserved = true;
            }
            if (relationOnlySeed() && !loopBodyRoot && relationComplete) {
                completedRelationReserved = true;
            }
        }

        private boolean blocksAdmissionAfterCompletedTarget() {
            return completedTargetReserved;
        }

        private boolean suppressesDuplicateRelationResult() {
            return completedRelationReserved;
        }

        /**
         * Whether this occurrence directly witnessed the selected failure
         * outcome, rather than merely deviating from its recorded seed path.
         */
        private boolean reachedRequiredTargetOutcome(JsonObject reach) {
            return declaresTargetBranch()
                    && reach != null
                    && targetBranchSite.equals(string(reach, "siteId"))
                    && targetBranchOccurrence == integer(reach,
                    "occurrence", -1)
                    && reach.has("outcome")
                    && reach.get("outcome").isJsonPrimitive()
                    && reach.getAsJsonPrimitive("outcome").isBoolean()
                    && reach.get("outcome").getAsBoolean()
                    == targetBranchRequiredOutcome;
        }

        /** The declared target branch event, for a named coverage gap. */
        private String targetBranchLabel() {
            return targetBranchSite + "#" + targetBranchOccurrence;
        }

        private static boolean targetRequiredOutcome(
                JsonArray branches, String targetSite,
                int targetOccurrence) {
            if (safe(targetSite).isEmpty()) return false;
            Boolean required = null;
            for (JsonElement element : branches) {
                if (!element.isJsonObject()) continue;
                JsonObject branch = element.getAsJsonObject();
                if (!targetSite.equals(string(branch, "siteId"))
                        || targetOccurrence != integer(branch,
                        "selectedOccurrence", -1)) {
                    continue;
                }
                JsonElement encoded = branch.get("requiredOutcome");
                if (encoded == null || !encoded.isJsonPrimitive()
                        || !encoded.getAsJsonPrimitive().isBoolean()) {
                    throw new IllegalArgumentException(
                            "target branch requires a boolean outcome: "
                                    + targetSite + '#' + targetOccurrence);
                }
                boolean candidate = encoded.getAsBoolean();
                if (required != null && required != candidate) {
                    throw new IllegalArgumentException(
                            "ambiguous target required outcome: "
                                    + targetSite + '#' + targetOccurrence);
                }
                required = candidate;
            }
            if (required == null) {
                throw new IllegalArgumentException(
                        "target branch is absent from the branch catalog: "
                                + targetSite + '#' + targetOccurrence);
            }
            return required;
        }

        private OutputCaptureSpec outputCapture(String captureBindingId) {
            OutputCaptureSpec match = null;
            for (OutputCaptureSpec request : outputCaptures) {
                if (!request.captureBindingId().equals(
                        safe(captureBindingId))) {
                    continue;
                }
                if (match != null) return null;
                match = request;
            }
            return match;
        }

    }

    /** The bounded campaign this JVM executes. */
    private static final class Configuration {
        /**
         * How many tasks one campaign may contain.  A campaign has to be
         * bounded to be a campaign: the runtime instruments and admits every
         * row, so an unbounded plan is a runaway workload rather than an
         * experiment, and it is refused by name instead of being started.
         */
        static final String MAX_TASKS_PROPERTY =
                "causynth.concolic.campaign.max.tasks";
        static final int DEFAULT_MAX_TASKS = 64;

        private final Path resultFile;
        private final List<RuntimeTask> tasks;
        /**
         * Tasks whose occurrence is running as a candidate right now, and
         * tasks whose candidate confirmed its anchor and published.
         *
         * <p>Together they turn admission into what README {@code OCC-1} asks
         * for: every compatible root invocation is a candidate for the
         * address, one at a time, until one of them is the addressed
         * occurrence.</p>
         */
        private final boolean[] candidateLive;
        private final boolean[] occurrenceClaimed;
        /** Halt-status contribution of each task that has settled. */
        private final Map<String, Integer> settled = new LinkedHashMap<>();
        private boolean unansweredAddressesPublished;

        private Configuration(Path resultFile, List<RuntimeTask> tasks) {
            this.resultFile = resultFile;
            this.tasks = Collections.unmodifiableList(tasks);
            this.candidateLive = new boolean[tasks.size()];
            this.occurrenceClaimed = new boolean[tasks.size()];
        }

        /**
         * Releases the address of a candidate that ended without being the
         * occurrence, so the next compatible invocation may try for it.
         */
        /**
         * Claims every other open occurrence of one root that this same
         * activation could answer.
         *
         * <p>A campaign instruments one entry hook per plan row, so a root
         * carrying two selected occurrences of one region -- HDFS-11741 plans
         * {@code #1} and {@code #9} of the balancer's {@code Dispatcher$1} --
         * calls two hooks on every activation.  Letting each hook start its
         * own region put two VM contexts on one thread, and since
         * {@code CURRENT_TOKEN} holds one token the inner one silently took
         * every capture: campaign-takeover-22 exported the SASL handshake
         * under occurrence {@code #1}, which then failed on its own
         * constructor captures, while {@code #9} sat live and blind and
         * reported all three leaves missing.  One activation is one region;
         * the other occurrences ride along as claimants and the exit decides
         * which of them it answered.</p>
         *
         * <p>Only an occurrence {@link #select} would itself have admitted
         * on this invocation is claimed -- the same root address and the same
         * request-API gate -- so this never widens who may answer an address:
         * the sibling would have been admitted on its own hook anyway.</p>
         */
        private synchronized List<RuntimeTask> claimSiblingOccurrences(
                RuntimeTask primary, String rootMethod, Object receiver,
                Object[] rootArguments, String threadName,
                String requestApi) {
            List<RuntimeTask> claimed = new ArrayList<>();
            for (int index = 0; index < tasks.size(); index++) {
                RuntimeTask task = tasks.get(index);
                if (task == primary || candidateLive[index]
                        || task.blocksAdmissionAfterCompletedTarget()
                        || !task.regionId.equals(primary.regionId)
                        // Entry hooks may share a method, region and source
                        // while naming different concurrent invocations.  A
                        // sibling is another contract on this exact frozen
                        // activation, never merely another compatible root.
                        || primary.activationId.isEmpty()
                        || !task.activationId.equals(primary.activationId)
                        || !task.rootMethod.equals(primary.rootMethod)
                        || !task.sourceKey.equals(primary.sourceKey)
                        || !task.rootContextSelector.sameAddress(
                        primary.rootContextSelector, requestApi)) {
                    continue;
                }
                if (!compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector, task.rootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                candidateLive[index] = true;
                claimed.add(task);
            }
            return claimed;
        }

        private synchronized void releaseCandidate(RuntimeTask task) {
            int index = tasks.indexOf(task);
            if (index >= 0) candidateLive[index] = false;
        }

        /**
         * States every selected address this run could not answer with exactly
         * one occurrence, once each, now that the run is over and both "never
         * registered in this run" and "several activations fit" are decidable
         * rather than snapshots the same run can contradict.
         *
         * <p>An address nothing answered is a coverage statement about the
         * replay; an address several activations answered is README {@code
         * OCC-1}'s ambiguity, a statement about the address itself.</p>
         */
        private synchronized void publishUnansweredAddresses() {
            if (unansweredAddressesPublished) return;
            unansweredAddressesPublished = true;
            for (int index = 0; index < tasks.size(); index++) {
                RuntimeTask task = tasks.get(index);
                if (task.missedCausalAnchor()) {
                    writeSkipped(task, SKIP_CAUSAL_ANCHOR_NOT_OBSERVED,
                            "selected semantic anchor identities "
                                    + task.missingSemanticAnchorIds()
                                    + " were not observed before workload "
                                    + "termination; K_L bounded published "
                                    + "cases, not polling turns",
                            task.missedCausalAnchorEvidence());
                    continue;
                }
                // An address that published at least one occurrence has been
                // answered for end-of-run diagnostics. Goal completion owns
                // the separate decision to admit another activation.
                if (occurrenceClaimed[index]) continue;
                if (task.unaddressedCandidates == 0) continue;
                writeSkipped(task, task.rootContextSelector
                                .anchorSourceNeverExisted()
                                ? SKIP_ANCHOR_SOURCE_NEVER_EXISTED
                                : SKIP_OCCURRENCE_ANCHOR_UNMATCHED,
                        task.unansweredAddress(), null);
            }
        }

        /** Records that a candidate was the occurrence and published it. */
        private synchronized void claimOccurrence(RuntimeTask task) {
            int index = tasks.indexOf(task);
            if (index < 0) return;
            candidateLive[index] = false;
            occurrenceClaimed[index] = true;
        }

        /** Marks durable evidence without clearing a newer live candidate. */
        private synchronized void markOccurrencePublished(RuntimeTask task) {
            int index = tasks.indexOf(task);
            if (index >= 0) occurrenceClaimed[index] = true;
        }

        /** The campaign task with this id, or {@code null}. */
        private RuntimeTask taskById(String taskId) {
            if (taskId == null || taskId.isEmpty()) return null;
            for (RuntimeTask task : tasks) {
                if (taskId.equals(task.taskId)) return task;
            }
            return null;
        }

        /** Claims at most one open task for this root invocation. */
        private synchronized RuntimeTask select(String instrumentationSelector,
                                                String rootMethod,
                                                Object receiver,
                                                Object[] rootArguments) {
            String threadName = Thread.currentThread().getName();
            // A short-lived Runnable need not be registered as an alias
            // itself: an exact inherited async/request/RPC context can still
            // attribute its entry.
            SourceRef registeredReceiverSource =
                    RuntimeTraceContext.sourceFor(receiver);
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            String requestApi = context.requestApi;
            RuntimeTask completedRelationFallback = null;
            for (int index = 0; index < tasks.size(); index++) {
                RuntimeTask task = tasks.get(index);
                if (!task.instrumentationSelector.equals(
                        safe(instrumentationSelector))) continue;
                if (task.blocksAdmissionAfterCompletedTarget()) continue;
                if (!compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector, task.rootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                // The root must have entered the selected local scope.
                if (!task.rootContextSelector.requestApi.isEmpty()
                        && !task.rootContextSelector.requestApi.equals(
                        safe(requestApi))) {
                    task.noteUnaddressedCandidate(
                            "matching root entered request API "
                                    + safe(requestApi) + " instead of "
                                    + task.rootContextSelector.requestApi);
                    continue;
                }
                // INHERITED_CONTEXT is an exact thread-context address.
                // Discovery named this occurrence's source from the context
                // the thread inherited because its receiver carries no alias
                // of its own -- the balancer builds Dispatcher$1 and
                // KeyManager$BlockKeyUpdater under the test thread's
                // registered client source -- so replay re-checks the same
                // authority.  An alias, if the receiver does have one, must
                // still agree: an object that belongs to another node or
                // another epoch never answers this address.
                if (task.rootContextSelector.inheritedContextAnchor) {
                    SourceRef inherited = context.source;
                    if (inherited == null
                            || !task.sourceKey.equals(inherited.key())
                            || registeredReceiverSource != null
                            && !task.sourceKey.equals(
                            registeredReceiverSource.key())) {
                        task.noteUnaddressedCandidate(
                                registeredReceiverSource != null
                                        && !task.sourceKey.equals(
                                        registeredReceiverSource.key())
                                        ? "matching root receiver belonged to "
                                        + registeredReceiverSource.key()
                                        + " instead of " + task.sourceKey
                                        : inherited == null
                                        ? "matching root inherited no source; "
                                        + "its anchor names " + task.sourceKey
                                        : "matching root inherited "
                                        + inherited.key() + " instead of "
                                        + task.sourceKey);
                        continue;
                    }
                }
                // REGISTERED_SOURCE is an exact receiver-owned occurrence
                // address.
                boolean exactRegistered = task.rootContextSelector
                        .receiverScoped
                        && task.rootContextSelector.registeredSourceAnchor;
                if (exactRegistered
                        && (registeredReceiverSource == null
                        || !task.sourceKey.equals(
                        registeredReceiverSource.key()))) {
                    task.noteUnaddressedCandidate(
                            registeredReceiverSource == null
                                    ? "matching root receiver had no "
                                    + "registered source; its anchor names "
                                    + task.sourceKey
                                    : "matching root receiver belonged to "
                                    + registeredReceiverSource.key()
                                    + " instead of " + task.sourceKey);
                    continue;
                }
                if (!exactRegistered
                        && task.rootContextSelector.receiverScoped
                        && registeredReceiverSource != null
                        && !RuntimeTraceContext.sameSourceIdentity(
                        task.sourceKey, registeredReceiverSource.key())) {
                    task.noteUnaddressedCandidate(
                            "matching root receiver belonged to "
                            + registeredReceiverSource.key() + " instead of "
                            + task.sourceKey);
                    continue;
                }
                // A further candidate of an incomplete address is another
                // occurrence, not an ambiguity. Only one runs at a time; a
                // completed non-loop seed remains eligible for later symbolic
                // propagation, but it must not starve another selected
                // occurrence of the same root that has not published yet.
                if (candidateLive[index]) continue;
                if (task.suppressesDuplicateRelationResult()) {
                    if (completedRelationFallback == null) {
                        completedRelationFallback = task;
                    }
                    continue;
                }
                candidateLive[index] = true;
                return task;
            }
            if (completedRelationFallback != null) {
                // Hooks are injected per occurrence.  A completed producer's
                // hook therefore runs before later hooks at the same root and
                // would otherwise open a duplicate VM region on every
                // invocation, making the unfinished occurrence's hook see an
                // already-active thread forever.  Propagation fallback is
                // last across the whole compatible campaign, not merely last
                // among rows sharing this hook's selector.
                if (unfinishedTaskMatchesInvocation(rootMethod, receiver,
                        rootArguments, threadName, requestApi,
                        registeredReceiverSource, context)) {
                    return null;
                }
                int index = tasks.indexOf(completedRelationFallback);
                if (index >= 0 && !candidateLive[index]) {
                    candidateLive[index] = true;
                    return completedRelationFallback;
                }
            }
            return null;
        }

        /** Whether a later entry hook can admit unfinished work here. */
        private boolean unfinishedTaskMatchesInvocation(
                String rootMethod, Object receiver, Object[] rootArguments,
                String threadName, String requestApi,
                SourceRef registeredReceiverSource,
                RuntimeTraceContext.View context) {
            for (int index = 0; index < tasks.size(); index++) {
                RuntimeTask task = tasks.get(index);
                if (candidateLive[index]
                        || task.blocksAdmissionAfterCompletedTarget()
                        || task.suppressesDuplicateRelationResult()
                        || !compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector, task.rootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                if (!task.rootContextSelector.requestApi.isEmpty()
                        && !task.rootContextSelector.requestApi.equals(
                        safe(requestApi))) {
                    continue;
                }
                if (task.rootContextSelector.inheritedContextAnchor) {
                    SourceRef inherited = context.source;
                    if (inherited == null
                            || !task.sourceKey.equals(inherited.key())
                            || registeredReceiverSource != null
                            && !task.sourceKey.equals(
                            registeredReceiverSource.key())) {
                        continue;
                    }
                }
                boolean exactRegistered = task.rootContextSelector
                        .receiverScoped
                        && task.rootContextSelector.registeredSourceAnchor;
                if (exactRegistered
                        && (registeredReceiverSource == null
                        || !task.sourceKey.equals(
                        registeredReceiverSource.key()))) {
                    continue;
                }
                if (!exactRegistered
                        && task.rootContextSelector.receiverScoped
                        && registeredReceiverSource != null
                        && !RuntimeTraceContext.sameSourceIdentity(
                        task.sourceKey, registeredReceiverSource.key())) {
                    continue;
                }
                return true;
            }
            return false;
        }

        /**
         * Records one task's terminal outcome and returns the campaign's halt
         * status once every task has settled, or {@code -1} while any task can
         * still produce evidence.
         */
        private synchronized int settle(String taskId, int status) {
            if (tasks.isEmpty()) return -1;
            Integer previous = settled.get(safe(taskId));
            if (previous == null) settled.put(safe(taskId), status);
            if (settled.size() < tasks.size()) return -1;
            int worst = 0;
            for (Integer contribution : settled.values()) {
                worst = Math.max(worst, contribution);
            }
            return worst;
        }

        private static Configuration load() {
            String planValue = safe(System.getProperty(
                    "causynth.concolic.task.plan")).trim();
            String selectedTasks = safe(System.getProperty(
                    "causynth.concolic.task.id")).trim();
            if (planValue.isEmpty()) {
                return new Configuration(null,
                        Collections.<RuntimeTask>emptyList());
            }
            String resultValue = safe(System.getProperty(
                    "causynth.concolic.results")).trim();
            if (selectedTasks.isEmpty() || resultValue.isEmpty()) {
                throw new IllegalStateException("Concolic runtime requires "
                        + "task id and result path with a task plan");
            }
            Path result = Paths.get(resultValue);
            Path plan = Paths.get(planValue);
            if (!Files.isRegularFile(plan)) {
                throw new IllegalStateException(
                        "Concolic task plan not found: " + plan);
            }
            Set<String> selected = campaignTaskIds(selectedTasks);
            List<RuntimeTask> tasks = new ArrayList<>();
            try (BufferedReader reader = Files.newBufferedReader(plan,
                    StandardCharsets.UTF_8)) {
                Set<String> taskIds = new LinkedHashSet<>();
                int maxTasks = maxCampaignTasks();
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) continue;
                    JsonElement parsed = new JsonParser().parse(line);
                    if (!parsed.isJsonObject()) {
                        throw new IllegalStateException("malformed plan: "
                                + "every task plan row must be an object");
                    }
                    if (tasks.size() == maxTasks) {
                        throw new IllegalStateException("malformed plan: "
                                + "campaign exceeds its bound of " + maxTasks
                                + " tasks");
                    }
                    ExecutionTask encoded = ExecutionTask.decode(
                            parsed.getAsJsonObject());
                    RuntimeTask task = new RuntimeTask(encoded);
                    if (!taskIds.add(task.taskId)) {
                        throw new IllegalStateException("malformed plan: "
                                + "duplicate execution task " + task.taskId);
                    }
                    if (!selected.contains(task.taskId)) {
                        throw new IllegalStateException("malformed plan: "
                                + "task plan contains unselected task "
                                + task.taskId);
                    }
                    tasks.add(task);
                }
            } catch (IOException | RuntimeException exception) {
                throw new IllegalStateException("Causynth rejected "
                        + "task plan " + plan + ": "
                        + exception.getMessage(), exception);
            }
            for (String taskId : selected) {
                boolean present = false;
                for (RuntimeTask task : tasks) {
                    present |= task.taskId.equals(taskId);
                }
                if (!present) {
                    throw new IllegalStateException("Selected execution task "
                            + taskId + " is absent in " + plan);
                }
            }
            return new Configuration(result, tasks);
        }

        /** The selected campaign, in plan order. */
        private static Set<String> campaignTaskIds(String property) {
            Set<String> ids = new LinkedHashSet<>();
            for (String value : property.split(",")) {
                String taskId = safe(value).trim();
                if (taskId.isEmpty()) continue;
                if (!ids.add(taskId)) {
                    throw new IllegalStateException("malformed plan: "
                            + "duplicate selected execution task " + taskId);
                }
            }
            if (ids.isEmpty()) {
                throw new IllegalStateException("malformed plan: "
                        + "no execution task is selected");
            }
            return ids;
        }

        private static int maxCampaignTasks() {
            String configured = safe(System.getProperty(
                    MAX_TASKS_PROPERTY)).trim();
            if (configured.isEmpty()) return DEFAULT_MAX_TASKS;
            try {
                int value = Integer.parseInt(configured);
                if (value <= 0) {
                    throw new IllegalStateException("malformed plan: "
                            + MAX_TASKS_PROPERTY + " must be positive");
                }
                return value;
            } catch (NumberFormatException malformed) {
                throw new IllegalStateException("malformed plan: "
                        + MAX_TASKS_PROPERTY + " must be a number");
            }
        }
    }

    private static boolean compatibleRoot(
            String selectedMethod, String actualMethod,
            RootContextSelector context, RootArgumentSelector arguments,
            Object receiver, Object[] rootArguments, String threadName) {
        if (!safe(selectedMethod).equals(safe(actualMethod))) return false;
        if (!context.matches(receiver, threadName)) {
            return false;
        }
        return !arguments.present || arguments.matches(rootArguments);
    }


    /** Test seam listing the configured campaign, in plan order. */
    static List<String> campaignTaskIdsForTests() {
        List<String> ids = new ArrayList<>();
        for (RuntimeTask task : configuration().tasks) {
            ids.add(task.taskId);
        }
        return ids;
    }

    /**
     * Test seam mimicking {@code admitRegion}'s bounded-loop occurrence cap
     * over {@code admissions} sequential admissions of one task: each
     * admission that is not a bounded cut publishes one occurrence (takes an
     * ordinal), and the returned count is how many published.  A loop-body
     * region caps at K_L; any other region is uncapped.  The one bounded-cut
     * marker, when written, lands in the configured results file.
     */
    static int simulateAdmissionsForTests(String taskId, int admissions) {
        RuntimeTask task = configuration().taskById(taskId);
        if (task == null) return 0;
        int published = 0;
        for (int index = 0; index < admissions; index++) {
            if (boundedLoopOccurrenceCut(task)) continue;
            task.nextActivationOrdinal();
            published++;
        }
        return published;
    }

    /**
     * Test seam running one bounded loop body turn by turn, where turn
     * {@code index} carried the region's selected causal anchor exactly when
     * {@code anchored[index]}, and naming the turns whose occurrence the
     * address kept.
     */
    static List<Integer> simulateAnchoredTurnsForTests(
            String taskId, boolean[] anchored) {
        RuntimeTask task = configuration().taskById(taskId);
        if (task == null) return Collections.emptyList();
        List<Integer> kept = new ArrayList<>();
        for (int turn = 0; turn < anchored.length; turn++) {
            if (boundedLoopOccurrenceCut(task)) continue;
            int ordinal = task.nextActivationOrdinal();
            Set<String> carried = new LinkedHashSet<>();
            if (anchored[turn]) {
                Set<String> missing = task.missingSemanticAnchorIds();
                if (!missing.isEmpty()) {
                    carried.add(missing.iterator().next());
                }
            }
            Set<String> fresh = task.newSemanticAnchorIds(carried);
            if (task.releasesUnanchoredLoopTurn(!fresh.isEmpty())) {
                task.releaseActivationOrdinal(ordinal);
            } else {
                kept.add(turn + 1);
                task.commitSemanticAnchorIds(fresh);
            }
        }
        return kept;
    }

    /** Exact-identity variant used to exercise duplicate and co-located anchors. */
    static List<Integer> simulateSemanticAnchorTurnsForTests(
            String taskId, String[][] phaseIdsByTurn,
            String[][] responsePortsByTurn) {
        RuntimeTask task = configuration().taskById(taskId);
        if (task == null) return Collections.emptyList();
        int turns = Math.max(phaseIdsByTurn == null ? 0
                        : phaseIdsByTurn.length,
                responsePortsByTurn == null ? 0
                        : responsePortsByTurn.length);
        List<Integer> kept = new ArrayList<>();
        for (int turn = 0; turn < turns; turn++) {
            if (boundedLoopOccurrenceCut(task)) continue;
            int ordinal = task.nextActivationOrdinal();
            Set<String> carried = new LinkedHashSet<>();
            if (phaseIdsByTurn != null && turn < phaseIdsByTurn.length
                    && phaseIdsByTurn[turn] != null) {
                for (String phaseId : phaseIdsByTurn[turn]) {
                    carried.add(task.sourcePhaseAnchorId(phaseId));
                }
            }
            if (responsePortsByTurn != null
                    && turn < responsePortsByTurn.length
                    && responsePortsByTurn[turn] != null) {
                for (String portId : responsePortsByTurn[turn]) {
                    carried.add(task.attachAnchorId(portId));
                }
            }
            Set<String> fresh = task.newSemanticAnchorIds(carried);
            if (task.releasesUnanchoredLoopTurn(!fresh.isEmpty())) {
                task.releaseActivationOrdinal(ordinal);
            } else {
                kept.add(turn + 1);
                task.commitSemanticAnchorIds(fresh);
            }
        }
        return kept;
    }

    /** Provisional task-scoped source ordinal; does not consume it. */
    static int configuredSourcePhaseOrdinalForTests(
            String taskId, String key, int localOrdinal) {
        RuntimeTask task = configuration().taskById(taskId);
        return task == null ? 0
                : task.configuredSourcePhaseOrdinal(key, localOrdinal);
    }

    /** Commits a source phase exactly as one published activation does. */
    static void commitConfiguredSourcePhaseOrdinalsForTests(
            String taskId, String key, int used) {
        RuntimeTask task = configuration().taskById(taskId);
        if (task == null) return;
        Map<String, Integer> phases = new LinkedHashMap<>();
        phases.put(key, used);
        task.reserveConfiguredSourcePhaseOrdinals(phases);
    }

    /** Test seam for exact task-directed admission. */
    static String admitCampaignTaskForTests(
            String taskId, String rootMethod, Object receiver,
            Object[] rootArguments) {
        RuntimeTask requested = configuration().taskById(taskId);
        if (requested == null) return "";
        RuntimeTask admitted = configuration().select(
                requested.instrumentationSelector, rootMethod, receiver,
                rootArguments);
        return admitted == null ? "" : admitted.taskId;
    }

    /**
     * Test seam listing the other occurrences one activation would carry
     * alongside the named task.
     */
    static List<String> claimSiblingOccurrencesForTests(
            String taskId, String rootMethod, Object receiver,
            Object[] rootArguments) {
        return claimSiblingOccurrencesForTests(taskId, rootMethod, receiver,
                rootArguments, RuntimeTraceContext.current().requestApi);
    }

    /**
     * Test seam listing the other occurrences one activation entered under
     * the named request API would carry alongside the named task.
     */
    static List<String> claimSiblingOccurrencesForTests(
            String taskId, String rootMethod, Object receiver,
            Object[] rootArguments, String requestApi) {
        Configuration configured = configuration();
        RuntimeTask primary = configured.taskById(taskId);
        List<String> claimed = new ArrayList<>();
        if (primary == null) return claimed;
        for (RuntimeTask task : configured.claimSiblingOccurrences(primary,
                rootMethod, receiver, rootArguments,
                Thread.currentThread().getName(), requestApi)) {
            claimed.add(task.taskId);
        }
        return claimed;
    }

    /**
     * Test seam admitting one activation and answering its address with it,
     * so README {@code OCC-1} ambiguity can be exercised without a VM.
     */
    static boolean claimCampaignTaskForTests(
            String taskId, String rootMethod, Object receiver,
            Object[] rootArguments) {
        Configuration configured = configuration();
        RuntimeTask requested = configured.taskById(taskId);
        if (requested == null) return false;
        RuntimeTask admitted = configured.select(
                requested.instrumentationSelector, rootMethod, receiver,
                rootArguments);
        if (admitted == null) return false;
        configured.claimOccurrence(admitted);
        return true;
    }

    /**
     * Reflective view of the concolic VM's static entry points.
     *
     * <p>Every name below is looked up by reflection so this class remains
     * loadable on a stock JDK. A replay plan requires the complete current
     * broker surface before its workload starts.</p>
     */
    private static final class EngineApi {
        private Method openWorkloadSession;
        private Method closeWorkloadSession;
        private Method workloadSessionStatus;
        private Method startRegion;
        private Method currentContextId;
        private Method symbolizeWithPrefix;
        private Method symbolizeField;
        private Method symbolizeExactField;
        private Method observeExactPrimitiveField;
        private Method snapshotContainer;
        private Method trackContainer;
        private Method getExpression;
        private Method getFieldExpression;
        private Method finishRegion;
        private Method getPathCondition;
        private Method pausePathCondition;
        private Method resumePathCondition;
        private Method markBranch;
        private Method getBranchEvents;
        private Method cleanupEnd;
        private Method export;
        private Method attach;
        private Method range;
        private Method activate;
        private Method selectField;
        private Method selectElement;
        private Method selectMap;
        private Method fieldVersions;
        private Method elementVersions;
        private Method mapVersions;
        private Method eventLedger;

        private void requireCurrentCapabilities() {
            List<String> missing = new ArrayList<>();
            for (Field capability : EngineApi.class.getDeclaredFields()) {
                if (capability.getType() != Method.class) continue;
                try {
                    if (capability.get(this) == null) {
                        missing.add(capability.getName());
                    }
                } catch (IllegalAccessException impossible) {
                    throw new AssertionError(impossible);
                }
            }
            Collections.sort(missing);
            if (!missing.isEmpty()) {
                throw new IllegalStateException("Concolic task plan requires "
                        + "current custom VM broker capabilities: " + missing);
            }
        }

        /** Positive session id, or a negative VM status. */
        private long openWorkloadSession() throws Exception {
            Object status = openWorkloadSession.invoke(null);
            return status instanceof Number
                    ? ((Number) status).longValue() : Long.MIN_VALUE;
        }

        /** Zero, or a negative VM status. */
        private long closeWorkloadSession() throws Exception {
            Object status = closeWorkloadSession.invoke(null);
            return status instanceof Number
                    ? ((Number) status).longValue() : Long.MIN_VALUE;
        }

        /** One JSON snapshot of the session, or {@code ""} when absent. */
        private String workloadSessionStatus() {
            if (workloadSessionStatus == null) return "";
            try {
                return safe(String.valueOf(
                        workloadSessionStatus.invoke(null)));
            } catch (Throwable unavailable) {
                return "";
            }
        }

        private void start(String regionId, String taskId) throws Exception {
            Object status = startRegion.invoke(null, regionId, taskId);
            if (status instanceof Number
                    && ((Number) status).longValue() != 0L) {
                throw new IllegalStateException(
                        "custom concolic engine rejected region start: "
                                + ((Number) status).longValue());
            }
        }

        private long currentContextId() throws Exception {
            Object value = currentContextId.invoke(null);
            return value instanceof Number
                    ? ((Number) value).longValue() : 0L;
        }

        private void symbolize(Object value, String prefix) throws Exception {
            symbolizeWithPrefix.invoke(null, value, prefix);
        }

        private void symbolizeField(Object owner, String field, String prefix)
                throws Exception {
            symbolizeField.invoke(null, owner, field, prefix);
        }

        private void symbolizeExactField(
                Object owner, String fieldSignature, String prefix)
                throws Exception {
            DeclaredField field = FieldPathSpec.declaredField(
                    safe(fieldSignature));
            if (field == null) {
                throw new UnsupportedOperationException(
                        "no exact declared field for symbolized leaf: "
                                + safe(fieldSignature));
            }
            symbolizeExactField.invoke(null, owner, field.owner(),
                    field.name(), javaTypeDescriptor(field.type()), prefix);
        }

        private void observeExactPrimitiveField(
                Object owner, String fieldSignature) throws Exception {
            DeclaredField field = FieldPathSpec.declaredField(
                    safe(fieldSignature));
            if (field == null) {
                throw new UnsupportedOperationException(
                        "no exact declared field for observed leaf: "
                                + safe(fieldSignature));
            }
            observeExactPrimitiveField.invoke(null, owner, field.owner(),
                    field.name(), javaTypeDescriptor(field.type()));
        }

        private boolean snapshotContainer(
                Object value, Object[] keys, Object[] values, int kind)
                throws Exception {
            return Boolean.TRUE.equals(snapshotContainer.invoke(
                    null, value, keys, values, kind));
        }

        private boolean trackContainer(Object value, String prefix)
                throws Exception {
            return Boolean.TRUE.equals(trackContainer.invoke(
                    null, value, prefix));
        }

        private String expression(Object value) throws Exception {
            return String.valueOf(getExpression.invoke(null, value));
        }

        private String fieldExpression(
                Object owner, String declaringClass, String fieldName,
                String fieldDescriptor, Object value)
                throws Exception {
            return String.valueOf(getFieldExpression.invoke(null, owner,
                    declaringClass, fieldName, fieldDescriptor, value));
        }

        private String finish() throws Exception {
            return String.valueOf(finishRegion.invoke(null));
        }

        private void pausePathCondition() throws Exception {
            pausePathCondition.invoke(null);
        }

        private void resumePathCondition() throws Exception {
            resumePathCondition.invoke(null);
        }

        private String branchEvents() throws Exception {
            return String.valueOf(getBranchEvents.invoke(null));
        }

        private void cleanupAfterFailure() {
            if (cleanupEnd != null) {
                try {
                    cleanupEnd.invoke(null);
                } catch (Throwable ignored) {
                }
            }
        }

        /**
         * Exports one field and reports the VM ledger event the export is.
         *
         * <p>README {@code RPC-1}: the exporter is one endpoint of the {@code
         * VALUE_HANDOFF} edge, so it has to name its own event.</p>
         *
         * @param eventOut single-slot out-array receiving the export event
         */
        private long exportExpression(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long[] eventOut) throws Exception {
            Object handle = export.invoke(null, owner, declaringClass,
                    fieldName, descriptor, eventOut);
            return handle instanceof Number
                    ? ((Number) handle).longValue() : 0L;
        }

        /**
         * Attaches one live handle and reports both edge endpoints: the export
         * event as the return value, this receive's attach event in
         * {@code eventOut}.
         *
         * <p>README {@code RPC-1}: one export may be attached at several
         * receivers, so the export id does not name this receive; recovering
         * it from the order domain returns whichever attach sorts first.</p>
         */
        private long attachExpression(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long handle, long[] eventOut)
                throws Exception {
            Object answer = attach.invoke(null, owner, declaringClass,
                    fieldName, descriptor, handle, eventOut);
            return answer instanceof Number
                    ? ((Number) answer).longValue()
                    : RpcExpressionHandoff.MALFORMED_RESULT;
        }

        private boolean activateEventLedger() throws Exception {
            Object recording = activate.invoke(null);
            if (!(recording instanceof Boolean)) {
                throw new IllegalStateException(
                        "activateConcolicEventLedger returned no boolean status");
            }
            return ((Boolean) recording).booleanValue();
        }

        private String pathConditionRange(int startIndex, int endIndex)
                throws Exception {
            return String.valueOf(range.invoke(null, startIndex, endIndex));
        }

        private long selectSharedFieldCarrier(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            Object version = selectField.invoke(null, owner, declaringClass,
                    fieldName, descriptor);
            if (!(version instanceof Number)) {
                throw new IllegalStateException(
                        "selectSharedFieldCarrier returned no numeric version");
            }
            return ((Number) version).longValue();
        }

        private long selectSharedElementCarrier(Object array, int index)
                throws Exception {
            Object version = selectElement.invoke(null, array, index);
            if (!(version instanceof Number)) {
                throw new IllegalStateException(
                        "selectSharedElementCarrier returned no numeric version");
            }
            return ((Number) version).longValue();
        }

        private long selectSharedMapCarrier(Object map) throws Exception {
            Object version = selectMap.invoke(null, map);
            if (!(version instanceof Number)) {
                throw new IllegalStateException(
                        "selectSharedMapCarrier returned no numeric version");
            }
            return ((Number) version).longValue();
        }

        private String sharedMapVersions(Object map) throws Exception {
            return requiredVmJson(mapVersions.invoke(null, map),
                    "getSharedMapVersions");
        }

        private String sharedFieldVersions(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            return requiredVmJson(fieldVersions.invoke(null, owner,
                    declaringClass, fieldName, descriptor),
                    "getSharedFieldVersions");
        }

        private String sharedElementVersions(Object array, int index)
                throws Exception {
            return requiredVmJson(elementVersions.invoke(null, array, index),
                    "getSharedElementVersions");
        }

        private String eventLedger() throws Exception {
            return requiredVmJson(eventLedger.invoke(null), "getEventLedger");
        }

        private static String requiredVmJson(Object value, String api) {
            if (!(value instanceof String)
                    || ((String) value).trim().isEmpty()) {
                throw new IllegalStateException(api
                        + " returned no serialized VM evidence");
            }
            return (String) value;
        }

        private static EngineApi load() {
            Class<System> system = System.class;
            EngineApi api = new EngineApi();
            api.openWorkloadSession = method(system, "openWorkloadSession");
            api.closeWorkloadSession = method(system, "closeWorkloadSession");
            api.workloadSessionStatus =
                    method(system, "getWorkloadSessionStatus");
            api.startRegion = method(system, "startConcolicRegion",
                    String.class, String.class);
            api.currentContextId = method(system,
                    "getCurrentConcolicContextId");
            api.symbolizeWithPrefix = method(system, "symbolize",
                    Object.class, String.class);
            api.symbolizeField = method(system, "symbolizeField",
                    Object.class, String.class, String.class);
            api.symbolizeExactField = method(system, "symbolizeExactField",
                    Object.class, String.class, String.class, String.class,
                    String.class);
            api.observeExactPrimitiveField = method(system,
                    "observeExactPrimitiveField", Object.class, String.class,
                    String.class, String.class);
            api.snapshotContainer = method(system,
                    "snapshotContainerExpression", Object.class,
                    Object[].class, Object[].class, int.class);
            api.trackContainer = method(system, "trackContainerExpression",
                    Object.class, String.class);
            api.getExpression = method(system, "getSymbolicExpression",
                    Object.class);
            api.getFieldExpression = method(system,
                    "getSymbolicFieldExpression", Object.class, String.class,
                    String.class, String.class, Object.class);
            api.finishRegion = method(system, "finishConcolicRegion");
            api.getPathCondition = method(system, "getPathCondition");
            api.pausePathCondition =
                    method(system, "pauseConcolicPathCondition");
            api.resumePathCondition =
                    method(system, "resumeConcolicPathCondition");
            api.markBranch = method(system, "markConcolicBranch",
                    String.class, int.class);
            api.getBranchEvents = method(system, "getConcolicBranchEvents");
            api.cleanupEnd = method(system, "endConcolic");
            api.export = method(system, "exportExpression", Object.class,
                    String.class, String.class, String.class, long[].class);
            api.attach = method(system, "attachExpression", Object.class,
                    String.class, String.class, String.class, long.class,
                    long[].class);
            api.range = method(system, "getConcolicPathConditionRange",
                    int.class, int.class);
            api.activate = method(system, "activateConcolicEventLedger");
            api.selectField = method(system, "selectSharedFieldCarrier",
                    Object.class, String.class, String.class, String.class);
            api.selectElement = method(system, "selectSharedElementCarrier",
                    Object.class, int.class);
            api.selectMap = method(system, "selectSharedMapCarrier",
                    Object.class);
            api.fieldVersions = method(system, "getSharedFieldVersions",
                    Object.class, String.class, String.class, String.class);
            api.elementVersions = method(system, "getSharedElementVersions",
                    Object.class, int.class);
            api.mapVersions = method(system, "getSharedMapVersions",
                    Object.class);
            api.eventLedger = method(system, "getEventLedger");
            return api;
        }

        private static Method method(Class<?> owner, String name,
                                     Class<?>... parameters) {
            try {
                return owner.getMethod(name, parameters);
            } catch (NoSuchMethodException ignored) {
                return null;
            }
        }
    }

}
