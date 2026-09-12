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
import edu.uva.liftlab.graphchecker.concolic.CoverageDivergence;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.RecordedEvidenceIdentity;
import edu.uva.liftlab.graphchecker.concolic.RpcExpressionHandoff;
import edu.uva.liftlab.graphchecker.concolic.SharedStateEvidence;
import edu.uva.liftlab.graphchecker.concolic.SymbolicPropagationClosure;
import edu.uva.liftlab.graphchecker.concolic.SymbolicSourceEvidence;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionIr;
import edu.uva.liftlab.graphchecker.concolic.VmExpressionTable;
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
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.object;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.optionalString;

/**
 * Runtime bridge injected at symbolic-region roots for the second (concolic)
 * unit-test execution.
 *
 * <p>The class uses reflection for the custom {@code java.lang.System} APIs so
 * GraphChecker itself remains buildable and testable on an ordinary JDK.</p>
 */
public final class ConcolicRegionRuntime {
    private static final String MANUAL_INPUT_OBSERVATION_KIND =
            "MANUAL_SYMBOLIC_INPUT_OBSERVATION";
    private static final String MANUAL_INPUT_OBSERVATION_AUTHORITY =
            "EXACT_PLANNED_SYMBOLIZATION_ACTION_V1";
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
            new ThreadPoolExecutor(1, 1, 0L, TimeUnit.MILLISECONDS,
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
    static final String SKIP_UNAPPLIED_MODEL_ASSIGNMENT =
            "UNAPPLIED_MODEL_ASSIGNMENT";
    static final String SKIP_RESULT_PUBLICATION_FAILED =
            "RESULT_PUBLICATION_FAILED";
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
    /** One workload invocation's symbolic-propagation closure identity. */
    static final String REPLAY_GROUP_ENV =
            "CAUSYNTH_CONCOLIC_REPLAY_GROUP_ID";
    private static volatile Boolean diagnostics;
    private static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    /**
     * Selected activations on this Java thread, innermost first.
     *
     * <p>The custom VM already keeps the matching native region stack.  The
     * Java runtime must preserve that nesting as well: a selected helper can
     * execute inside a selected caller while both share the same propagated
     * expression universe and thread-local path condition.</p>
     */
    private static final ThreadLocal<Deque<Long>> CURRENT_TOKENS =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<>();
                }
            };
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
    /** Enclosing method calls that own LOOP_BODY_ROOT iteration frames. */
    private static final ThreadLocal<Deque<LoopRootInvocationContext>>
            LOOP_ROOT_INVOCATIONS =
            new ThreadLocal<Deque<LoopRootInvocationContext>>() {
                @Override
                protected Deque<LoopRootInvocationContext> initialValue() {
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
     * Content-addressed expression universe of the current VM workload
     * session.  Native expression ids are session-wide, so decoding them in
     * one store per region needlessly rebuilt the same propagated DAG at every
     * hop and every concurrent occurrence.
     */
    private static volatile VmExpressionTable.Store workloadExpressionStore =
            new VmExpressionTable.Store();
    /** Exact materialized activation owning each session VM context. */
    private static final Object CONTEXT_ACTIVATION_LOCK = new Object();
    private static final Map<Long, List<WriterActivationIdentity>>
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
                long attempted = active.loopBackedges.recordTraversal(edge);
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
        diag("REGION_CUT", cut.toString());
        finish(active.token, "CUT", "", null);
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
            workloadExpressionStore = new VmExpressionTable.Store();
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
        clearContextActivations();
        workloadExpressionStore = new VmExpressionTable.Store();
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
            workloadExpressionStore = new VmExpressionTable.Store();
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
        clearContextActivations();
        workloadSessionId = 0L;
        workloadExpressionStore = new VmExpressionTable.Store();
        return "";
    }

    private static String workloadSessionStatusName(long status) {
        if (status == 0L) return "OK";
        if (status == -1L) return "ALREADY_OPEN";
        if (status == -2L) return "NOT_OPEN";
        if (status == -3L) return "MEMBERS_REMAIN";
        if (status == -4L) return "CLOSING";
        return "UNNAMED_STATUS(" + status + ")";
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
            CONTEXT_ACTIVATIONS.computeIfAbsent(contextId,
                    ignored -> new ArrayList<>()).add(
                    new WriterActivationIdentity(active));
        }
    }

    /** Exact nested activation in one VM thread context, or null if ambiguous. */
    private static WriterActivationIdentity contextActivation(
            long contextId, long regionEnterEventId, RuntimeTask writer) {
        synchronized (CONTEXT_ACTIVATION_LOCK) {
            for (WriterActivationIdentity candidate
                    : CONTEXT_ACTIVATIONS.getOrDefault(contextId,
                    Collections.<WriterActivationIdentity>emptyList())) {
                if (candidate.regionEnterEventId == regionEnterEventId
                        && candidate.owns(writer)) {
                    return candidate;
                }
            }
            return null;
        }
    }

    /** Immutable owner of one session-global VM field-version event. */
    private static final class WriterActivationIdentity {
        private final String vmTaskId;
        private final String vmRegionId;
        private final long regionEnterEventId;
        private final String sourceKey;
        private final String occurrenceId;
        private final List<WriterCaseAddress> caseClosure;

        private WriterActivationIdentity(ActiveRegion active) {
            this.vmTaskId = active.activation.taskId;
            this.vmRegionId = active.activation.regionId;
            this.regionEnterEventId = active.vmRegionEnterEventId;
            this.sourceKey = active.activation.sourceKey;
            this.occurrenceId = active.occurrenceId();
            this.caseClosure = activeWriterCaseClosure();
        }

        private boolean owns(RuntimeTask writer) {
            return writer != null && vmTaskId.equals(writer.taskId)
                    && vmRegionId.equals(writer.regionId);
        }

        private JsonObject caseClosure() {
            JsonObject result = new JsonObject();
            result.addProperty("authority", SymbolicPropagationClosure
                    .WRITER_ACTIVATION_CLOSURE_AUTHORITY);
            result.addProperty("complete", !caseClosure.isEmpty());
            JsonArray cases = new JsonArray();
            for (WriterCaseAddress address : caseClosure) {
                cases.add(address.toJson());
            }
            result.add("cases", cases);
            return result;
        }
    }

    /** Stable dynamic addresses of the selected regions active at this write. */
    private static List<WriterCaseAddress> activeWriterCaseClosure() {
        List<WriterCaseAddress> result = new ArrayList<>();
        Set<String> occurrences = new LinkedHashSet<>();
        for (Long token : CURRENT_TOKENS.get()) {
            ActiveRegion active = ownerRegion(token);
            if (active == null || active.activationOrdinal <= 0) continue;
            WriterCaseAddress address = new WriterCaseAddress(active);
            if (occurrences.add(address.occurrenceId)) result.add(address);
        }
        return Collections.unmodifiableList(result);
    }

    /** Runtime address resolved to a local-case selector after all PCs close. */
    private static final class WriterCaseAddress {
        private final String taskId;
        private final String regionId;
        private final String occurrenceId;

        private WriterCaseAddress(ActiveRegion active) {
            this.taskId = active.activation.taskId;
            this.regionId = active.activation.regionId;
            this.occurrenceId = active.occurrenceId();
        }

        private JsonObject toJson() {
            JsonObject result = new JsonObject();
            result.addProperty("taskId", taskId);
            result.addProperty("regionId", regionId);
            result.addProperty("occurrenceId", occurrenceId);
            return result;
        }
    }

    /**
     * Admits the one planned occurrence this root invocation will execute.
     *
     * @return the started occurrence, or {@code null} when nothing was
     *         admitted or it could not be started
     */
    private static ActiveRegion admitRegion(
            Configuration config, String rootHookGroupKey,
            String rootMethod, Object receiver, Object[] rootArguments) {
        if (config.tasks.isEmpty() || rootMethod == null) {
            return null;
        }
        RuntimeTask admitted = selectTask(config, rootHookGroupKey,
                rootMethod, receiver, rootArguments);
        if (admitted == null) return null;
        if (boundedLoopOccurrenceCut(admitted)) {
            // The bounded loop's captured occurrence set is full: release the
            // candidate so the next iteration re-selects and re-caps, and run
            // this iteration concretely.
            config.releaseCandidate(admitted);
            return null;
        }
        boolean messageAddressed = inboundMessageAddressesAdmission(admitted);
        SourceRef registeredReceiverSource =
                RuntimeTraceContext.sourceFor(receiver);
        String messageSource = inboundMessageSourceEvidence(
                admitted.sourceKey, registeredReceiverSource,
                messageAddressed);
        if (messageAddressed && messageSource.isEmpty()) {
            admitted.noteUnaddressedCandidate(
                    "matching message reached a receiver belonging to "
                            + registeredReceiverSource.key() + " instead of "
                            + admitted.sourceKey);
            config.releaseCandidate(admitted);
            return null;
        }
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        boolean deferredOutgoingSource = !Configuration.sourceMismatch(
                admitted, registeredReceiverSource, context).isEmpty()
                && Configuration.mayDeferMissingContextToOutgoingAnchor(
                admitted, registeredReceiverSource, context);
        return startSymbolicRegion(admitted, receiver, messageSource,
                deferredOutgoingSource);
    }

    /** Exact message evidence survives until a selected region is started. */
    private static boolean inboundMessageAddressesAdmission(
            RuntimeTask admitted) {
        if (admitted.attachProducerOccurrenceByPort.isEmpty()) return false;
        if (!admitted.loopBodyRoot) {
            return inboundMessageAddressMatches(
                    admitted.attachProducerOccurrenceByPort,
                    admitted.occurrenceId);
        }
        // The enclosing hook checked the envelope before an attach inside the
        // method could consume it. An anchored loop task enters this set only
        // after every planned port and producer occurrence matched.
        return enclosingLoopRootAdmits(admitted);
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
                                          String rootHookGroupKey,
                                          String rootMethod,
                                          Object receiver,
                                          Object[] rootArguments) {
        beginBookkeeping();
        try {
            return config.select(rootHookGroupKey, rootMethod, receiver,
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
            String admittedMessageSource,
            boolean deferredOutgoingSource) {
        beginLiveSelectedRegion();
        EngineApi api = engine();
        boolean engineStarted = false;
        boolean pathConditionPaused = false;
        boolean javaRegionPushed = false;
        ActiveRegion active = null;
        try {
            api.start(admitted.regionId, admitted.taskId);
            engineStarted = true;
            // Region setup performs reflection, collection lookups and JSON-
            // safe bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
            ActiveRegion enclosing = activeRegion();
            active = new ActiveRegion(TOKEN_COUNTER.incrementAndGet(),
                    admitted, receiver, Thread.currentThread(),
                    deferredOutgoingSource);
            // A nested region starts with the symbolic state already carried
            // by its caller.  Its local branches must therefore open
            // immediately even when it mints no new task-local root.
            if (enclosing != null && enclosing.pathRecordingStarted) {
                active.pathRecordingStarted = true;
            }
            active.activationOrdinal = admitted.nextActivationOrdinal();
            ACTIVE.put(active.token, active);
            pushActiveRegion(active);
            javaRegionPushed = true;
            active.vmContextId = api.currentContextId();
            if (active.vmContextId <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no context id");
            }
            active.vmRegionEnterEventId = api.currentRegionEnterEventId();
            if (active.vmRegionEnterEventId <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no region-entry "
                                + "event id");
            }
            rememberContextActivation(active.vmContextId, active);
            // A delivery can establish the causal request immediately before
            // the selected handler entry.
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            SourceRef receiverSource = RuntimeTraceContext.sourceFor(receiver);
            if (receiverSource != null) {
                observeCausalSource(receiverSource.key());
            } else if (!safe(admittedMessageSource).isEmpty()) {
                // The exact incoming exchange is also the consumer
                // occurrence's address. Preserve that source on the active
                // region even when replay reconstructed no receiver alias or
                // inherited trace context; close-time confirmation then sees
                // the same evidence that admitted the region.
                observeCausalSource(admittedMessageSource);
            } else if (context.source != null
                    && RuntimeTraceContext.sameSourceIdentity(
                    admitted.sourceKey, context.source.key())) {
                observeCausalSource(context.source.key());
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
                if (javaRegionPushed) popActiveRegion(active);
                active.releaseActivationOrdinal();
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
        RuntimeTask task = active.activation;
        symbolizeReceiverFields(active, task, engine());
        selectDeclaredSharedCarriers(active, task);
    }
    /** Instrumentation-facing root entry. */
    public static long enterRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        Configuration config = configuration();
        RootHookGroup group = config.rootHookGroup(
                instrumentationSelector, rootMethod);
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        // A plan may contain several dynamic occurrences rooted at the same
        // Java method.  Instrumentation emits one hook for each plan row, but
        // one concrete method invocation is one logical activation.  The
        // first physical hook dispatches the whole group even when no task is
        // admitted; every remaining hook at that same entry is transparent.
        for (RootInvocationFrame existing : frames) {
            if (existing.claimsSiblingHook(group.key)) {
                frames.push(new RootInvocationFrame(instrumentationSelector,
                        rootMethod, group.key, 0, 0L));
                return 0L;
            }
        }
        RootInvocationFrame frame = new RootInvocationFrame(
                instrumentationSelector, rootMethod, group.key,
                Math.max(0, group.hookCount - 1), 0L);
        frames.push(frame);
        ActiveRegion active = admitRegion(config, group.key, rootMethod,
                receiver, rootArguments);
        long token = active == null ? 0L : active.token;
        frame.token = token;
        return token;
    }

    /**
     * Opens the lightweight enclosing call that addresses LOOP_BODY_ROOT
     * iterations. The outer invocation is counted once; individual body
     * entries only consult this context and never advance that address.
     */
    public static long enterLoopRootInvocationFrame(
            String instrumentationSelector, String rootMethod,
            Object receiver, Object[] rootArguments) {
        Configuration config = configuration();
        RootHookGroup group = config.loopRootHookGroup(
                instrumentationSelector, rootMethod);
        Deque<LoopRootInvocationContext> contexts =
                LOOP_ROOT_INVOCATIONS.get();
        for (LoopRootInvocationContext existing : contexts) {
            if (existing.claimsSiblingHook(group.key)) return 0L;
        }
        long token = TOKEN_COUNTER.incrementAndGet();
        Set<String> admittedTasks = config.addressLoopRootInvocation(
                group.key, rootMethod, receiver, rootArguments);
        contexts.push(new LoopRootInvocationContext(token, group.key,
                Math.max(0, group.hookCount - 1), admittedTasks));
        return token;
    }

    /** Closes one enclosing LOOP_BODY_ROOT method call. */
    public static void exitLoopRootInvocationFrame(long token) {
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

    /** Exceptional counterpart of {@link #exitLoopRootInvocationFrame}. */
    public static void throwLoopRootInvocationFrame(
            long token, Throwable throwable) {
        exitLoopRootInvocationFrame(token);
    }

    /** Whether the nearest matching outer call owns this loop task. */
    private static boolean enclosingLoopRootAdmits(RuntimeTask task) {
        if (task == null || !task.loopBodyRoot) return false;
        for (LoopRootInvocationContext context
                : LOOP_ROOT_INVOCATIONS.get()) {
            if (!context.groupKey.equals(task.loopRootHookGroupKey())) {
                continue;
            }
            return context.admittedTaskIds.contains(task.taskId);
        }
        return false;
    }

    private static boolean sameSelector(String left, String right) {
        return left == null ? right == null : left.equals(right);
    }

    private static boolean sameRootMethod(String left, String right) {
        return left == null ? right == null : left.equals(right);
    }

    /**
     * Called once per Java argument immediately after
     * {@link #enterRegionFrame}.
     */
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
        ConsumerAccessAnchor consumer = consumerAccessAnchor(active, method,
                unitIndex, occurrence, owner);
        GuardedReadAssignment guardedRead =
                active.activation.guardedReadAssignment(consumer,
                        fieldSignature);
        List<SymbolizeAction> claimed = active.activation.symbolize;
        boolean writtenInThisRegion = active.writtenFields.contains(
                owner, fieldSignature);
        if (writtenInThisRegion) {
            // The real getfield resolves the VM writer version and carries
            // its expression forward.  Never replace it with a replay-time
            // input synthesized from an output port.
            selectAccessOwnerSharedCarriers(active, owner, fieldSignature,
                    consumer);
            armGuardedRead(active, owner, guardedRead);
            return;
        }
        for (SymbolizeAction action : claimed) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName, null)
                    || !action.acceptsDirectFieldOccurrence(occurrence)) {
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
                EngineApi api = engine();
                Field exactField = declaredInstanceField(leafOwner,
                        action.exactLeafFieldSignature());
                if (exactField == null) {
                    active.addUnresolvedOnce(action.symbol
                            + ": exact field declaration is unavailable");
                    continue;
                }
                String leafFieldSignature = exactFieldSignature(exactField);
                Object value = exactField.get(leafOwner);
                boolean assignmentFailed = false;
                for (ModelAssignment assignment
                        : active.fieldAssignments(action)) {
                    if (!assignment.hasContainerTarget()) continue;
                    if (!assignment.validContainerTarget()
                            || !writeContainerTarget(value, assignment)) {
                        active.addUnresolvedOnce(action.symbol
                                + ": solver container model could not be "
                                + "materialized");
                        assignmentFailed = true;
                        break;
                    }
                    active.recordModelAssignment(assignment);
                }
                if (assignmentFailed) continue;
                JsonElement carried;
                try {
                    carried = containerValue(value)
                            ? engineExpression(api.expression(value))
                            : engineExpression(api.fieldExpression(leafOwner,
                            exactField.getDeclaringClass().getName(),
                            exactField.getName(), javaTypeDescriptor(
                            exactField.getType().getTypeName()), value));
                } catch (Throwable unsymbolized) {
                    carried = null;
                }
                // Ask before replay writes or fresh minting. A boundary that
                // already reached this field is the input authority.
                if (retainPropagatedInput(active, action, value, carried,
                        action.symbol, action.fieldPath,
                        leafFieldSignature)) {
                    continue;
                }
                // This hook executes before the original getfield. The VM
                // resolves the actual writer and creates any concurrent-read
                // boundary at that getfield, so a selected shared read can
                // only open recording and retain the carrier here.
                if (active.activation.observesSharedRead(fieldSignature)) {
                    ensurePathRecordingStarted(active);
                    if (containerValue(value)) {
                        active.recordSymbolizedInputPort(action.symbol,
                                value);
                    }
                    continue;
                }
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
                JsonElement expression;
                if (value != null && value != MissingValue.INSTANCE
                        && containerValue(value)) {
                    requireTrackedContainer(api, value, action.symbol);
                    ensurePathRecordingStarted(active);
                    active.recordSymbolizedInputPort(action.symbol, value);
                    expression = engineExpression(api.expression(value));
                } else {
                    active.addUnresolvedOnce(action.symbol
                            + ": exact input has no propagated VM expression");
                    continue;
                }
                active.recordManualSymbolization(action, action.symbol,
                        action.fieldPath, leafFieldSignature, expression,
                        true, false);
            } catch (Throwable throwable) {
                active.addUnresolvedOnce(action.symbol
                        + ": field materialization "
                        + safe(method) + "#u" + unitIndex + " failed: "
                        + rootCause(throwable));
            }
        }
        selectAccessOwnerSharedCarriers(active, owner, fieldSignature,
                consumer);
        armGuardedRead(active, owner, guardedRead);
    }

    /** Applies a model to the key used by this exact live Map.get. */
    public static void materializeAssociativeRead(Object container,
                                                  Object key) {
        ActiveRegion active = activeRegion();
        if (active == null || !(container instanceof Map<?, ?>)) return;
        beginBookkeeping();
        try {
            String inputSymbol = safe(
                    active.symbolizedInputPorts.get(container));
            if (inputSymbol.isEmpty()) return;
            int occurrence = active.associativeAccessOccurrences
                    .getOrDefault(inputSymbol, 0) + 1;
            active.associativeAccessOccurrences.put(inputSymbol, occurrence);
            ModelAssignment selected = null;
            for (ModelAssignment candidate
                    : active.activation.modelAssignments) {
                if (!candidate.dynamicAssociativeTarget()
                        || !candidate.inputSymbol.equals(inputSymbol)
                        || candidate.containerAccessOrdinal != occurrence
                        || active.appliedModelAssignments.contains(
                        candidate.key)) {
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
            if (!selected.validContainerTarget()
                    || !writeAssociativeContainerTarget(container, key,
                    selected)) {
                active.addUnresolvedOnce(inputSymbol + "#access."
                        + occurrence
                        + ": solver model could not be materialized");
                return;
            }
            active.recordModelAssignment(selected);
        } finally {
            endBookkeeping();
        }
    }

    /** Installs the selected arm at its exact consumer read. */
    private static void armGuardedRead(ActiveRegion active, Object owner,
                                       GuardedReadAssignment assignment) {
        if (assignment == null || active.armedGuardedReads.containsKey(
                assignment.readIdentity)) {
            return;
        }
        try {
            long token = engine().armSharedPrimitiveFieldRead(owner,
                    assignment.declaringClass, assignment.fieldName,
                    assignment.descriptor, assignment.valueBits);
            if (token > 0L) {
                active.armedGuardedReads.put(assignment.readIdentity, token);
            } else {
                active.addUnresolvedOnce(assignment.readIdentity
                        + ": VM rejected guarded read materialization: "
                        + token);
            }
        } catch (Throwable failure) {
            active.addUnresolvedOnce(assignment.readIdentity
                    + ": guarded read materialization failed: "
                    + rootCause(failure));
        }
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
        selectAccessOwnerSharedCarriers(active, owner, fieldSignature, null);
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
        private SourceSiteEntry(
                ConfiguredSourcePhaseContract.Occurrence phase,
                String siteId, int ordinal) {
            this.phase = phase;
            this.siteId = safe(siteId);
            this.ordinal = ordinal;
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
     *
     * <p>Called from outside this repository: the workload checkouts invoke it
     * directly from {@code org.apache.hadoop.ipc.CausynthSymbolicSource}, and
     * it is the only symbolic root of HDFS-17960.</p>
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
            boolean reused = VmExpressionIr.carriesPropagatedValue(carried);
            // The application's Map re-key reads the modeled value back
            // through this same path, so the model is written first.
            ModelAssignment assignment = reused ? null
                    : active.configuredSourceAssignment(entry.phaseId(),
                    safe(sourceId), safe(fieldSignature));
            if (assignment != null) {
                if (!writeModeledField(owner, safe(fieldSignature),
                        assignment)) {
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
            ensurePathRecordingStarted(active);
            Object value = field.get(owner);
            JsonElement expression = engineExpression(api.fieldExpression(
                    owner, declaringClass, field.getName(), descriptor,
                    value));
            active.recordConfiguredSourceMint(entry, safe(sourceId),
                    safe(fieldSignature), symbol, expression, reused);
            // Only the occurrence that minted the VM leaf owns source
            // evidence and its model assignment.  A propagated bare or
            // compound expression remains the consumer's exact input and is
            // recorded above as reuse without acquiring a second identity.
            if (!reused) {
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


    private static JsonElement engineExpression(String serialized) {
        try {
            ActiveRegion active = activeRegion();
            VmExpressionTable.Store store = active == null
                    ? workloadExpressionStore
                    : active.expressionStore;
            return store.importField(serialized, "expression");
        } catch (RuntimeException malformed) {
            return null;
        }
    }

    /** Resolves a native session DAG while retaining content sharing here. */
    private static JsonObject decodeVmEnvelope(JsonObject envelope,
                                               ActiveRegion active) {
        VmExpressionTable.Store store = active == null
                ? workloadExpressionStore
                : active.expressionStore;
        return store.importEnvelope(envelope);
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

    /** Result of one VM symbolic-expression export or attach. */
    private static final class HandoffResult {
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

        /** Named reason for a failure; empty for a successful call. */
        public String reason() {
            return RpcExpressionHandoff.reason(status);
        }

        private long handle() {
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
            String descriptor) {
        HandoffResult result;
        beginBookkeeping();
        try {
            result = exportLeaf(owner, declaringClass, fieldName, descriptor);
        } finally {
            endBookkeeping();
        }
        return result;
    }

    private static HandoffResult exportLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
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
        if (active == null) return false;
        String consumerOccurrence = active.activation
                .exportConsumerOccurrence(portId);
        boolean staged = !consumerOccurrence.isEmpty()
                && SymbolicMessageEnvelope.stage(
                portId, handle, active.activation.taskId,
                active.occurrenceId(), consumerOccurrence);
        if (staged) {
            beginBookkeeping();
            try {
                active.observeOutgoingSourceAnchor(portId);
            } finally {
                endBookkeeping();
            }
        }
        return staged;
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
        CommunicationHandoffSpec site;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, true);
        } finally {
            endBookkeeping();
        }
        if (site == null || carrier == null) return;
        HandoffResult result = exportSymbolicLeaf(carrier, CARRIER_CLASS,
                field, descriptor);
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
        ActiveRegion active = activeRegion();
        if (leafCarried && !acceptCommunicationEndpoint(active, site,
                carried.producerOccurrenceId(),
                carried.consumerOccurrenceId())) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, handle,
                    "message entry names a different planned edge: "
                            + carried.producerOccurrenceId() + " -> "
                            + carried.consumerOccurrenceId()));
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
                ? optionalLongInteger(result.record, "exportEventId", 0L) : 0L;
        if (exportEvent <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "attached leaf named no VM export event"));
            return;
        }
        // README RPC-1: the reference carries both endpoints of the edge.
        long attachEvent = result.ok()
                ? optionalLongInteger(result.record, "attachEventId", 0L) : 0L;
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
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "custom VM returned no propagated destination expression"));
            return;
        }
        acceptVmHandoffExpression(active, site, exportEvent, attachEvent,
                expression, producerTaskId, producerOccurrenceId);
    }

    /** Commits one fully validated receiver-side handoff to the active case. */
    private static void acceptVmHandoffExpression(
            ActiveRegion active, CommunicationHandoffSpec site,
            long exportEvent, long attachEvent, JsonElement expression,
            String producerTaskId, String producerOccurrenceId) {
        active.vmHandoffEvents.add(VmHandoffEvidence.event(site.portId(),
                exportEvent, attachEvent, expression, producerTaskId,
                producerOccurrenceId));
        // A VM-attached expression is an exact selected symbolic input just as
        // much as one created by a local symbolize hook.
        ensurePathRecordingStarted(active);
    }

    /** Checks that one message entry came from its planned producer. */
    private static boolean acceptCommunicationEndpoint(
            ActiveRegion active, CommunicationHandoffSpec site,
            String producerOccurrenceId, String consumerOccurrenceId) {
        String expectedProducer = active.activation
                .attachProducerOccurrence(site.portId());
        String actualProducer = PathObservation.plannedOccurrenceOf(
                producerOccurrenceId);
        String expectedConsumer = active.activation.occurrenceId;
        String actualConsumer = PathObservation.plannedOccurrenceOf(
                consumerOccurrenceId);
        if (expectedProducer.isEmpty()
                || !expectedProducer.equals(actualProducer)
                || !expectedConsumer.equals(actualConsumer)) {
            diag("ATTACH_ENDPOINT_MISMATCH", "task="
                    + safe(active.activation.taskId) + " port="
                    + site.portId() + " expected=" + expectedProducer
                    + " -> " + expectedConsumer + " actual="
                    + actualProducer + " -> " + actualConsumer);
            return false;
        }
        return true;
    }

    /**
     * Whether the current concrete message carries this exact planned edge.
     * The handle and correlation metadata are deliberately irrelevant here:
     * the envelope's port and producer occurrence are the admission address.
     */
    static boolean inboundMessageMatches(String portId,
                                         String producerOccurrenceId,
                                         String consumerOccurrenceId) {
        String expectedProducer = PathObservation.plannedOccurrenceOf(
                producerOccurrenceId);
        String expectedConsumer = PathObservation.plannedOccurrenceOf(
                consumerOccurrenceId);
        if (safe(portId).isEmpty() || expectedProducer.isEmpty()
                || expectedConsumer.isEmpty()) {
            return false;
        }
        SymbolicMessageEnvelope.Entry carried =
                SymbolicMessageEnvelope.peek(portId);
        return carried.present() && expectedProducer.equals(
                PathObservation.plannedOccurrenceOf(
                        carried.producerOccurrenceId()))
                && expectedConsumer.equals(
                PathObservation.plannedOccurrenceOf(
                        carried.consumerOccurrenceId()));
    }

    /** Whether every planner-authored input belongs to this exact message. */
    static boolean inboundMessageAddressMatches(
            Map<String, String> inboundProducers,
            String consumerOccurrenceId) {
        if (inboundProducers == null || inboundProducers.isEmpty()) {
            return false;
        }
        for (Map.Entry<String, String> anchor
                : inboundProducers.entrySet()) {
            if (!inboundMessageMatches(anchor.getKey(), anchor.getValue(),
                    consumerOccurrenceId)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Source attribution carried by an exact incoming message address.
     * An explicit receiver registration remains authoritative and may veto
     * the message; an absent receiver alias does not erase message evidence.
     */
    static String inboundMessageSourceEvidence(
            String plannedSourceKey, SourceRef registeredReceiverSource,
            boolean allPlannerAnchorsMatch) {
        String planned = safe(plannedSourceKey);
        if (!allPlannerAnchorsMatch || planned.isEmpty()
                || registeredReceiverSource != null
                && !RuntimeTraceContext.sameSourceIdentity(planned,
                registeredReceiverSource.key())) {
            return "";
        }
        return planned;
    }

    /** Communication-addressed roots ignore an unrelated local ordinal. */
    static boolean rootInvocationAddressMatches(
            Integer actualOrdinal, int plannedOrdinal,
            Map<String, String> inboundProducers,
            String consumerOccurrenceId,
            boolean exactOutgoingAddress) {
        // An exact request/OUT/consumer tuple is the occurrence address.  A
        // failed candidate may therefore release the address and let a later
        // invocation try it; the raw call count must not consume it.
        if (exactOutgoingAddress) return true;
        if (inboundProducers == null || inboundProducers.isEmpty()) {
            return actualOrdinal != null
                    && actualOrdinal.intValue() == plannedOrdinal;
        }
        return inboundMessageAddressMatches(inboundProducers,
                consumerOccurrenceId);
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
    private static final class SharedStateResult {
        private final String stage;
        private final int status;
        private final String locationKey;
        private final JsonObject record;

        private SharedStateResult(String stage, int status, String locationKey,
                                  JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.locationKey = locationKey;
            this.record = record;
        }

        private boolean ok() {
            return status == SharedStateEvidence.OK;
        }

        /** Named reason for a failure; empty for an admitted answer. */
        private String reason() {
            return SharedStateEvidence.reason(status);
        }

        @Override
        public String toString() {
            return "SharedStateResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " location=" + locationKey + "]";
        }
    }

    /**
     * Selects one instance or static field as a symbolic carrier. Later
     * writes publish candidate expressions and reads capture their bounded
     * candidate snapshot as a guarded value.
     */
    private static SharedStateResult selectSharedFieldCarrier(
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

    /** Selects one map as a symbolic carrier of its own whole state. */
    private static SharedStateResult selectSharedMapCarrier(
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
        return selectedCarrier(carrier, active == null
                ? null : active.activation, active);
    }

    /** Selects a carrier using the task that declared this exact access. */
    private static SharedStateResult selectedCarrier(
            SharedCarrier carrier, RuntimeTask locator) {
        return selectedCarrier(carrier, locator, activeRegion());
    }

    /** Selects one physical carrier while retaining its declaring task. */
    private static SharedStateResult selectCarrierForTask(
            SharedCarrier carrier, RuntimeTask task) {
        beginBookkeeping();
        try {
            return selectedCarrier(carrier, task);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult selectedCarrier(
            SharedCarrier carrier, RuntimeTask locator,
            ActiveRegion active) {
        carrier.bindPlannedReceiver(locator);
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
        // still retain the carrier so it can read the shared version snapshot.
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
                        SharedStateEvidence.OK, "", new JsonObject()),
                carrier, active);
    }

    /**
     * Raw VM read-outs already taken while closing the selected occurrence on
     * this thread, keyed by the location they answer for.
     *
     * <p>Several evidence builders may ask for the same selected carrier.</p>
     */
    private static final ThreadLocal<Map<String, String>> READ_OUT_MEMO =
            new ThreadLocal<Map<String, String>>();

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
        JsonObject envelope = decodeVmEnvelope(parsed.getAsJsonObject(),
                active);
        String fault = SharedStateEvidence.versionsFault(envelope);
        if (!fault.isEmpty()) {
            boolean unselected = SharedStateEvidence.VERSIONS_ENVELOPE_KIND
                    .equals(optionalString(envelope, "kind"))
                    && !optionalBool(envelope, "selected", false);
            int status = unselected ? SharedStateEvidence.NOT_SELECTED
                    : SharedStateEvidence
                    .expressionSerializationTruncationFault(fault)
                    ? SharedStateEvidence.EXPRESSION_SERIALIZATION_TRUNCATED
                    : SharedStateEvidence.MALFORMED_ENVELOPE;
            return failedShared(SharedStateEvidence.STAGE_VERSIONS,
                    status,
                    SharedStateEvidence.locationKey(envelope), fault);
        }
        String locationKey = SharedStateEvidence.locationKey(envelope);
        JsonObject record = SharedStateEvidence.versionsRecord(locationKey,
                envelope, identity);
        if (carrier != null) {
            // The VM addresses a location by its own session identity; the
            // slice and the composer address one by its declared Java field.
            record.add("carrier", carrier.toJson());
        }
        // Publication can run after the owner thread has left ACTIVE.
        addActivationIdentity(object(record, "envelope"), active, carrier);
        return new SharedStateResult(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.OK, locationKey, record);
    }

    /**
     * Gives every write and read in one envelope the activation address the
     * rest of the pipeline joins on.
     *
     * <p>The VM stamps writes and reads with their task, region and thread
     * context; reads additionally carry the exact region-entry event.</p>
     */
    private static void addActivationIdentity(JsonObject envelope,
                                              ActiveRegion active,
                                              SharedCarrier carrier) {
        Configuration config = configuration();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            // Wave 3 concurrency: every symbolic write of the session is a
            // version the composer may read from, so each one is addressed
            // by the write that produced it and the thread that ran it.
            RuntimeTask writer = config.taskById(
                    optionalString(version, "taskId"));
            if (writer == null) continue;
            WriterActivationIdentity exact = contextActivation(
                    optionalLongInteger(version, "writerContextId", 0L),
                    optionalLongInteger(version, "regionEnterEventId", 0L), writer);
            if (exact != null && exact.owns(writer)) {
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                        exact.sourceKey);
                version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                        exact.occurrenceId);
                version.add(SymbolicPropagationClosure
                        .WRITER_ACTIVATION_CLOSURE, exact.caseClosure());
            } else {
                // A writer without its exact region-entry binding has no
                // activation owner. Leave it unnamed rather than collapsing
                // loop activations to their common planned address.
                version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY, "");
                version.addProperty(
                        SharedStateEvidence.WRITER_OCCURRENCE_ID, "");
            }
        }
        List<JsonObject> ownedReads = new ArrayList<>();
        for (JsonElement element : array(envelope, "reads")) {
            if (element.isJsonObject()
                    && activeOwnsRead(element.getAsJsonObject(), active)) {
                ownedReads.add(element.getAsJsonObject());
            }
        }
        ownedReads.sort(Comparator.comparingLong(
                read -> optionalLongInteger(read, "readEventId", Long.MAX_VALUE)));
        if (carrier != null
                && ownedReads.size() == carrier.consumerAccesses().size()) {
            for (int index = 0; index < ownedReads.size(); index++) {
                ConsumerAccessAnchor anchor =
                        carrier.consumerAccesses().get(index);
                ownedReads.get(index).addProperty(
                        SharedStateEvidence.CONSUMER_SITE_ID, anchor.siteId);
                ownedReads.get(index).addProperty(
                        SharedStateEvidence.CONSUMER_SITE_OCCURRENCE,
                        anchor.occurrence);
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
            // A session envelope contains reads from every task that touched
            // this location.  A row may claim only the reads issued by the
            // activation currently closing: native task, context and region
            // entry together are the exact dynamic owner.
            if (!activeOwnsRead(read, active)) {
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

    /** Whether this native read belongs to the activation publishing it. */
    private static boolean activeOwnsRead(JsonObject read,
                                           ActiveRegion active) {
        if (read == null || active == null
                || active.vmRegionEnterEventId <= 0L) {
            return false;
        }
        RuntimeTask reader = active.activation;
        return active.vmContextId == optionalLongInteger(read,
                "readerContextId", 0L)
                && reader.taskId.equals(optionalString(read, "taskId"))
                && reader.regionId.equals(optionalString(read, "regionId"))
                && active.vmRegionEnterEventId == optionalLongInteger(read,
                "regionEnterEventId", 0L);
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

    /** One shared location a task asked this activation to select. */
    static final class SharedCarrierRequest {
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final String sourceKind;
        private final int index;
        private final boolean element;
        private final boolean mapState;
        /** Came from the planner's cross-region shared-state selection. */
        private final boolean plannerDeclared;
        private final List<String> fieldPath = new ArrayList<>();

        SharedCarrierRequest(JsonObject declaration,
                             boolean plannerDeclared) {
            this.declaringClass = optionalString(declaration, "declaringClass");
            this.fieldName = optionalString(declaration, "fieldName");
            this.descriptor = optionalString(declaration, "descriptor");
            this.sourceKind = optionalString(declaration, "sourceKind");
            this.index = optionalInteger(declaration, "index", -1);
            this.element = "ARRAY_ELEMENT".equals(
                    optionalString(declaration, "kind"));
            this.mapState = SharedStateEvidence.LOCATION_KIND_MAP_STATE
                    .equals(optionalString(declaration, "kind"));
            this.plannerDeclared = plannerDeclared;
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

        boolean observesSharedRead(String fieldSignature) {
            return plannerDeclared && matchesAccess(fieldSignature);
        }

        /** Activation-local identity of this exact access-bound request. */
        String accessSelectionKey(Object owner) {
            return (mapState ? "MAP" : element ? "ELEMENT" : "FIELD")
                    + "/" + System.identityHashCode(owner) + "/"
                    + declaringClass + "#" + fieldName + ":" + descriptor
                    + "@" + index;
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
                                         String fieldSignature,
                                         RuntimeTask task,
                                         ConsumerAccessAnchor consumer) {
            SharedCarrier carrier = mapState
                    ? SharedCarrier.map(
                    readExactField(owner, fieldSignature),
                    declaringClass, fieldName, descriptor)
                    : SharedCarrier.field(owner, declaringClass,
                    fieldName, descriptor);
            carrier.recordConsumerAccess(consumer);
            return selectCarrierForTask(carrier, task);
        }

        /** Selects this carrier for {@code active}, or names why it cannot. */
        SharedStateResult select(ActiveRegion active, RuntimeTask task) {
            Object owner = resolveOwner(active.receiver);
            if (owner == MissingValue.INSTANCE) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.MISSING_METADATA, "",
                        "declared carrier owner is unreachable from the "
                                + "region receiver: " + describe()), null,
                        active);
            }
            if (element) {
                return selectCarrierForTask(
                        SharedCarrier.element(owner, index), task);
            }
            if (mapState) {
                return selectCarrierForTask(SharedCarrier.map(owner,
                        declaringClass, fieldName, descriptor), task);
            }
            return selectCarrierForTask(SharedCarrier.field(owner,
                    declaringClass, fieldName, descriptor), task);
        }
    }

    /** Selects every carrier this activation's task declared. */
    private static void selectDeclaredSharedCarriers(ActiveRegion active,
                                                    RuntimeTask task) {
        for (SharedCarrierRequest request : task.sharedCarriers) {
            // This binding is resolved by the exact instrumented field access,
            // where the actual declaring object is available.
            if (request.accessOwnerBound()) continue;
            try {
                request.select(active, task);
            } catch (Throwable throwable) {
                recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        request.describe() + ": " + rootCause(throwable)),
                        null, active);
            }
        }
    }

    /**
     * Stable identity of the getfield this hook immediately precedes.
     * Accessor implementations use the caller site which selected the
     * receiver; direct reads use their own bytecode site.
     */
    private static ConsumerAccessAnchor consumerAccessAnchor(
            ActiveRegion active, String method, int unitIndex,
            int occurrence, Object owner) {
        AccessorCallContext accessor = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (accessor != null && active != null
                && accessor.regionToken == active.token
                && accessor.thread == Thread.currentThread()
                && accessor.receiver == owner
                && !accessor.callSiteId.isEmpty()
                && accessor.occurrence > 0) {
            return new ConsumerAccessAnchor(accessor.callSiteId,
                    accessor.occurrence);
        }
        if (safe(method).isEmpty() || unitIndex < 0 || occurrence < 1) {
            return null;
        }
        return new ConsumerAccessAnchor(siteId(method, unitIndex),
                occurrence);
    }

    /** Selects a demanded carrier on its exact field-access owner once. */
    private static void selectAccessOwnerSharedCarriers(
            ActiveRegion active, Object owner, String fieldSignature,
            ConsumerAccessAnchor consumer) {
        selectAccessOwnerSharedCarriers(active, active.activation, owner,
                fieldSignature, consumer);
    }

    /** Selects one task's access-owner carriers for this activation. */
    private static void selectAccessOwnerSharedCarriers(
            ActiveRegion active, RuntimeTask task, Object owner,
            String fieldSignature, ConsumerAccessAnchor consumer) {
        Set<String> visited = new LinkedHashSet<>();
        for (SharedCarrierRequest request : task.sharedCarriers) {
            if (!request.matchesAccess(fieldSignature)) continue;
            String selectionKey = request.accessSelectionKey(owner);
            if (!visited.add(selectionKey)) {
                continue;
            }
            SharedCarrier held = active.sharedCarriers.get(selectionKey);
            if (held != null) {
                held.recordConsumerAccess(consumer);
                continue;
            }
            try {
                request.selectAtAccess(owner, fieldSignature, task,
                        consumer);
            } catch (Throwable throwable) {
                recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        request.describe() + ": " + rootCause(throwable)),
                        null, active);
            }
        }
    }

    /** One stable region-local consumer access, independent of object ids. */
    private static final class ConsumerAccessAnchor {
        private final String siteId;
        private final int occurrence;

        private ConsumerAccessAnchor(String siteId, int occurrence) {
            this.siteId = safe(siteId);
            this.occurrence = occurrence;
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
        /** Reads of this live carrier in the publishing activation. */
        private final List<ConsumerAccessAnchor> consumerAccesses =
                new ArrayList<>();

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
            if (!requiresPlannedReceiver()) {
                return;
            }
            bindPlannedReceiver(task == null ? 0L
                    : task.plannedReceiverObjectId(
                    declaringClass, fieldName));
        }

        void bindPlannedReceiver(long receiverObjectId) {
            plannedReceiverObjectId = Math.max(0L, receiverObjectId);
        }

        boolean requiresPlannedReceiver() {
            return !SHAPE_ELEMENT.equals(shape)
                    && !declaringClass.isEmpty() && !fieldName.isEmpty();
        }

        long plannedReceiverObjectId() {
            return plannedReceiverObjectId;
        }

        void recordConsumerAccess(ConsumerAccessAnchor consumer) {
            if (consumer != null && SHAPE_FIELD.equals(shape)
                    && !consumer.siteId.isEmpty()
                    && consumer.occurrence > 0) {
                consumerAccesses.add(consumer);
            }
        }

        List<ConsumerAccessAnchor> consumerAccesses() {
            return consumerAccesses;
        }

        String describe() {
            return shape + " " + declaringClass + "#" + fieldName + ":"
                    + descriptor;
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
        return new SharedStateResult(stage, status, safe(locationKey),
                SharedStateEvidence.gap(stage, status,
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
            carrier.bindPlannedReceiver(active.activation);
            // A map-state expression itself needs one stable map identity.
            // Scalar field reads instead carry a stable consumer-site anchor
            // on each read, so a loop-created receiver need not have one
            // trace-wide object id before its exact VM versions are read.
            if (carrier.mapState()
                    && carrier.plannedReceiverObjectId() <= 0L) {
                carriers.add(RawSharedCarrierReadOut.failure(carrier,
                        failedShared(SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.MISSING_METADATA, "",
                                "selected task has no unique frozen receiver"
                                        + " locator for "
                                        + carrier.describe())));
                continue;
            }
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

        return new RawSharedStateReadOut(carriers, identity);
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
        private final RecordedEvidenceIdentity identity;

        private RawSharedStateReadOut(
                List<RawSharedCarrierReadOut> carriers,
                RecordedEvidenceIdentity identity) {
            this.carriers = carriers;
            this.identity = identity;
        }
    }

    /**
     * Invocation-exact normal cleanup used by injected roots.  This method is
     * intentionally no-throw: instrumentation bookkeeping must never turn a
     * normal program return into an exception (or let the synthetic catch-all
     * pop an enclosing frame a second time).
     */
    public static void exitRegionFrame(String instrumentationSelector,
                                       String rootMethod) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    instrumentationSelector, rootMethod);
            if (frame != null && frame.token != 0L) {
                finish(frame.token, "NORMAL", "", null);
            }
        } catch (Throwable ignored) {
            // Runtime observation is fail-closed and cannot alter the return.
        }
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
                    finish(frame.token, "CUT", "", throwable);
                } else {
                    finish(frame.token, "THROW",
                            throwable == null ? ""
                                    : throwable.getClass().getName(),
                            throwable);
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
        private final String rootHookGroupKey;
        private int remainingSiblingHooks;
        private long token;

        private RootInvocationFrame(String instrumentationSelector,
                                    String rootMethod, String rootHookGroupKey,
                                    int remainingSiblingHooks,
                                    long token) {
            this.instrumentationSelector = instrumentationSelector;
            this.rootMethod = rootMethod;
            this.rootHookGroupKey = safe(rootHookGroupKey);
            this.remainingSiblingHooks = remainingSiblingHooks;
            this.token = token;
        }

        private boolean claimsSiblingHook(String actualGroupKey) {
            if (remainingSiblingHooks <= 0
                    || !rootHookGroupKey.equals(safe(actualGroupKey))) {
                return false;
            }
            remainingSiblingHooks--;
            return true;
        }
    }

    /** Static hook group that instrumentation placed at one Java entry. */
    private static final class RootHookGroup {
        private final String key;
        private final int hookCount;

        private RootHookGroup(String key, int hookCount) {
            this.key = safe(key);
            this.hookCount = Math.max(1, hookCount);
        }
    }

    /** One real enclosing method invocation for bounded body activations. */
    private static final class LoopRootInvocationContext {
        private final long token;
        private final String groupKey;
        private int remainingSiblingHooks;
        private final Set<String> admittedTaskIds;

        private LoopRootInvocationContext(
                long token, String groupKey, int remainingSiblingHooks,
                Set<String> admittedTaskIds) {
            this.token = token;
            this.groupKey = safe(groupKey);
            this.remainingSiblingHooks = remainingSiblingHooks;
            this.admittedTaskIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(admittedTaskIds));
        }

        private boolean claimsSiblingHook(String actualGroupKey) {
            if (remainingSiblingHooks <= 0
                    || !groupKey.equals(safe(actualGroupKey))) {
                return false;
            }
            remainingSiblingHooks--;
            return true;
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
                    expression);
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
        boolean declared = active.activation.declaresBranch(branchSite);
        boolean replayBoundary = active.activation
                .observesReplayBoundary(branchSite);
        if (!declared && !replayBoundary) {
            active.takePreparedBranch(preparedHandle);
            return observedOutcome;
        }
        if (!declared) {
            PreparedBranch prepared = active.takePreparedBranch(
                    preparedHandle);
            int occurrence;
            if (!active.pathRecordingStarted) {
                occurrence = active.nextBranchOccurrence(branchSite);
            } else if (prepared != null && prepared.matches(method,
                    unitIndex, expression)) {
                occurrence = prepared.occurrence;
            } else {
                active.addUnresolvedOnce("missing or mismatched replay loop "
                        + "boundary " + preparedHandle + " for "
                        + branchSite);
                return observedOutcome;
            }
            ExactConcreteBranchObservation observation =
                    active.recordReplayBoundary(method, unitIndex,
                            occurrence, observedOutcome);
            if (observation != null) {
                active.observeReplayBranch(branchSite, occurrence,
                        observedOutcome);
            }
            if (active.replayPrefixContradicted()) {
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                        null);
            }
            return observedOutcome;
        }
        if (!active.pathRecordingStarted) {
            ExactConcreteBranchObservation observation =
                    active.recordConcreteBranch(method, unitIndex,
                            observedOutcome);
            if (observation != null) {
                active.observeReplayBranch(observation.siteId(),
                        observation.occurrence(), observedOutcome);
                if (active.replayPrefixContradicted()) {
                    finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                            null);
                }
            }
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
            RecordedBranch recorded = recordBranchPaused(active, api, method,
                    unitIndex, expression, prepared.occurrence,
                    observedOutcome, vmEventId);
            boolean replayTargetMatched = active.observeReplayBranch(
                    siteId(method, unitIndex), prepared.occurrence,
                    observedOutcome, recorded.symbolicSupportDigest);
            replayContradicted = active.replayPrefixContradicted();
            if (recorded.solverWitness && replayTargetMatched
                    && !active.activation.targetBranchSite.isEmpty()
                    && active.activation.targetBranchSite.equals(
                    siteId(method, unitIndex))
                    && (active.activation.replayContract != null
                    || active.activation.targetBranchOccurrence
                    == prepared.occurrence)) {
                // Reaching the target is a fact of this case, never a reason
                // to stop recording it: the RPC, state and throw effects the
                // occurrence still owes all happen after this branch.
                // targetReach is the planner's semantic source address.  The
                // branch mapping beside it retains the actual occurrence and
                // symbolic support which matched that source after a bounded
                // loop permutation.
                active.recordTargetReach(
                        active.activation.replayContract == null
                                ? siteId(method, unitIndex)
                                : active.activation.targetBranchSite,
                        active.activation.replayContract == null
                                ? prepared.occurrence
                                : active.activation.targetBranchOccurrence,
                        observedOutcome);
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
        boolean declared = active.activation.declaresBranch(branchSite);
        boolean replayBoundary = active.activation
                .observesReplayBoundary(branchSite);
        if (!declared && !replayBoundary) {
            active.takePreparedBranch(preparedHandle);
            return observedSuccessorIndex;
        }
        if (!declared) {
            PreparedBranch prepared = active.takePreparedBranch(
                    preparedHandle);
            int occurrence;
            if (!active.pathRecordingStarted) {
                occurrence = active.nextBranchOccurrence(branchSite);
            } else if (prepared != null && prepared.matches(method,
                    unitIndex, expression)) {
                occurrence = prepared.occurrence;
            } else {
                active.addUnresolvedOnce("missing or mismatched replay loop "
                        + "switch boundary " + preparedHandle + " for "
                        + branchSite);
                return observedSuccessorIndex;
            }
            ExactConcreteBranchObservation observation =
                    active.recordReplaySwitchBoundary(method, unitIndex,
                            occurrence, expected);
            if (observation != null) {
                active.observeReplaySwitch(branchSite, occurrence, expected);
            }
            if (active.replayPrefixContradicted()) {
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                        null);
            }
            return observedSuccessorIndex;
        }
        if (!active.pathRecordingStarted) {
            ExactConcreteBranchObservation observation =
                    active.recordConcreteSwitchBranch(method, unitIndex,
                            expected);
            if (observation != null) {
                active.observeReplaySwitch(observation.siteId(),
                        observation.occurrence(), expected);
                if (active.replayPrefixContradicted()) {
                    finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "",
                            null);
                }
            }
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
        boolean replayContradicted = false;
        try {
            api.pausePathCondition();
            paused = true;
            boolean attested = recordSwitchBranchPaused(active, api, method,
                    unitIndex,
                    expression, prepared.occurrence, expected, vmEventId);
            active.observeReplaySwitch(branchSite, prepared.occurrence,
                    expected);
            replayContradicted = active.replayPrefixContradicted();
            if (attested
                    && active.activation.targetBranchSite.equals(branchSite)
                    && active.activation.targetBranchOccurrence
                    == prepared.occurrence) {
                active.recordTargetReach(branchSite, prepared.occurrence,
                        expected.caseArm());
            }
            return observedSuccessorIndex;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("switch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedSuccessorIndex;
        } finally {
            if (paused) resumePathCondition(active, api);
            if (replayContradicted) {
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    private static RecordedBranch recordBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, boolean observedOutcome,
            long vmEventId) throws Exception {
        if (vmEventId <= 0L) {
            // The VM emitted no symbolic branch event.
            return RecordedBranch.NONE;
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
            PathConditionRead read = readPathConditionRange(active, api,
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
        String symbolicSupportDigest = "";
        if (conditionIndex >= 0) {
            JsonElement condition = conditions.get(conditionIndex);
            JsonElement semanticCondition = semanticBranchCondition(
                    expression, observedOutcome, condition);
            String rawOperator = binaryOperator(condition);
            String semanticOperator = binaryOperator(semanticCondition);
            if (vmAttestation.valid) {
                symbolicSupportDigest =
                        BranchPredicateAlgebra.symbolicSupportDigest(
                                semanticCondition);
                JsonObject metadata = new JsonObject();
                metadata.addProperty("predicateNormalization",
                        safe(rawOperator).equals(safe(semanticOperator))
                                ? BranchWitness.IDENTITY_NORMALIZATION
                                : BranchWitness.CMP_NORMALIZATION);
                BranchWitness witness = BranchWitness.vmPcImmutable(siteId,
                        safe(method), unitIndex, occurrence,
                        observedOutcome, semanticCondition, conditionIndex,
                        metadata);
                mapping.add("witness", witness.toImmutableJsonView());
            }
        } else if (vmAttestation.valid
                && vmAttestation.conditionIndices.isEmpty()) {
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attested(siteId,
                            safe(method), unitIndex, occurrence,
                            observedOutcome).toJson());
        }
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
        return new RecordedBranch(vmAttestation.valid && conditionIndex >= 0,
                symbolicSupportDigest);
    }

    /** Result of one exact binary-branch capture used by replay matching. */
    private static final class RecordedBranch {
        private static final RecordedBranch NONE =
                new RecordedBranch(false, "");
        private final boolean solverWitness;
        private final String symbolicSupportDigest;

        private RecordedBranch(boolean solverWitness,
                               String symbolicSupportDigest) {
            this.solverWitness = solverWitness;
            this.symbolicSupportDigest = safe(symbolicSupportDigest);
        }
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
            ActiveRegion active, EngineApi api, int start, int end)
            throws Exception {
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
                PathConditionElements.window(windowed, start,
                        active.expressionStore);
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
            if (optionalLongInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) return null;
        JsonArray raw = array(selected, "conditionIndices");
        if (optionalInteger(selected, "conditionCount", -1) != raw.size()) {
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

    private static boolean recordSwitchBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        String siteId = safe(method) + "#u" + unitIndex;
        int baseline = active.lastPathConditionSize;
        JsonElement events = parseJson(api.branchEvents());
        List<Integer> eventConditionIndices =
                vmEventConditionIndices(events, vmEventId);
        boolean noVmCondition = eventConditionIndices != null
                && eventConditionIndices.isEmpty();
        PathConditionRead read;
        if (noVmCondition) {
            read = new PathConditionRead(PathConditionElements.EMPTY, 0,
                    "CONDITIONLESS_EVENT");
        } else if (contiguousConditionIndices(eventConditionIndices)) {
            int firstCondition = eventConditionIndices.get(0);
            int lastCondition = eventConditionIndices.get(
                    eventConditionIndices.size() - 1);
            read = readPathConditionRange(active, api, firstCondition,
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
                occurrence, conditions, noVmCondition ? 0 : baseline,
                expected, events);
        List<Integer> conditionIndices = attestation.valid
                ? attestation.conditionIndices
                : Collections.<Integer>emptyList();
        int mappingBaseline = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(0);
        int mappingLimit = conditionIndices.isEmpty()
                ? baseline : conditionIndices.get(
                conditionIndices.size() - 1) + 1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence);
        mapping.addProperty("rawPathConditionSize", mappingLimit);
        mapping.addProperty("rawPathConditionBaseline", mappingBaseline);
        if (!attestation.valid) {
            active.addUnresolvedOnce(siteId
                    + ": exact switch event attestation failed: "
                    + attestation.error);
        } else {
            // The source-level successor is the replay authority.  Its VM
            // predicates below constrain this path but are never Boolean flip
            // sources of their own.
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attestedSwitch(siteId,
                            safe(method), unitIndex, occurrence,
                            expected.branchKind, expected.caseKeys,
                            expected.observedSuccessorIndex).toJson());
        }
        active.branchMappings.add(mapping);
        if (attestation.valid) {
            int decisionOrdinal = 1;
            for (Integer conditionIndex : conditionIndices) {
                JsonObject predicate = branchMapping(method, unitIndex,
                        occurrence);
                predicate.addProperty("rawPathConditionSize", mappingLimit);
                predicate.addProperty("rawPathConditionBaseline",
                        mappingBaseline);
                predicate.add("witness",
                        BranchWitness.pcPredicateImmutable(siteId,
                                safe(method), unitIndex, occurrence,
                                decisionOrdinal++,
                                conditions.get(conditionIndex),
                                conditionIndex).toImmutableJsonView());
                active.branchMappings.add(predicate);
            }
        }
        if (!conditionIndices.isEmpty()
                && "EXPLORE".equals(active.activation.policy(siteId))) {
            active.addBranchCoverageGap(CoverageDivergence.of(
                    CoverageDivergence.Kind.FLOW,
                    "MULTIWAY_SWITCH_SUCCESSOR_ENUMERATION_UNSUPPORTED",
                    siteId + '#' + occurrence,
                    "observed successor "
                            + expected.observedSuccessorIndex
                            + " is retained as a path assumption"));
        }
        active.lastPathConditionSize = Math.max(
                active.lastPathConditionSize, mappingLimit);
        return attestation.valid;
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
        if (optionalInteger(envelope, "schemaVersion", -1) != 1
                || !"CONCOLIC_THREAD_BRANCH_EVENTS".equals(
                optionalString(envelope, "kind"))
                || !optionalBool(envelope, "active", false)) {
            return VmBranchEventAttestation.invalid(
                    "unexpected or inactive event stream");
        }
        long envelopeContext = optionalLongInteger(envelope, "contextId", 0L);
        long envelopeOwner = optionalLongInteger(envelope,
                "ownerJavaThreadId", 0L);
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
                optionalString(envelope, "regionId"))
                || !safe(active.activation.taskId).equals(
                optionalString(envelope, "taskId"))) {
            return VmBranchEventAttestation.invalid(
                    "event stream region/task does not match owner");
        }

        JsonObject selected = null;
        int matches = 0;
        for (JsonElement candidate : array(envelope, "events")) {
            if (!candidate.isJsonObject()) continue;
            JsonObject event = candidate.getAsJsonObject();
            if (optionalLongInteger(event, "eventId", -1L) == eventId) {
                selected = event;
                matches++;
            }
        }
        if (matches != 1 || selected == null) {
            return VmBranchEventAttestation.invalid(
                    "event id " + eventId + " matched " + matches
                            + " records");
        }
        String authority = optionalString(selected, "authority");
        if (!"VM_THREAD_CONTEXT_EXACT_BRANCH_EVENT_V1".equals(authority)) {
            return VmBranchEventAttestation.invalid(
                    "unsupported event authority " + authority);
        }
        if (!safe(siteId).equals(optionalString(selected, "siteId"))
                || optionalInteger(selected, "occurrence", -1) != occurrence) {
            return VmBranchEventAttestation.invalid(
                    "event site/occurrence does not match prepared branch");
        }
        if (optionalBool(selected, "outcome", !observedOutcome)
                != observedOutcome) {
            return VmBranchEventAttestation.invalid(
                    "event outcome differs from observed branch");
        }
        JsonArray indices = array(selected, "conditionIndices");
        if (optionalInteger(selected, "conditionCount", -1) != indices.size()) {
            return VmBranchEventAttestation.invalid(
                    "event condition count differs from its index vector");
        }
        if (switchExpectation != null) {
            return attestVmSwitchConditions(selected,
                    switchExpectation, indices, conditions);
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
            JsonArray rawIndices, PathConditionElements conditions) {
        int expectedOpcode = "TABLE_SWITCH".equals(expected.branchKind)
                ? 170 : 171;
        if (optionalInteger(event, "opcode", -1) != expectedOpcode) {
            return VmBranchEventAttestation.invalid(
                    "event opcode does not match static "
                            + expected.branchKind);
        }
        if (optionalString(event, "codePosition").isEmpty()) {
            return VmBranchEventAttestation.invalid(
                    "switch event has no bytecode position");
        }

        int completeSymbolicCount = expected.caseArm()
                ? 1 : expected.caseKeys.size();
        // The VM still emits an exact event when the selector is concrete.
        if (rawIndices.size() == 0) {
            return VmBranchEventAttestation.valid(
                    Collections.<Integer>emptyList());
        }
        if (rawIndices.size() != completeSymbolicCount) {
            return VmBranchEventAttestation.invalid(
                    "switch arm owns " + rawIndices.size()
                            + " conditions; exact arm requires "
                            + completeSymbolicCount);
        }
        List<Integer> indices = new ArrayList<>();
        String selector = "";
        String expectedPosition = optionalString(event, "codePosition");
        int previousIndex = -1;
        for (int offset = 0; offset < rawIndices.size(); offset++) {
            final int conditionIndex;
            try {
                conditionIndex = rawIndices.get(offset).getAsInt();
            } catch (RuntimeException malformed) {
                return VmBranchEventAttestation.invalid(
                        "switch condition index is not an integer");
            }
            if (conditionIndex < 0
                    || offset > 0 && conditionIndex != previousIndex + 1) {
                return VmBranchEventAttestation.invalid(
                        "switch condition indices are not one exact ordered "
                                + "VM event range");
            }
            final JsonElement condition;
            try {
                condition = conditions.get(conditionIndex);
            } catch (IndexOutOfBoundsException unavailable) {
                return VmBranchEventAttestation.invalid(
                        "switch condition index " + conditionIndex
                                + " is outside the exact VM event range");
            }
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
                    ? optionalString(condition.getAsJsonObject(), "_code_position")
                    : "";
            if (!conditionPosition.isEmpty()
                    && !expectedPosition.equals(conditionPosition)) {
                return VmBranchEventAttestation.invalid(
                        "switch condition bytecode position differs from "
                                + "its exact event");
            }
            indices.add(conditionIndex);
            previousIndex = conditionIndex;
        }
        return VmBranchEventAttestation.valid(indices);
    }

    private static String switchSelectorIfMatches(
            JsonElement condition, String expectedOperator, int expectedKey) {
        if (condition == null || !condition.isJsonObject()) return "";
        JsonObject object = condition.getAsJsonObject();
        if (!"BinaryExpression".equals(optionalString(object, "_type"))
                || !expectedOperator.equals(optionalString(object, "_op"))) {
            return "";
        }
        JsonElement left = object.get("_left");
        JsonElement right = object.get("_right");
        if (left == null || !left.isJsonObject()
                || right == null || !right.isJsonObject()
                || "ConstExpr".equals(optionalString(left.getAsJsonObject(),
                "_type"))) {
            return "";
        }
        JsonObject constant = right.getAsJsonObject();
        if (!"ConstExpr".equals(optionalString(constant, "_type"))) return "";
        Matcher encoded = Pattern.compile("^Y_I_(-?(?:0|[1-9][0-9]*))$")
                .matcher(optionalString(constant, "_exp"));
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
        active.terminalGap = true;
        endLiveSelectedRegion();
        writeSkipped(active.activation, skipKind, reason, null);
    }

    /** Ends whichever selected occurrence owns {@code token}. */
    private static void finish(long token, String exitKind,
                               String exceptionType, Throwable throwable) {
        ActiveRegion active = ownerRegion(token);
        if (active == null) return;
        finishOccurrence(active, exitKind, exceptionType, throwable);
    }

    private static void finishOccurrence(ActiveRegion active, String exitKind,
                                         String exceptionType,
                                         Throwable throwable) {
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
                        + " exit=" + safe(exitKind));
                active.exitKind = safe(exitKind);
                active.exceptionType = safe(exceptionType);
                active.exitThrowable = throwable;
                judgeFinishedOccurrence(active);
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
     * Applies the admission gates a finished occurrence must pass before its
     * relation may be built.
     */
    private static void judgeFinishedOccurrence(ActiveRegion active) {
        if (!active.outgoingSourceConfirmed()) {
            active.activation.noteUnaddressedCandidate(
                    "provisional producer reached no complete exact outgoing "
                            + "anchor "
                            + active.activation.deferredOutgoingSourcePorts);
            active.releaseActivationOrdinal();
            active.abandoned = true;
            endLiveSelectedRegion();
            return;
        }
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
        // The source/address gate has now answered this planned occurrence.
        // A later prefix or materialization rejection owns the sole durable
        // diagnostic; do not also report the same activation as an unmatched
        // occurrence when the workload terminates.
        configuration().markOccurrenceClaimed(active.activation);
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
        // Replay progress is frozen at this terminal.
        if (active.activation.replayContract != null) {
            if (!active.replayProgress.complete()) {
                abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                        "no compatible activation matched replay prefix: "
                                + active.replayProgress.failure());
                return;
            }
        }
        List<String> unapplied = new ArrayList<>();
        for (ModelAssignment assignment
                : active.activation.modelAssignments) {
            if (!active.appliedModelAssignments.contains(assignment.key)) {
                unapplied.add(assignment.key);
            }
        }
        if (!unapplied.isEmpty()) {
            // Every linked member owns its explicit source assignments.  A
            // companion has no branch replay contract, but allowing it to
            // publish before applying these rows would silently leave an
            // upstream root concrete.
            abandonOccurrence(active, SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                    "terminal reached with unapplied model assignment keys "
                            + unapplied);
            return;
        }
        List<String> unappliedReads = new ArrayList<>();
        for (GuardedReadAssignment assignment
                : active.activation.guardedReadAssignments) {
            if (active.materializedGuardedReads.contains(
                    assignment.readIdentity)) {
                continue;
            }
            Long token = active.armedGuardedReads.get(
                    assignment.readIdentity);
            if (token == null) {
                unappliedReads.add(assignment.readIdentity + ":NOT_ARMED");
                continue;
            }
            try {
                long status = engine().confirmSharedPrimitiveFieldRead(token);
                if (status > 0L) {
                    active.materializedGuardedReads.add(
                            assignment.readIdentity);
                } else {
                    unappliedReads.add(assignment.readIdentity
                            + ":NOT_CONSUMED(" + status + ")");
                }
            } catch (Throwable failure) {
                unappliedReads.add(assignment.readIdentity
                        + ":CONFIRM_FAILED(" + rootCause(failure) + ")");
            }
        }
        if (!unappliedReads.isEmpty()) {
            abandonOccurrence(active, SKIP_UNAPPLIED_MODEL_ASSIGNMENT,
                    "terminal reached with unapplied guarded read "
                            + "assignments " + unappliedReads);
            return;
        }
        if (active.activation.replayContract != null) {
            return;
        }
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
        boolean hasEnclosingRegion = hasEnclosingActiveRegion(active);
        ActiveRegion enclosingRegion = hasEnclosingRegion
                ? enclosingActiveRegion(active) : null;
        EngineApi api = engine();
        boolean engineFinished = false;
        boolean pathConditionPaused = false;
        String rawEngineSummary = null;
        RawSharedStateReadOut rawSharedState = null;
        JsonObject result = null;
        try {
            // Everything below is observational bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
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
            // Symbolic state created or attached in a nested region remains
            // on the VM values returned to its caller.  The native thread PC
            // gate remains admitted as well, so open the caller's Java branch
            // gate before its next selected conditional executes.
            if (enclosingRegion != null && active.pathRecordingStarted) {
                enclosingRegion.pathRecordingStarted = true;
            }
            // Finishing an inner native region pops only that region.  Its
            // caller continues in the same thread context, so undo the pause
            // that protected this read-out before returning to application
            // code.  An outermost finish detached the context and needs no
            // balancing call.
            if (hasEnclosingRegion) {
                api.resumePathCondition();
                pathConditionPaused = false;
            }
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
            if (pathConditionPaused && hasEnclosingRegion) {
                try {
                    api.resumePathCondition();
                    pathConditionPaused = false;
                } catch (Throwable ignored) {
                    // A failed native close below is still popped explicitly.
                }
            }
            if (!engineFinished) {
                // A failing native finish used to be able to throw after it
                // had already popped this region.  Never let recovery pop an
                // enclosing activation: cleanup belongs only to the exact VM
                // occurrence Java is closing.
                try {
                    if (api.currentRegionEnterEventId()
                            == active.vmRegionEnterEventId) {
                        api.cleanupAfterFailure();
                    }
                } catch (Throwable ignored) {
                    // Without an exact owner identity, destructive recovery
                    // would be less safe than letting this run terminate.
                }
            }
            ACTIVE.remove(active.token, active);
            popActiveRegion(active);
            if (!active.abandoned) endLiveSelectedRegion();
        }
        if (result == null) {
            configuration().releaseCandidate(active.activation);
            if (active.terminalGap && !active.activation.loopBodyRoot) {
                active.activation.reserveCompletedEvidence(false);
                haltWhenCampaignSettled(active.activation.taskId, 2);
            }
            return false;
        }
        if (!result.has("event")) {
            addResultIdentity(result, active, active.exitKind,
                    active.exceptionType);
        }
        return submitCompletedResultPublication(active, result,
                rawEngineSummary, rawSharedState);
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
                targetReachedByActivation(active));
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
            assembleRecordedSharedState(active, rawSharedState);
            addRecordedSharedStateToResult(result, active,
                    rawSharedState == null ? evidenceIdentity(active)
                            : rawSharedState.identity);
            JsonObject portableResult = active.expressionStore.compact(result);
            boolean written = appendResult(portableResult, rawEngineSummary);
            boolean goalAnswered = written
                    && resultAnswersSelectedGoal(active.activation, result);
            if (goalAnswered) {
                configuration().markOccurrenceClaimed(active.activation);
            }
            // A compatible root is only a candidate for an occurrence address.
            // Keep admitting candidates until the selected target is reached.
            if (!written || goalAnswered) {
                haltWhenCampaignSettled(active.activation.taskId,
                        written ? 0 : 2);
            }
        } catch (Throwable failure) {
            // Admission was already reopened after the VM raw read-out.  A
            // failure is terminal because a later activation may have used
            // the reserved loop phase; silently rolling back would make its
            // identity false.
            diagAfterVmClose("RESULT_PUBLICATION_FAILED",
                    rootCause(failure));
            configuration().markOccurrenceClaimed(active.activation);
            try {
                writeSkipped(active.activation,
                        SKIP_RESULT_PUBLICATION_FAILED,
                        "completed VM occurrence could not be published: "
                                + rootCause(failure), null);
            } catch (Throwable reportingFailure) {
                diagAfterVmClose("RESULT_PUBLICATION_FAILURE_REPORT_FAILED",
                        rootCause(reportingFailure));
            } finally {
                haltWhenCampaignSettled(active.activation.taskId, 2);
            }
        } finally {
            endSelectedResultPublication();
        }
    }

    /** Builds one occurrence result before the VM summary is spliced in. */
    private static void buildCompletedResult(
            JsonObject result, ActiveRegion active,
            RecordedEvidenceIdentity identity) {
        String exitKind = active.exitKind;
        // A loop-bound cut is itself the terminal of the bounded local path.
        boolean boundedPathExit = "CUT".equals(exitKind)
                && active.loopBoundCut != null
                && active.replayResourceCut == null;
        String completedExitKind = boundedPathExit
                ? "BOUNDED" : exitKind;
        if (!active.activation.symbolize.isEmpty()
                && !active.pathRecordingStarted) {
            active.addUnresolvedOnce("NO_SELECTED_INPUT_MATERIALIZED");
        }
        populateCompletedResult(result, active, completedExitKind,
                active.exceptionType, active.exitThrowable, identity);
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
     * The activation's exact configured-source and planned-action
     * observations, one runtime hook result per row.
     */
    private static JsonArray symbolizedInputs(ActiveRegion active) {
        return sharedRows(active.symbolizedRows);
    }

    /** One array shell over immutable evidence rows and expression DAGs. */
    private static JsonArray sharedRows(Collection<JsonObject> source) {
        JsonArray rows = new JsonArray();
        if (source != null) {
            for (JsonObject row : source) rows.add(row);
        }
        return rows;
    }

    /** Copies {@code rows} with the identity stamp applied to each. */
    private static JsonArray stamped(List<JsonObject> rows,
                                     RecordedEvidenceIdentity identity) {
        JsonArray stamped = new JsonArray();
        for (JsonObject row : rows) {
            JsonObject copy = shallowCopy(row);
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
            String exceptionType, Throwable throwable,
            RecordedEvidenceIdentity identity) {
        active.nameUnreachedTargetBranch();
        addResultIdentity(result, active, exitKind, exceptionType);
        if (throwable != null && !"CUT".equals(exitKind)) {
            result.add("exceptionChain", exceptionChain(throwable));
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
                    sharedRows(active.loopCardinalities));
        }
        if (!active.loopCardinalityGaps.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITY_GAPS,
                    sharedRows(active.loopCardinalityGaps));
        }
        if (active.targetReach != null) {
            result.add("targetReach", active.targetReach);
        }
        result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
        result.add("symbolizedInputs", symbolizedInputs(active));
        SymbolicSourceEvidence.writeTo(result,
                new ArrayList<>(active.symbolicSources.values()));
        if (!active.activation.configuredSourcePhases.isEmpty()) {
            result.add(CONFIGURED_SOURCE_PHASE_OBSERVATIONS,
                    sharedRows(active.configuredSourcePhaseObservations));
            result.add(CONFIGURED_SOURCE_PHASE_GAPS,
                    sharedRows(active.configuredSourcePhaseGaps));
        }
        result.add("branchMappings", sharedRows(active.branchMappings));
        if (!active.branchCoverageGaps.isEmpty()) {
            result.add("branchCoverageGaps",
                    sharedRows(active.branchCoverageGaps));
        }
        if (!active.concreteBranchWitnesses.isEmpty()) {
            result.add("concreteBranchWitnesses",
                    sharedRows(active.concreteBranchWitnesses));
        }
        // Every evidence row this activation publishes names the run, the
        // session, the activation, and the read-out batch it came from.
        VmHandoffEvidence.writeTo(result, active.vmHandoffEvents);
        if (!active.rpcHandoffGaps.isEmpty()) {
            result.add("rpcHandoffGaps",
                    stamped(active.rpcHandoffGaps, identity));
        }
    }

    /** Whether this candidate supplied the evidence its selected goal needs. */
    private static boolean resultAnswersSelectedGoal(
            RuntimeTask task, JsonObject result) {
        // One complete non-loop activation is the selected occurrence.  A
        // targetReached:false row is its seed case and must settle the task;
        // a later replay is a separate planned task, not another candidate
        // for this physical occurrence.
        if (!task.loopBodyRoot) {
            return true;
        }
        if (task.capturesTargetReach) {
            return optionalBool(result, "targetReached", false);
        }
        return true;
    }

    /** Whether this activation decided the selected fatal target event. */
    private static boolean targetReachedByActivation(ActiveRegion active) {
        RuntimeTask task = active.activation;
        if (task.declaresTargetBranch()) {
            return task.reachedRequiredTargetOutcome(active.targetReach);
        }
        return task.capturesTargetReach
                && "THROW".equals(safe(active.exitKind))
                && !safe(active.exceptionType).isEmpty();
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
        addReplayIdentity(result, task);
        result.addProperty("exitKind", exitKind);
        result.addProperty("exceptionType", safe(exceptionType));
        // README OCC-1 result-row contract, consumed by the importer:
        // one row per activation of the address, each naming which activation
        // it is and what it did or did not reach.
        result.addProperty("plannedOccurrenceId", task.occurrenceId);
        result.addProperty("occurrenceId", active.occurrenceId());
        result.addProperty("activationOrdinal", active.activationOrdinal);
        if (task.capturesTargetReach) {
            // Only a target-reach address selects on this.
            result.addProperty("targetReached",
                    targetReachedByActivation(active));
        }
    }

    /** Publishes the linked replay family carried by this exact task. */
    private static void addReplayIdentity(JsonObject result,
                                          RuntimeTask task) {
        result.addProperty("replayGroupId", task.replayGroupId);
        result.addProperty("linkedReplayRole", task.linkedReplayRole);
        result.addProperty("familySnapshotDigest",
                task.familySnapshotDigest);
        result.addProperty("topologyEpoch", task.topologyEpoch);
    }

    private static void symbolizeReceiverFields(ActiveRegion active,
                                               RuntimeTask task,
                                               EngineApi api) {
        for (SymbolizeAction action : task.symbolize) {
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
            String leafFieldSignature = action.exactLeafFieldSignature(
                    exactFieldPath);
            Object value = readExactField(owner, leafFieldSignature);
            DeclaredField field = FieldPathSpec.declaredField(
                    leafFieldSignature);
            if (field == null) {
                active.unresolved.add(symbol
                        + ": exact field declaration is unavailable");
                return;
            }
            JsonElement carried = containerValue(value)
                    ? engineExpression(api.expression(value))
                    : engineExpression(api.fieldExpression(owner,
                    field.owner(), field.name(),
                    javaTypeDescriptor(field.type()), value));
            if (retainPropagatedInput(active, action, value, carried, symbol,
                    exactFieldPath, leafFieldSignature)) {
                return;
            }
            JsonElement expression;
            if (value != null && value != MissingValue.INSTANCE
                    && containerValue(value)) {
                if (!trackContainerOrObserveConcrete(active, api, value,
                        action)) {
                    return;
                }
                ensurePathRecordingStarted(active);
                active.recordSymbolizedInputPort(action.symbol, value);
                expression = engineExpression(api.expression(value));
            } else {
                api.symbolizeExactField(owner, leafFieldSignature,
                        manualMintLabel(symbol, active.activation.occurrenceId,
                                primitiveDescriptor(field.type())));
                ensurePathRecordingStarted(active);
                expression = engineExpression(api.fieldExpression(owner,
                        field.owner(), field.name(),
                        javaTypeDescriptor(field.type()), value));
            }
            active.recordManualSymbolization(action, symbol, exactFieldPath,
                    leafFieldSignature, expression, true, false);
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
        String label = FieldPathSpec.join(path);
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
            active.unresolved.add(action.symbol + "." + FieldPathSpec.join(path)
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
                assignment)) {
            active.unresolved.add(action.symbol + "." + FieldPathSpec.join(path)
                    + ": solver model could not be written to real field");
            return;
        }
        active.recordModelAssignment(assignment);
    }

    private static Object materializePrimitiveValue(
            ActiveRegion active, SymbolizeAction action, Object concrete,
            List<String> path) {
        EngineApi api = engine();
        List<String> exactPath = path == null
                ? Collections.<String>emptyList() : path;
        String fieldSignature = path == null ? ""
                : action.exactLeafFieldSignature(path);
        JsonElement carried;
        try {
            carried = primitiveBoxExpression(api, concrete);
        } catch (Throwable unsymbolized) {
            carried = null;
        }
        if (retainPropagatedInput(active, action, concrete, carried,
                action.symbol, exactPath, fieldSignature)) {
            return concrete;
        }
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
            api.symbolizeField(fresh, "value", manualMintLabel(action.symbol,
                    active.activation.occurrenceId, true));
            ensurePathRecordingStarted(active);
            JsonElement expression = primitiveBoxExpression(api, fresh);
            active.recordManualSymbolization(action, action.symbol,
                    exactPath, fieldSignature, expression, true, false);
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

    /** Exact expression stored in a Java primitive wrapper's value field. */
    private static JsonElement primitiveBoxExpression(
            EngineApi api, Object boxed) throws Exception {
        if (boxed == null) return null;
        String descriptor = JavaPrimitiveBoxing.primitiveDescriptor(
                boxed.getClass().getName());
        if (descriptor.isEmpty()) return null;
        return engineExpression(api.fieldExpression(boxed,
                boxed.getClass().getName(), "value", descriptor, boxed));
    }

    static boolean writeModeledField(
            Object owner, String fieldSignature,
            ModelAssignment assignment) {
        Field field = declaredInstanceField(owner, fieldSignature);
        if (field == null) return false;
        try {
            Object value = coerceModelValue(assignment.valueType,
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
            Object container, ModelAssignment assignment) {
        if ("INDEXED".equals(assignment.containerShape)) {
            return writeIndexedContainerElement(container,
                    assignment.containerIndex,
                    assignment.valueType, assignment.value);
        }
        if (!"ASSOCIATIVE".equals(assignment.containerShape)) return false;
        if (assignment.iterationTarget()) {
            return writeOrderedIterationTarget(container, assignment);
        }
        if (assignment.dynamicAssociativeTarget()) return false;
        if (!(container instanceof Map<?, ?>)) return false;
        Object key = containerKey(assignment.containerKeyJavaType,
                assignment.containerKeyValue);
        if (key == UnsupportedReplayValue.INSTANCE) return false;
        return writeAssociativeContainerTarget(container, key, assignment);
    }

    @SuppressWarnings("unchecked")
    static boolean writeAssociativeContainerTarget(
            Object container, Object key, ModelAssignment assignment) {
        if (!(container instanceof Map<?, ?>)
                || !"ASSOCIATIVE".equals(assignment.containerShape)) {
            return false;
        }
        Map<Object, Object> map = (Map<Object, Object>) container;
        if ("UNCHANGED".equals(assignment.valueType)) {
            // A non-null reference model constrains only nullness. The live
            // object is already the only replayable identity.
            return map.containsKey(key) && map.get(key) != null;
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
            Object container, ModelAssignment assignment) {
        int index = assignment.containerIndex;
        if (index < 0) return false;
        try {
            if (container instanceof LinkedHashSet<?>
                    && "KEY".equals(assignment.containerProjection)) {
                List<Object> values = new ArrayList<>(
                        (Set<Object>) container);
                if (index >= values.size()) return false;
                Object current = values.get(index);
                Object modeled = modeledContainerValue(current, assignment);
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
            if (container instanceof Map<?, ?>
                    && "VALUE".equals(assignment.containerProjection)) {
                Map<Object, Object> target = (Map<Object, Object>) container;
                List<Map.Entry<Object, Object>> entries = new ArrayList<>(
                        target.entrySet());
                if (index >= entries.size()) return false;
                Map.Entry<Object, Object> selected = entries.get(index);
                Object modeled = modeledContainerValue(
                        selected.getValue(), assignment);
                if (modeled == UnsupportedReplayValue.INSTANCE) return false;
                // Replacing the value of an existing entry is not a
                // structural modification and therefore preserves the live
                // map's current iteration frontier, including HashMap's.
                target.put(selected.getKey(), modeled);
                return true;
            }
            if (!(container instanceof LinkedHashMap<?, ?>)) return false;
            LinkedHashMap<Object, Object> target =
                    (LinkedHashMap<Object, Object>) container;
            List<Map.Entry<Object, Object>> entries = new ArrayList<>(
                    target.entrySet());
            if (index >= entries.size()) return false;
            Map.Entry<Object, Object> selected = entries.get(index);
            if (!"KEY".equals(assignment.containerProjection)) return false;
            Object current = selected.getKey();
            Object modeled = modeledContainerValue(current, assignment);
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
            Object current, ModelAssignment assignment) {
        if ("NULL".equals(assignment.valueType)) return null;
        return current == null ? UnsupportedReplayValue.INSTANCE
                : coerceModelValue(assignment.valueType,
                assignment.value, current.getClass());
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

    private static void symbolize(ActiveRegion active, SymbolizeAction action,
                                  Object value, EngineApi api) {
        try {
            boolean liveArray = value != null && value.getClass().isArray();
            boolean declaredArray = action.declaresArrayInput(
                    Collections.<String>emptyList());
            if (declaredArray && !liveArray) return;
            JsonElement carried = value == null ? null
                    : engineExpression(api.expression(value));
            if (retainPropagatedInput(active, action, value, carried,
                    action.symbol, Collections.<String>emptyList(), "")) {
                return;
            }
            if (containerValue(value)) {
                if (!trackContainerOrObserveConcrete(active, api, value,
                        action)) {
                    return;
                }
            } else {
                api.symbolize(value, manualMintLabel(action.symbol,
                        active.activation.occurrenceId,
                        isPrimitiveBox(value)));
            }
            ensurePathRecordingStarted(active);
            if (value != null && !liveArray) {
                active.recordSymbolizedInputPort(action.symbol, value);
            }
            JsonElement expression = value == null ? null
                    : engineExpression(api.expression(value));
            active.recordManualSymbolization(action, action.symbol,
                    Collections.<String>emptyList(), "", expression,
                    true, false);
        } catch (Throwable throwable) {
            active.unresolved.add(action.symbol + ": symbolize failed: "
                    + rootCause(throwable));
        }
    }

    /** Keeps a VM-propagated value as this consumer's input authority. */
    private static boolean retainPropagatedInput(
            ActiveRegion active, SymbolizeAction action, Object value,
            JsonElement expression, String requestedSymbol,
            List<String> fieldPath, String fieldSignature) {
        if (!VmExpressionIr.carriesPropagatedValue(expression)) return false;
        ensurePathRecordingStarted(active);
        if (value != null && !value.getClass().isArray()) {
            active.recordSymbolizedInputPort(action.symbol, value);
        }
        active.recordManualSymbolization(action, requestedSymbol, fieldPath,
                fieldSignature, expression, false, true);
        return true;
    }

    private static boolean containerValue(Object value) {
        return value != null && (value.getClass().isArray()
                || value instanceof Map<?, ?>
                || value instanceof Set<?>
                || value instanceof Collection<?>);
    }

    /**
     * Gives each manually minted primitive root the stable address of its
     * planned occurrence. A propagated expression never reaches a mint call,
     * and reference/container labels retain their existing wire identity.
     */
    static String manualMintLabel(String requestedSymbol,
                                  String plannedOccurrenceId,
                                  boolean primitiveRoot) {
        String requested = safe(requestedSymbol);
        if (!primitiveRoot) return requested;
        String occurrence = safe(plannedOccurrenceId);
        if (requested.isEmpty() || occurrence.isEmpty()) {
            throw new IllegalArgumentException(
                    "manual primitive mint requires symbol and occurrence");
        }
        return requested + ".occ."
                + CanonicalJson.sha256(occurrence);
    }

    private static boolean primitiveDescriptor(String javaType) {
        String descriptor = javaTypeDescriptor(javaType);
        return descriptor.length() == 1
                && "ZBCSIJFD".contains(descriptor);
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
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long token = tokens.peek();
        return token == null ? null : ownerRegion(token);
    }

    private static void pushActiveRegion(ActiveRegion active) {
        CURRENT_TOKENS.get().push(active.token);
    }

    /** True only when {@code active} is the innermost region with a caller. */
    private static boolean hasEnclosingActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long current = tokens.peek();
        if (current == null || current.longValue() != active.token) {
            throw new IllegalStateException(
                    "selected regions must close in strict LIFO order");
        }
        return tokens.size() > 1;
    }

    /** The exact selected caller of the current innermost activation. */
    private static ActiveRegion enclosingActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        java.util.Iterator<Long> iterator = tokens.iterator();
        Long current = iterator.hasNext() ? iterator.next() : null;
        if (current == null || current.longValue() != active.token) {
            throw new IllegalStateException(
                    "selected regions must inspect callers in strict LIFO "
                            + "order");
        }
        Long enclosingToken = iterator.hasNext() ? iterator.next() : null;
        return enclosingToken == null ? null : ownerRegion(enclosingToken);
    }

    /** Pops the exact innermost activation; an ownership mismatch is fatal. */
    private static void popActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long current = tokens.peek();
        if (current == null || current.longValue() != active.token) {
            throw new IllegalStateException(
                    "selected region stack does not own token " + active.token);
        }
        tokens.pop();
        if (tokens.isEmpty()) CURRENT_TOKENS.remove();
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
        if (!"BinaryExpression".equals(optionalString(object, "_type"))) {
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
        String observed = optionalString(object, "_op");
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
        if (!"OpStrExpression".equals(optionalString(condition, "_type"))) {
            return null;
        }
        String operation = optionalString(condition, "_name");
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
        return !optionalBool(condition, "_is_not", false);
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
        if (!"BinaryExpression".equals(optionalString(original, "_type"))) {
            return condition;
        }
        Matcher matcher = BRANCH_OPERATOR.matcher(safe(expression));
        if (!matcher.find()) {
            return condition;
        }
        String expected = outcome ? matcher.group(1)
                : BranchPredicateAlgebra.complementOperator(
                matcher.group(1));
        String observed = optionalString(original, "_op");
        if (!observedOperatorImpliesBranch(expected, observed,
                safe(expression).matches(".*\\bnull\\b.*"))
                || expected.equals(observed)) {
            return condition;
        }
        JsonObject normalized = shallowCopy(original);
        normalized.addProperty("_op", expected);
        return normalized;
    }

    private static String binaryOperator(JsonElement condition) {
        return condition != null && condition.isJsonObject()
                ? optionalString(condition.getAsJsonObject(), "_op") : "";
    }

    private static boolean symbolicNull(JsonElement element) {
        if (element == null || !element.isJsonObject()) {
            return false;
        }
        JsonObject object = element.getAsJsonObject();
        return "SymbolExpression".equals(optionalString(object, "_type"))
                && VmExpressionIr.SYMBOLIC_NULL.equals(
                optionalString(object, "_exp"));
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

    /** Records that an activation published nothing, and why. */
    private static void writeSkipped(RuntimeTask activation, String skipKind,
                                     String reason, JsonObject evidence) {
        JsonObject result = new JsonObject();
        result.addProperty("event", "CONCOLIC_REGION_SKIPPED");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", activation.taskId);
        addReplayIdentity(result, activation);
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
        private static final String TREE_MODE = "TREE";
        private static final String WINDOW_MODE = "WINDOW_SCAN";

        private final JsonArray tree;
        /** Absolute index of element 0, and the exclusive end of the window. */
        private final int base;
        private final int windowEnd;
        /** Conditions the thread has accumulated, window or not. */
        private final int size;
        private final boolean windowed;

        private PathConditionElements(JsonArray tree) {
            this(tree, 0, tree.size(), tree.size(), false);
        }

        private PathConditionElements(JsonArray tree, int base, int windowEnd,
                                      int size, boolean windowed) {
            this.tree = tree;
            this.base = base;
            this.windowEnd = windowEnd;
            this.size = size;
            this.windowed = windowed;
        }

        /**
         * Reads one {@code CONCOLIC_PATH_CONDITION_RANGE} envelope as the
         * conditions at absolute indices {@code [startIndex, endIndex)}.
         *
         * <p>The VM always writes the window through the session expression
         * table, so the envelope is decoded once by the shared importer and
         * never rescanned by hand.</p>
         */
        static PathConditionElements window(String envelope, int expectedStart,
                                            VmExpressionTable.Store store) {
            if (envelope == null) return null;
            try {
                JsonObject decoded = store.importEnvelope(envelope);
                int start = optionalInteger(decoded, "startIndex", -1);
                int end = optionalInteger(decoded, "endIndex", -1);
                int watermark = optionalInteger(decoded,
                        "pathConditionWatermark", -1);
                JsonArray conditions = array(decoded, "conditions");
                int declaredCount = optionalInteger(decoded, "conditionCount", -1);
                if (start != expectedStart || end < start
                        || watermark < 0
                        || conditions.size() != end - start
                        || declaredCount != conditions.size()) {
                    return null;
                }
                return new PathConditionElements(conditions, start, end,
                        watermark, true);
            } catch (RuntimeException malformed) {
                return null;
            }
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
            return tree.get(index - base);
        }

        /** Which reader answered, for the replay's own diagnostics. */
        String mode() {
            return windowed ? WINDOW_MODE : TREE_MODE;
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

        private int observe(String key) {
            int occurrence = observed(key) + 1;
            occurrences.put(key, occurrence);
            return occurrence;
        }

        private int observed(String key) {
            return occurrences.getOrDefault(key, 0);
        }
    }

    private static final class ActiveRegion {
        private final long token;
        /** The one task whose region-local path this activation records. */
        private final RuntimeTask activation;
        /**
         * This activation's ordinal within its address, taken at admission so
         * every symbol, mint row and handoff lineage it publishes can name
         * the occurrence it belongs to rather than the planned address.
         */
        private int activationOrdinal;
        /** VM context whose writes belong to this materialized activation. */
        private long vmContextId;
        /** Exact event-ledger entry of this native region frame. */
        private long vmRegionEnterEventId;
        private final Object receiver;
        private final Thread thread;
        /** Entry lacked local producer-source evidence; OUT must confirm it. */
        private final boolean deferredOutgoingSource;
        /** Exact outgoing message leaves this provisional activation reached. */
        private final Set<String> observedOutgoingSourcePorts =
                new LinkedHashSet<>();
        private final AtomicBoolean finished = new AtomicBoolean();
        private boolean prepared;
        /**
         * The declared target branch event this occurrence decided, or {@code
         * null} while it has not decided one.
         */
        private JsonObject targetReach;
        /** Terminal outcome, frozen when the occurrence stops running. */
        private boolean abandoned;
        /** A selected non-loop occurrence ended in a durable named gap. */
        private boolean terminalGap;
        private boolean closed;
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
        private Throwable exitThrowable;
        /** Exact configured-source and planned-action observations. */
        private final List<JsonObject> symbolizedRows = new ArrayList<>();
        /** Exact configured source roots materialized by this activation. */
        private final Map<String, JsonObject> symbolicSources =
                new LinkedHashMap<>();
        /**
         * Mint sites, and the fields they mint, this activation reached.
         *
         * <p>A configured source mints one symbol per element of the walk it
         * runs, and those occurrences are recorded here rather than in
         * the ordinary input-action ledger: the mint hook is a call-site
         * phase, not an instrumented field access. A capture anchored on one of those
         * per-element ports is answered by the site having run.</p>
         */
        private final Set<String> reachedConfiguredSourceSites =
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
        private final List<JsonObject> branchCoverageGaps = new ArrayList<>();
        private final Set<String> branchCoverageGapKeys =
                new LinkedHashSet<>();
        /**
         * Branches this activation executed before its symbolic gate opened.
         */
        private final List<JsonObject> concreteBranchWitnesses =
                new ArrayList<>();
        /** Exact pre-gate decisions already emitted, including switch arms. */
        private final Set<String> concreteBranchDecisionTokens =
                new LinkedHashSet<>();
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
                String phaseId = optionalString(observation, "matchedPhaseId");
                if (!phaseId.isEmpty()) {
                    carried.add(activation.sourcePhaseAnchorId(phaseId));
                }
            }
            Set<String> anchors = activation.causalAnchorPorts();
            for (JsonObject handoff : vmHandoffEvents) {
                String portId = optionalString(handoff, "portId");
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
        private final Map<String, JsonObject> sharedStateRecords =
                new LinkedHashMap<>();
        private final List<JsonObject> sharedStateGaps = new ArrayList<>();

        /** Read-out batch every record of this activation is stamped with. */
        private long evidenceSnapshot;
        private final Set<String> materialized = new LinkedHashSet<>();
        private final Map<String, Long> armedGuardedReads =
                new LinkedHashMap<>();
        private final Set<String> materializedGuardedReads =
                new LinkedHashSet<>();
        private final Set<String> appliedModelAssignments =
                new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        private final OccurrenceCounter
                materializationOccurrences =
                new OccurrenceCounter();
        private final Map<String, Integer> accessorCallOccurrences =
                new LinkedHashMap<>();
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
        private final ReplayFieldWrites writtenFields =
                new ReplayFieldWrites();
        private final Map<String, Object> fieldAccessOwners =
                new LinkedHashMap<>();
        private final Set<String> ambiguousFieldAccessOwners =
                new LinkedHashSet<>();
        private final Map<String, Integer> associativeAccessOccurrences =
                new LinkedHashMap<>();
        private final BranchReplayContract.ReplayProgress replayProgress;
        /** One shared expression DAG for all read-outs in this VM session. */
        private final VmExpressionTable.Store expressionStore;
        private long preparedBranchSequence;
        private int lastPathConditionSize;
        private JsonObject loopBoundCut;
        private JsonObject replayResourceCut;
        private boolean pathRecordingStarted;

        private ActiveRegion(long token, RuntimeTask activation,
                             Object receiver, Thread thread,
                             boolean deferredOutgoingSource) {
            this.token = token;
            this.activation = activation;
            this.receiver = receiver;
            this.thread = thread;
            this.deferredOutgoingSource = deferredOutgoingSource;
            this.expressionStore = workloadExpressionStore;
            this.loopBackedges = new LoopBackedgeBudget(
                    activation.loopBound);
            this.replayProgress = new BranchReplayContract.ReplayProgress(
                    activation.replayContract);
        }

        /** Confirms a provisional producer only from its executed OUT sites. */
        private synchronized void observeOutgoingSourceAnchor(String portId) {
            if (!deferredOutgoingSource
                    || !activation.deferredOutgoingSourcePorts.contains(
                    safe(portId))) {
                return;
            }
            observedOutgoingSourcePorts.add(safe(portId));
            if (observedOutgoingSourcePorts.containsAll(
                    activation.deferredOutgoingSourcePorts)) {
                observedSourceKeys.add(activation.sourceKey);
            }
        }

        private synchronized boolean outgoingSourceConfirmed() {
            return !deferredOutgoingSource
                    || observedOutgoingSourcePorts.containsAll(
                    activation.deferredOutgoingSourcePorts);
        }

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

        /**
         * Charges one body of this loop to the replay resource cap, returning
         * the cut that ends the activation once the cap is spent.
         */
        private synchronized ReplayLoopResourceCut chargeLoopBody(
                String loopId) {
            int maxBodies = activation.maxLoopBodies(loopId);
            chargedLoopBodies++;
            // A fixed-count loop may be invoked repeatedly inside one region
            // activation.  Its resource ceiling applies to each dynamic
            // invocation; accumulating all invocations under the static loop
            // id cuts ordinary code after (for example) two 16-element array
            // walks.  recordLoopCardinality opens the exact invocation before
            // the first body hook and completeLoopCardinality closes it.
            DynamicLoopCardinality invocation =
                    activeLoopCardinalities.get(loopId);
            String budgetKey = invocation == null ? loopId
                    : LoopBackedgeBudget.scoped(
                    loopId, invocation.occurrence);
            long entered = loopBackedges.recordBody(budgetKey);
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

        /** Records the terminal of this activation's bounded local path. */
        private LoopBoundCut loopBoundCut(
                String backedgeId, int maxTraversals, String reason) {
            LoopBoundCut cut = new LoopBoundCut(backedgeId, maxTraversals,
                    reason);
            if (loopBoundCut == null) {
                loopBoundCut = cut.toJson();
                addUnresolvedOnce("LOOP_BOUND_PATH_CUT:"
                        + cut.backedgeId + ':' + cut.reason);
            }
            return cut;
        }

        private int nextBranchOccurrence(String siteId) {
            Integer previous = branchOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            branchOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        /** Records a branch while the symbolic gate is closed. */
        private ExactConcreteBranchObservation recordConcreteBranch(
                String method, int unitIndex, boolean outcome) {
            try {
                String site = siteId(method, unitIndex);
                if (!activation.declaresBranch(site)) {
                    String token = site + "\u0000"
                            + ExactConcreteBranchObservation
                            .binaryDecisionToken(outcome);
                    if (concreteBranchDecisionTokens.add(token)) {
                        concreteBranchWitnesses.add(concreteBranchWitness(
                                method, unitIndex, outcome));
                    }
                    return null;
                }
                int occurrence = nextBranchOccurrence(site);
                ExactConcreteBranchObservation observation =
                        ExactConcreteBranchObservation.attested(site,
                                safe(method), unitIndex, occurrence, outcome);
                JsonObject mapping = branchMapping(method, unitIndex,
                        occurrence);
                mapping.addProperty("rawPathConditionSize", 0);
                mapping.addProperty("rawPathConditionBaseline", 0);
                mapping.add("concreteObservation", observation.toJson());
                branchMappings.add(mapping);
                if (activation.targetBranchSite.equals(site)
                        && activation.targetBranchOccurrence == occurrence) {
                    recordTargetReach(site, occurrence, outcome);
                }
                return observation;
            } catch (Throwable ignored) {
                // Observation must never alter the workload's own outcome.
                return null;
            }
        }

        /** Persists an exact replay-invocation boundary without adding a PC. */
        private ExactConcreteBranchObservation recordReplayBoundary(
                String method, int unitIndex, int occurrence,
                boolean outcome) {
            try {
                String site = siteId(method, unitIndex);
                ExactConcreteBranchObservation observation =
                        ExactConcreteBranchObservation.attested(site,
                                safe(method), unitIndex, occurrence, outcome);
                JsonObject mapping = branchMapping(method, unitIndex,
                        occurrence);
                mapping.addProperty("rawPathConditionSize", 0);
                mapping.addProperty("rawPathConditionBaseline", 0);
                mapping.add("concreteObservation", observation.toJson());
                branchMappings.add(mapping);
                return observation;
            } catch (Throwable ignored) {
                return null;
            }
        }

        /** Switch counterpart of {@link #recordReplayBoundary}. */
        private ExactConcreteBranchObservation recordReplaySwitchBoundary(
                String method, int unitIndex, int occurrence,
                SwitchExpectation expected) {
            try {
                String site = siteId(method, unitIndex);
                ExactConcreteBranchObservation observation =
                        ExactConcreteBranchObservation.attestedSwitch(site,
                                safe(method), unitIndex, occurrence,
                                expected.branchKind, expected.caseKeys,
                                expected.observedSuccessorIndex);
                JsonObject mapping = branchMapping(method, unitIndex,
                        occurrence);
                mapping.addProperty("rawPathConditionSize", 0);
                mapping.addProperty("rawPathConditionBaseline", 0);
                mapping.add("concreteObservation", observation.toJson());
                branchMappings.add(mapping);
                return observation;
            } catch (Throwable ignored) {
                return null;
            }
        }

        /** Records one exact switch successor while the symbolic gate is
         * closed. */
        private ExactConcreteBranchObservation recordConcreteSwitchBranch(
                String method, int unitIndex, SwitchExpectation expected) {
            try {
                String site = siteId(method, unitIndex);
                ExactConcreteBranchObservation observation =
                        ExactConcreteBranchObservation.attestedSwitch(site,
                                safe(method), unitIndex,
                                activation.declaresBranch(site)
                                        ? nextBranchOccurrence(site) : 1,
                                expected.branchKind, expected.caseKeys,
                                expected.observedSuccessorIndex);
                if (!activation.declaresBranch(site)) {
                    String token = site + "\u0000"
                            + observation.exactDecisionToken();
                    if (concreteBranchDecisionTokens.add(token)) {
                        JsonObject witness = concreteBranchWitness(
                                method, unitIndex, expected.caseArm());
                        witness.addProperty("branchKind",
                                expected.branchKind);
                        JsonArray keys = new JsonArray();
                        for (Integer key : expected.caseKeys) keys.add(key);
                        witness.add("caseKeys", keys);
                        witness.addProperty("observedSuccessorIndex",
                                expected.observedSuccessorIndex);
                        concreteBranchWitnesses.add(witness);
                    }
                    return null;
                }
                JsonObject mapping = branchMapping(method, unitIndex,
                        observation.occurrence());
                mapping.addProperty("rawPathConditionSize", 0);
                mapping.addProperty("rawPathConditionBaseline", 0);
                mapping.add("concreteObservation", observation.toJson());
                branchMappings.add(mapping);
                if (activation.targetBranchSite.equals(site)
                        && activation.targetBranchOccurrence
                        == observation.occurrence()) {
                    recordTargetReach(site, observation.occurrence(),
                            expected.caseArm());
                }
                return observation;
            } catch (Throwable ignored) {
                // Observation must never alter the workload's own outcome.
                return null;
            }
        }

        private boolean observeReplayBranch(
                String siteId, int occurrence, boolean outcome) {
            return observeReplayBranch(siteId, occurrence, outcome, "");
        }

        private boolean observeReplayBranch(
                String siteId, int occurrence, boolean outcome,
                String symbolicSupportDigest) {
            boolean matched = replayProgress.observeBinary(
                    siteId, occurrence, outcome, symbolicSupportDigest);
            diag("REPLAY_OBSERVE", siteId + " occ=" + occurrence
                    + " outcome=" + outcome + " matched=" + matched
                    + " complete=" + replayProgress.complete()
                    + " failed=" + replayProgress.failed());
            if (replayProgress.failed()) {
                addUnresolvedOnce("REPLAY_PREFIX_MISMATCH:"
                        + replayProgress.failure());
            }
            return matched;
        }

        private void observeReplaySwitch(String siteId, int occurrence,
                                         SwitchExpectation expected) {
            replayProgress.observeSwitch(siteId, occurrence,
                    expected.branchKind, expected.caseKeys,
                    expected.observedSuccessorIndex);
            diag("REPLAY_OBSERVE", siteId + " occ=" + occurrence
                    + " successor=" + expected.observedSuccessorIndex
                    + " complete=" + replayProgress.complete()
                    + " failed=" + replayProgress.failed());
            if (replayProgress.failed()) {
                addUnresolvedOnce("REPLAY_PREFIX_MISMATCH:"
                        + replayProgress.failure());
            }
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

        private PreparedBranch prepareBranch(
                String method, int unitIndex, String expression)
                throws Exception {
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

        private void addBranchCoverageGap(JsonObject gap) {
            if (gap == null) return;
            String key = CanonicalJson.render(gap);
            if (branchCoverageGapKeys.add(key)) {
                branchCoverageGaps.add(gap);
            }
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
            recordConfiguredSourcePhaseObservation(matched, context);
            return new SourceSiteEntry(matched, site, ordinal);
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
         * Records what one exact frozen {@code SYMBOLIC} action observed after
         * its runtime hook either minted a value or retained a propagated one.
         * The requested VM label is descriptive only; downstream authority is
         * derived from the exact expression, never from this label.
         */
        private synchronized void recordManualSymbolization(
                SymbolizeAction action, String requestedSymbol,
                List<String> fieldPath, String fieldSignature,
                JsonElement expression, boolean minted, boolean reused) {
            if (action == null || minted == reused) {
                throw new IllegalArgumentException(
                        "manual symbolization must be exactly minted or reused");
            }
            JsonObject row = new JsonObject();
            row.addProperty("schemaVersion", 1);
            row.addProperty("kind", MANUAL_INPUT_OBSERVATION_KIND);
            row.addProperty("authority",
                    MANUAL_INPUT_OBSERVATION_AUTHORITY);
            row.addProperty("portId", action.symbol);
            row.addProperty("actionDigest", action.actionDigest);
            row.addProperty("plannedOccurrenceId",
                    activation.occurrenceId);
            row.addProperty("occurrenceId", occurrenceId());
            row.addProperty("symbol", safe(requestedSymbol));
            JsonArray encodedPath = new JsonArray();
            for (String segment : fieldPath == null
                    ? Collections.<String>emptyList() : fieldPath) {
                encodedPath.add(safe(segment));
            }
            row.add("fieldPath", encodedPath);
            row.addProperty("fieldSignature", safe(fieldSignature));
            row.add("expression", expression == null
                    ? JsonNull.INSTANCE : expression);
            JsonObject exact = VmExpressionIr.exactSymbolRoot(expression);
            row.addProperty("rawSymbol", exact == null ? ""
                    : optionalString(exact, "_exp"));
            row.addProperty("javaType", exact == null ? action.javaType
                    : optionalString(exact, "_java_type"));
            row.addProperty("minted", minted);
            row.addProperty("reused", reused);
            symbolizedRows.add(row);
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
                    shallowCopy(evidence));
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

        private void recordSymbolizedInputPort(String symbol, Object value) {
            if (value == null) return;
            String previous = symbolizedInputPorts.get(value);
            symbolizedInputPorts.put(value, previous == null
                    || previous.equals(symbol) ? symbol : "");
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

    }

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
                int previous = optionalInteger(encoded, loopId, 0);
                if (entry.getValue() > previous) {
                    encoded.addProperty(loopId, entry.getValue());
                }
            }
            return encoded;
        }

        JsonObject bodiesToJson() {
            JsonObject encoded = new JsonObject();
            for (Map.Entry<String, Integer> entry : bodies.entrySet()) {
                String scoped = safe(entry.getKey());
                int separator = scoped.indexOf(SCOPE_SEPARATOR);
                String loopId = separator < 0 ? scoped
                        : scoped.substring(0, separator);
                long total = (long) optionalInteger(encoded, loopId, 0)
                        + entry.getValue();
                encoded.addProperty(loopId,
                        (int) Math.min(total, Integer.MAX_VALUE));
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

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("kind", REASON);
            encoded.addProperty("loopId", loopId);
            encoded.addProperty("maxLoopBodies", maxBodies);
            encoded.addProperty("attemptedBody", attemptedBody);
            encoded.addProperty("reason", REASON);
            return encoded;
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
        /** Canonical identity of the exact frozen task action row. */
        private final String actionDigest;
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
        private final String symbolicDemand;
        private final String rootKind;
        private final List<String> fieldPath;
        private final String javaType;
        private final String symbolicName;
        private final Set<Integer> definitionUnitIndices =
                new LinkedHashSet<>();
        private final Map<String, String> leafFieldSignaturesByPath =
                new LinkedHashMap<>();

        private SymbolizeAction(JsonObject json) {
            this.symbol = optionalString(json, "symbol");
            this.actionDigest = CanonicalJson.sha256(json);
            this.cell = optionalString(json, "cell");
            this.location = optionalString(json, "location");
            this.index = optionalInteger(json, "index", -1);
            this.replayOccurrence = optionalInteger(json,
                    "replayOccurrence", -1);
            this.bindingMode = optionalString(json, "bindingMode");
            this.javaType = optionalString(json, "javaType");
            JsonObject definition = json;
            this.method = optionalString(definition, "method");
            this.local = optionalString(definition, "local");
            int unitIndex = optionalInteger(definition, "unitIndex", -1);
            if (unitIndex >= 0) definitionUnitIndices.add(unitIndex);
            for (JsonElement element : array(json, "definitionSites")) {
                if (element.isJsonObject()) {
                    int definitionIndex = optionalInteger(element.getAsJsonObject(),
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
            this.accessFieldSignature = optionalString(json,
                    "accessFieldSignature");
            DeclaredField accessDeclaration = FieldPathSpec.declaredField(
                    this.accessFieldSignature);
            this.accessOwnerClass = accessDeclaration == null ? ""
                    : accessDeclaration.owner();
            this.accessSites.addAll(
                    FieldPathSpec.stringArray(json, "accessSites"));
            this.accessorCallerMethod = optionalString(json,
                    "accessorCallerMethod");
            this.accessorCallUnitIndex = optionalInteger(json,
                    "accessorCallUnitIndex", -1);
            this.accessorDeclaredCallee = optionalString(json,
                    "accessorDeclaredCallee");
            this.accessorImplementationMethod = optionalString(json,
                    "accessorImplementationMethod");
            this.symbolicDemand = optionalString(json, "symbolicDemand");
            this.rootKind = optionalString(json, "rootKind");
            String explicitLeafSignature = firstNonBlank(
                    optionalString(json, "leafFieldSignature"),
                    this.accessFieldSignature);
            this.fieldPaths = new ArrayList<>(
                    FieldPathSpec.paths(json, "fieldPaths"));
            if (this.fieldPaths.isEmpty() && !this.fieldPath.isEmpty()) {
                this.fieldPaths.add(new ArrayList<>(this.fieldPath));
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
                    leafFieldSignaturesByPath.putIfAbsent(FieldPathSpec.join(
                            this.fieldPath.subList(0, hop + 1)), signature);
                }
            }
            if (!this.fieldPath.isEmpty()
                    && FieldPathSpec.declaredField(
                    explicitLeafSignature) != null) {
                leafFieldSignaturesByPath.put(FieldPathSpec.join(
                        this.fieldPath), explicitLeafSignature);
            }
            this.symbolicName = optionalString(json, "symbolicName");
        }

        private boolean declaresArrayInput(List<String> actualPath) {
            String pathSignature = leafFieldSignaturesByPath.get(
                    FieldPathSpec.join(actualPath));
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
                    FieldPathSpec.join(actualPath));
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

    /** One scalar assignment returned by a path-flip solve. */
    static final class ModelAssignment {
        private final String key;
        private final String engineSymbol;
        private final String inputSymbol;
        private final String valueType;
        private final String value;
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
        private final String containerKeyJavaType;
        private final String containerKeyValue;
        private final List<String> path = new ArrayList<>();

        ModelAssignment(JsonObject json) {
            this.engineSymbol = firstNonBlank(optionalString(json, "engineSymbol"));
            this.inputSymbol = optionalString(json, "inputSymbol");
            this.valueType = optionalString(json, "valueType");
            this.value = optionalString(json, "value");
            this.configuredSourcePhaseId = optionalString(json,
                    "configuredSourcePhaseId");
            this.configuredSourceId = optionalString(json,
                    "configuredSourceId");
            this.configuredSourceFieldSignature = optionalString(json,
                    "configuredSourceFieldSignature");
            this.modelIsNull = optionalBool(json, "modelIsNull", false);
            JsonElement encodedContainerTarget = json.get("containerTarget");
            this.containerTargetPresent = encodedContainerTarget != null;
            JsonObject containerTarget = object(json, "containerTarget");
            this.containerShape = optionalString(containerTarget, "shape");
            this.containerSelectorKind = optionalString(containerTarget,
                    "selectorKind");
            this.containerProjection = optionalString(containerTarget,
                    "projection");
            this.containerIndex = optionalInteger(containerTarget, "index", -1);
            this.containerAccessOrdinal = optionalInteger(containerTarget,
                    "accessOrdinal", -1);
            this.containerKeyJavaType = optionalString(containerTarget,
                    "keyJavaType");
            this.containerKeyValue = optionalString(containerTarget, "keyValue");
            for (JsonElement element : array(json,
                    "materializationPath")) {
                if (element.isJsonPrimitive()) {
                    path.add(element.getAsString());
                }
            }
            this.key = firstNonBlank(optionalString(json, "modelAssignmentKey"),
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

        private boolean hasContainerTarget() {
            return containerTargetPresent;
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
                return containerIndex >= 0;
            }
            if (iterationTarget()) {
                return containerIndex >= 0
                        && ("KEY".equals(containerProjection)
                        || "VALUE".equals(containerProjection));
            }
            if (dynamicAssociativeTarget()) {
                return true;
            }
            if (!"ASSOCIATIVE".equals(containerShape)
                    || containerKeyJavaType.isEmpty()
                    || containerKeyValue.isEmpty()) {
                return false;
            }
            return true;
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

    /** One solver-selected scalar arm for one exact shared-field read. */
    static final class GuardedReadAssignment {
        private static final String KIND = "PRIMITIVE_FIELD_READ";
        private static final String AUTHORITY =
                "SOLVER_SELECTED_GUARDED_READ_ARM_V1";

        private final String readIdentity;
        private final String candidateIdentity;
        private final String readerTaskId;
        private final String readerOccurrenceId;
        private final String consumerSiteId;
        private final int consumerSiteOccurrence;
        private final String declaringClass;
        private final String fieldName;
        private final String descriptor;
        private final long valueBits;

        GuardedReadAssignment(JsonObject json, String taskOccurrenceId) {
            if (optionalInteger(json, "schemaVersion", 0) != 1
                    || !KIND.equals(optionalString(json, "kind"))
                    || !AUTHORITY.equals(optionalString(json, "authority"))) {
                throw new IllegalArgumentException(
                        "unsupported guarded read assignment schema");
            }
            this.readIdentity = optionalString(json, "readIdentity");
            this.candidateIdentity = optionalString(json, "candidateIdentity");
            this.readerTaskId = optionalString(json, "readerTaskId");
            this.readerOccurrenceId = PathObservation.plannedOccurrenceOf(
                    optionalString(json, "readerOccurrenceId"));
            this.consumerSiteId = optionalString(json, "consumerSiteId");
            this.consumerSiteOccurrence = optionalInteger(json,
                    "consumerSiteOccurrence", 0);
            this.declaringClass = optionalString(json, "declaringClass");
            this.fieldName = optionalString(json, "fieldName");
            this.descriptor = javaTypeDescriptor(optionalString(json, "descriptor"));
            String valueType = optionalString(json, "valueType");
            String value = optionalString(json, "value");
            String plannedTaskOccurrence = PathObservation.plannedOccurrenceOf(
                    taskOccurrenceId);
            if (readIdentity.isEmpty() || candidateIdentity.isEmpty()
                    || readerTaskId.isEmpty() || readerOccurrenceId.isEmpty()
                    || !readerOccurrenceId.equals(plannedTaskOccurrence)
                    || consumerSiteId.isEmpty() || consumerSiteOccurrence < 1
                    || declaringClass.isEmpty() || fieldName.isEmpty()) {
                throw new IllegalArgumentException(
                        "incomplete guarded read assignment " + readIdentity);
            }
            this.valueBits = primitiveValueBits(descriptor, valueType, value);
        }

        private static long primitiveValueBits(String descriptor,
                                               String valueType,
                                               String value) {
            if ("Z".equals(descriptor)) {
                if (!"BOOL".equals(valueType)
                        || !("true".equals(value) || "false".equals(value))) {
                    throw new IllegalArgumentException(
                            "boolean guarded read has malformed value " + value);
                }
                return "true".equals(value) ? 1L : 0L;
            }
            if (!("B".equals(descriptor) || "C".equals(descriptor)
                    || "S".equals(descriptor) || "I".equals(descriptor)
                    || "J".equals(descriptor))
                    || !"INT".equals(valueType)) {
                throw new IllegalArgumentException(
                        "unsupported guarded read descriptor/type "
                                + descriptor + "/" + valueType);
            }
            final BigInteger parsed;
            try {
                parsed = new BigInteger(value);
            } catch (NumberFormatException malformed) {
                throw new IllegalArgumentException(
                        "guarded read has malformed integer value " + value,
                        malformed);
            }
            BigInteger minimum;
            BigInteger maximum;
            if ("B".equals(descriptor)) {
                minimum = BigInteger.valueOf(Byte.MIN_VALUE);
                maximum = BigInteger.valueOf(Byte.MAX_VALUE);
            } else if ("C".equals(descriptor)) {
                minimum = BigInteger.ZERO;
                maximum = BigInteger.valueOf(Character.MAX_VALUE);
            } else if ("S".equals(descriptor)) {
                minimum = BigInteger.valueOf(Short.MIN_VALUE);
                maximum = BigInteger.valueOf(Short.MAX_VALUE);
            } else if ("I".equals(descriptor)) {
                minimum = BigInteger.valueOf(Integer.MIN_VALUE);
                maximum = BigInteger.valueOf(Integer.MAX_VALUE);
            } else {
                minimum = BigInteger.valueOf(Long.MIN_VALUE);
                maximum = BigInteger.valueOf(Long.MAX_VALUE);
            }
            if (parsed.compareTo(minimum) < 0
                    || parsed.compareTo(maximum) > 0) {
                throw new IllegalArgumentException(
                        "guarded read value is outside " + descriptor
                                + " range: " + value);
            }
            return parsed.longValue();
        }

        private boolean matches(ConsumerAccessAnchor consumer,
                                DeclaredField field) {
            return consumer != null && field != null
                    && consumerSiteId.equals(consumer.siteId)
                    && consumerSiteOccurrence == consumer.occurrence
                    && declaringClass.equals(field.owner())
                    && fieldName.equals(field.name())
                    && descriptor.equals(javaTypeDescriptor(field.type()));
        }
    }

    /** Registration wins; inheritance fills only an absent replay alias. */
    static boolean registeredSourceAnchorMatches(
            String expectedSourceKey, SourceRef registeredReceiverSource,
            SourceRef inheritedSource) {
        if (registeredReceiverSource != null) {
            return RuntimeTraceContext.sameSourceIdentity(
                    expectedSourceKey, registeredReceiverSource.key());
        }
        return inheritedSource != null
                && RuntimeTraceContext.sameSourceIdentity(
                expectedSourceKey, inheritedSource.key());
    }

    /**
     * Whether an exact OUT hook may supply a producer identity lost while the
     * workload reconstructed its receiver.
     *
     * <p>The inherited source inside a request is commonly the caller, not
     * the service receiver.  It therefore does not contradict a missing
     * receiver registration when the complete traced request address still
     * matches.  Admission remains provisional: the activation publishes only
     * after every unique planner-authored OUT port actually executes.</p>
     */
    static boolean outgoingProducerMayDeferMissingContext(
            boolean exactUniqueOutgoingAnchor,
            SourceRef registeredReceiverSource,
            SourceRef inheritedSource,
            String plannedSourceKey, String plannedRequestKey,
            String plannedRequestApi, String actualRequestKey,
            String actualRequestApi) {
        if (!exactUniqueOutgoingAnchor || registeredReceiverSource != null
                || safe(plannedSourceKey).isEmpty()
                || OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(
                safe(plannedSourceKey))
                || safe(plannedRequestKey).isEmpty()
                || safe(plannedRequestApi).isEmpty()) {
            return false;
        }
        boolean exactRequestAddress = safe(plannedRequestKey).equals(
                safe(actualRequestKey))
                && safe(plannedRequestApi).equals(safe(actualRequestApi));
        return exactRequestAddress;
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
        private final String requestKey;
        private final String requestApi;
        /**
         * One-based invocation ordinal in this selector's stable runtime
         * scope.  This is planner evidence and is deliberately independent
         * of the trace occurrence id, which names evidence rather than a
         * replay counter.
         */
        private final int invocationOrdinal;
        /**
         * The baseline receiver was registered to the planned source.  A
         * replay receiver registration, when present, remains authoritative;
         * an unregistered reconstructed receiver may instead be attributed
         * by the exact inherited request context.
         */
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
                                    String requestKey, String requestApi,
                                    int invocationOrdinal,
                                    boolean registeredSourceAnchor,
                                    boolean inheritedContextAnchor) {
            this.receiverScoped = receiverScoped;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = stableReplayThreadContext(threadName);
            this.sourceKey = safe(sourceKey);
            this.requestKey = safe(requestKey);
            this.requestApi = safe(requestApi);
            this.invocationOrdinal = invocationOrdinal;
            this.registeredSourceAnchor = registeredSourceAnchor;
            this.inheritedContextAnchor = inheritedContextAnchor;
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = optionalString(selector, "kind");
            boolean global = "GLOBAL_INVOCATION".equals(kind);
            String receiverClass = optionalString(selector, "receiverClass");
            String thread = selector.has("thread")
                    ? optionalString(selector, "thread") : "";
            JsonObject anchor = object(selector, "causalAnchor");
            String sourceKey = optionalString(anchor, "sourceKey");
            String requestKey = optionalString(anchor, "requestKey");
            String requestApi = optionalString(anchor, "requestApi");
            int invocationOrdinal = optionalInteger(selector,
                    "invocationOrdinal", -1);
            String anchorKind = optionalString(anchor, "kind");
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
                    || !sourceKey.equals(sourceKey.trim())
                    || invocationOrdinal < 1) {
                throw new IllegalArgumentException(
                        "rootSelector requires an exact receiver context and "
                                + "a causal anchor naming its source and a "
                                + "positive invocationOrdinal");
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
                    sourceKey, requestKey, requestApi, invocationOrdinal,
                    registeredSource,
                    inheritedContext);
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
            StringBuilder description = new StringBuilder(sourceKey);
            if (!requestKey.isEmpty()) {
                description.append("/requestKey=").append(requestKey);
            }
            if (!requestApi.isEmpty()) {
                description.append("/requestApi=").append(requestApi);
            }
            description.append("/invocation=").append(invocationOrdinal);
            return description.toString();
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
                        optionalString(predicate, "kind"))) {
                    return invalid("predicate kind must be exact runtime type");
                }
                int index = optionalInteger(predicate, "argumentIndex", -1);
                String runtimeType = optionalString(predicate, "runtimeType");
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

    private static final class RuntimeTask {
        private final String taskId;
        private final String instrumentationSelector;
        private final String regionId;
        /** The activation this task is. */
        private final String sourceKey;
        private final String occurrenceId;
        private final String rootMethod;
        private final RootContextSelector rootContextSelector;
        /** Argument predicates evaluated at the enclosing method entry. */
        private final RootArgumentSelector enclosingRootArgumentSelector;
        private final RootArgumentSelector rootArgumentSelector;
        /** Actions that execute directly at ordinary instrumentation hooks. */
        private final List<SymbolizeAction> symbolize;
        private final Map<String, String> branchPolicies;
        private final Set<String> replayLoopExitSites;
        private final LoopBoundPolicy loopBound;
        private final List<ModelAssignment> modelAssignments;
        private final List<GuardedReadAssignment> guardedReadAssignments;
        private final boolean capturesTargetReach;
        /** Whether this non-loop address has already completed its goal. */
        private volatile boolean completedGoalReserved;
        /**
         * Result rows this address has published in this replay.
         *
         * <p>Every admitted activation that reaches a terminal is its own
         * occurrence. This counts them so each row can name which one it is;
         * non-loop admission stops after its goal has completed.</p>
         */
        private int publishedActivations;
        /**
         * Whether this region is rooted on a bounded loop body.  Its published
         * occurrence set is unrolled at most {@code loopBound
         * .maxBackedgeTraversals()} (K_L) times, exactly as an inner bounded
         * loop is: the iterations past K_L run concretely and capture nothing.
         */
        private final boolean loopBodyRoot;
        private final String rootLoopMethod;
        private final int rootLoopHeaderUnitIndex;
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
        /** Stable identity shared by every task in one linked replay. */
        private final String replayGroupId;
        private final String linkedReplayRole;
        private final String familySnapshotDigest;
        private final String topologyEpoch;
        private final BranchReplayContract.RuntimeSchedule replayContract;
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
        /** Exact consumer occurrence of each protocol value this task sends. */
        private final Map<String, String> exportConsumerOccurrenceByPort =
                new LinkedHashMap<>();
        /** OUT ports allowed to establish an otherwise absent producer source. */
        private final Set<String> deferredOutgoingSourcePorts =
                new LinkedHashSet<>();
        /** OUT ports backed by one exact traced exchange in this task row. */
        private final Set<String> exactOutgoingSourceCandidatePorts =
                new LinkedHashSet<>();
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
            this.sourceKey = task.sourceKey();
            this.occurrenceId = task.occurrenceId();
            this.rootMethod = task.rootMethod();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            this.enclosingRootArgumentSelector =
                    RootArgumentSelector.from(rootSelector);
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
            this.symbolize = new ArrayList<>();
            this.branchPolicies = new LinkedHashMap<>();
            this.replayLoopExitSites = task.loopExitSites();
            this.loopBound = task.loopBound();
            this.loopBodyRoot = LoopBoundPolicy.LOOP_BODY_ROOT.equals(
                    task.rootAuthority());
            this.rootLoopMethod = task.rootLoopMethod();
            this.rootLoopHeaderUnitIndex = task.rootLoopHeaderUnitIndex();
            // The root loop's declared K_L (its loopSiteId is the key its
            // bound is under); an undeclared site inherits the default.
            this.loopOccurrenceBudget = this.loopBound
                    .maxBackedgeTraversals(task.rootLoopSiteId());
            this.modelAssignments = new ArrayList<>();
            this.guardedReadAssignments = new ArrayList<>();
            this.capturesTargetReach =
                    task.goalKind().capturesTargetReach();
            // The driver refuses a plan whose members name different
            // groups and then exports that same one id, so the two can only
            // disagree when the task states none: a seed plan, whose group
            // the invocation names.
            String plannedReplayGroup = optionalString(task.json(),
                    "linkedReplayGroupId");
            this.replayGroupId = plannedReplayGroup.isEmpty()
                    ? safe(System.getenv(REPLAY_GROUP_ENV))
                    : plannedReplayGroup;
            this.linkedReplayRole = optionalString(task.json(),
                    "linkedReplayRole");
            this.familySnapshotDigest = optionalString(task.json(),
                    "familySnapshotDigest");
            this.topologyEpoch = optionalString(task.json(), "topologyEpoch");
            this.edgeBindings = task.edgeBindings();
            indexPlannedReceiverObjectIds(task.inputActions().all());
            // The plan row decoded this catalog once; phase ids are already
            // one strict ordered ledger by then, so this is an index, not a
            // second admission.
            this.configuredSourcePhases = task.configuredSourcePhases();
            for (ConfiguredSourcePhaseContract.Occurrence phase
                    : configuredSourcePhases) {
                configuredSourcePhasesById.put(phase.phaseId(), phase);
            }
            this.replayContract = task.replaySchedule();
            JsonObject targetBranch = object(task.json(), "targetBranch");
            this.targetBranchSite = optionalString(targetBranch, "siteId");
            this.targetBranchOccurrence = optionalInteger(targetBranch,
                    "occurrence", -1);
            this.targetBranchRequiredOutcome = targetRequiredOutcome(
                    task.branches(), targetBranchSite,
                    targetBranchOccurrence);
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        optionalString(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
            }
            for (JsonElement element : task.branches()) {
                JsonObject branch = element.getAsJsonObject();
                String siteId = optionalString(branch, "siteId");
                branchPolicies.put(siteId, optionalString(branch, "policy"));
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
            Set<String> guardedReadIdentities = new LinkedHashSet<>();
            Set<String> guardedReadAnchors = new LinkedHashSet<>();
            for (JsonElement element : task.guardedReadAssignments()) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "guardedReadAssignments must contain objects in "
                                    + taskId);
                }
                GuardedReadAssignment assignment =
                        new GuardedReadAssignment(element.getAsJsonObject(),
                                occurrenceId);
                String anchor = assignment.consumerSiteId + "\n"
                        + assignment.consumerSiteOccurrence + "\n"
                        + assignment.declaringClass + "\n"
                        + assignment.fieldName + "\n"
                        + assignment.descriptor;
                if (!guardedReadIdentities.add(assignment.readIdentity)
                        || !guardedReadAnchors.add(anchor)) {
                    throw new IllegalArgumentException(
                            "guarded read assignments must have unique "
                                    + "identities and exact anchors in "
                                    + taskId);
                }
                guardedReadAssignments.add(assignment);
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
                        || assignment.hasContainerTarget()) {
                    throw new IllegalArgumentException(
                            "model assignment names an undeclared or "
                                    + "unsupported configured source in "
                                    + taskId + ": " + assignment.key);
                }
            }
            indexAttachProducerOccurrences(edgeBindings);
            indexExportConsumerOccurrences(edgeBindings);
            for (JsonElement element : task.sharedCarriers()) {
                if (element.isJsonObject()) {
                    sharedCarriers.add(new SharedCarrierRequest(
                            element.getAsJsonObject(), true));
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
         * <p>These are added beside the planner's carrier list because
         * explicit field declarations need not cover every planned carrier.
         * The planner owns their reconciliation.</p>
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
                sharedCarriers.add(new SharedCarrierRequest(
                        declaration, false));
            }
        }

        /** A selected shared read observes the VM carrier; it never mints. */
        private boolean observesSharedRead(String fieldSignature) {
            for (SharedCarrierRequest request : sharedCarriers) {
                if (request.observesSharedRead(fieldSignature)) return true;
            }
            return false;
        }

        /** Solver value for the one exact getfield this hook precedes. */
        private GuardedReadAssignment guardedReadAssignment(
                ConsumerAccessAnchor consumer, String fieldSignature) {
            DeclaredField field = FieldPathSpec.declaredField(fieldSignature);
            GuardedReadAssignment selected = null;
            for (GuardedReadAssignment candidate : guardedReadAssignments) {
                if (!candidate.matches(consumer, field)) continue;
                if (selected != null) {
                    throw new IllegalStateException(
                            "two guarded read assignments match "
                                    + consumer.siteId + " occurrence "
                                    + consumer.occurrence);
                }
                selected = candidate;
            }
            return selected;
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
                String producerOccurrence = "";
                for (JsonElement element : bindings) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!"RUNTIME_PROTOCOL_FLOW".equals(
                            optionalString(binding, "kind"))
                            || !portId.equals(optionalString(binding, "toInputPort"))) {
                        continue;
                    }
                    String receiver = PathObservation.plannedOccurrenceOf(
                            optionalString(binding, "toOccurrenceId"));
                    if (!occurrenceId.equals(receiver)) {
                        continue;
                    }
                    String candidate = PathObservation.plannedOccurrenceOf(
                            optionalString(binding, "fromOccurrenceId"));
                    if (candidate.isEmpty()) continue;
                    if (!producerOccurrence.isEmpty()
                            && !producerOccurrence.equals(candidate)) {
                        throw new IllegalArgumentException(
                                "communication attach port has two producer "
                                        + "occurrences in " + taskId + ": "
                                        + portId);
                    }
                    producerOccurrence = candidate;
                }
                if (!producerOccurrence.isEmpty()) {
                    attachProducerOccurrenceByPort.put(portId,
                            producerOccurrence);
                }
            }
        }

        private String attachProducerOccurrence(String portId) {
            return safe(attachProducerOccurrenceByPort.get(safe(portId)));
        }

        /** Indexes the exact consumer named by each outgoing protocol edge. */
        private void indexExportConsumerOccurrences(JsonArray bindings) {
            for (CommunicationHandoffSpec site
                    : communicationHandoffs.values()) {
                if (!site.outgoing()) continue;
                String portId = site.portId();
                String consumerOccurrence = "";
                boolean exactSourceCandidate = true;
                boolean found = false;
                for (JsonElement element : bindings) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!"RUNTIME_PROTOCOL_FLOW".equals(
                            optionalString(binding, "kind"))
                            || !portId.equals(
                            optionalString(binding, "fromOutputPort"))) {
                        continue;
                    }
                    String producer = PathObservation.plannedOccurrenceOf(
                            optionalString(binding, "fromOccurrenceId"));
                    if (!occurrenceId.equals(producer)) {
                        continue;
                    }
                    found = true;
                    if (!"TRACED_RPC_EXCHANGE_CORRELATION_V1".equals(
                            optionalString(binding, "correlationAuthority"))
                            || !rootContextSelector.requestKey.equals(
                            optionalString(binding, "requestKey"))
                            || !rootContextSelector.requestApi.equals(
                            optionalString(binding, "requestApi"))) {
                        exactSourceCandidate = false;
                    }
                    String candidate = PathObservation.plannedOccurrenceOf(
                            optionalString(binding, "toOccurrenceId"));
                    if (candidate.isEmpty()) continue;
                    if (!consumerOccurrence.isEmpty()
                            && !consumerOccurrence.equals(candidate)) {
                        throw new IllegalArgumentException(
                                "communication export port has two consumer "
                                        + "occurrences in " + taskId + ": "
                                        + portId);
                    }
                    consumerOccurrence = candidate;
                }
                if (!consumerOccurrence.isEmpty()) {
                    exportConsumerOccurrenceByPort.put(portId,
                            consumerOccurrence);
                    if (found && exactSourceCandidate) {
                        exactOutgoingSourceCandidatePorts.add(portId);
                    }
                }
            }
        }

        private String exportConsumerOccurrence(String portId) {
            return safe(exportConsumerOccurrenceByPort.get(safe(portId)));
        }

        private String outgoingSourceScope(String portId) {
            return rootMethod + '\n' + rootContextSelector.requestKey + '\n'
                    + rootContextSelector.requestApi + '\n' + safe(portId);
        }

        private Set<String> declaredOutgoingPorts() {
            Set<String> ports = new LinkedHashSet<>();
            for (CommunicationHandoffSpec handoff
                    : communicationHandoffs.values()) {
                if (handoff.outgoing()) ports.add(handoff.portId());
            }
            return ports;
        }

        private void indexPlannedReceiverObjectIds(JsonArray inputActions) {
            Map<String, Set<Long>> candidates = new LinkedHashMap<>();
            for (JsonElement element : inputActions) {
                if (!element.isJsonObject()) continue;
                JsonObject action = element.getAsJsonObject();
                long receiver = optionalLongInteger(action,
                        "fieldReceiverObjectId", 0L);
                DeclaredField field = FieldPathSpec.declaredField(
                        firstNonBlank(optionalString(action, "leafFieldSignature"),
                                optionalString(action, "accessFieldSignature")));
                if (field == null || receiver <= 0L) continue;
                candidates.computeIfAbsent(field.owner() + "#" + field.name(),
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

        /** Body entries this loop may run before the replay is cut. */
        private int maxLoopBodies(String loopId) {
            return LoopBoundPolicy.maxLoopBodies(false);
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

        /** Boundary-only loop controls advance replay invocation identity. */
        private boolean observesReplayBoundary(String siteId) {
            return replayLoopExitSites.contains(safe(siteId));
        }

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

        /** Every injected hook that belongs to one physical Java entry. */
        private String rootHookGroupKey() {
            // Source is resolved from runtime evidence by the dispatcher. If
            // it were part of this static hook group, the first hook for one
            // source could not dispatch a sibling task for another source at
            // the same region root.
            return (loopBodyRoot ? "LOOP\n" : "METHOD\n")
                    + regionId + "\n" + rootMethod
                    + (loopBodyRoot ? "\n" + rootLoopMethod + "\n"
                    + rootLoopHeaderUnitIndex : "");
        }

        /** All lightweight enclosing hooks physically share this method. */
        private String loopRootHookGroupKey() {
            return loopBodyRoot ? rootMethod : "";
        }

        /**
         * Counter scope frozen by the planner. Request-scoped activations are
         * counted inside their exact request; roots with no request anchor
         * retain the source-and-region scope used during discovery.
         */
        private String invocationCounterKey() {
            StringBuilder key = new StringBuilder(sourceKey)
                    .append('\n').append(regionId)
                    .append('\n').append(rootMethod)
                    .append('\n').append(rootContextSelector.requestKey)
                    .append('\n').append(rootContextSelector.requestApi);
            return key.toString();
        }

        /**
         * Selects a communication consumer by the message that invoked it.
         * Tasks with no planner-authored IN edge retain ordinal addressing.
         */
        private boolean acceptsRootInvocation(Integer actualOrdinal,
                                              boolean exactOutgoingAddress) {
            return rootInvocationAddressMatches(actualOrdinal,
                    rootContextSelector.invocationOrdinal,
                    attachProducerOccurrenceByPort, occurrenceId,
                    exactOutgoingAddress);
        }

        /**
         * Reserves completed evidence before reopening task admission.
         *
         * <p>Loop-body roots remain governed exclusively by K_L. Every
         * non-loop address denotes one dynamic occurrence and is complete
         * after its first full terminal result; targetReached:false is that
         * occurrence's seed case.</p>
         */
        private void reserveCompletedEvidence(boolean targetReached) {
            if (!loopBodyRoot) {
                completedGoalReserved = true;
            }
        }

        private boolean blocksAdmissionAfterCompletedGoal() {
            return completedGoalReserved;
        }

        /**
         * Whether this occurrence directly witnessed the selected failure
         * outcome, rather than merely deviating from its recorded seed path.
         */
        private boolean reachedRequiredTargetOutcome(JsonObject reach) {
            return declaresTargetBranch()
                    && reach != null
                    && targetBranchSite.equals(optionalString(reach, "siteId"))
                    && targetBranchOccurrence == optionalInteger(reach,
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
                if (!targetSite.equals(optionalString(branch, "siteId"))
                        || targetOccurrence != optionalInteger(branch,
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
        /** Next observed physical entry in each planner-authored scope. */
        private final Map<String, Integer> invocationOrdinals =
                new LinkedHashMap<>();
        /** Halt-status contribution of each task that has settled. */
        private final Map<String, Integer> settled = new LinkedHashMap<>();
        private boolean unansweredAddressesPublished;

        private Configuration(Path resultFile, List<RuntimeTask> tasks) {
            this.resultFile = resultFile;
            this.tasks = Collections.unmodifiableList(tasks);
            this.candidateLive = new boolean[tasks.size()];
            this.occurrenceClaimed = new boolean[tasks.size()];
            indexDeferredOutgoingSourceAnchors(tasks);
        }

        /**
         * Admits an OUT site as source evidence only when the frozen runtime
         * edges give that exact root/request/port scope one producer source.
         */
        private static void indexDeferredOutgoingSourceAnchors(
                List<RuntimeTask> tasks) {
            Map<String, Set<String>> sourcesByScope = new LinkedHashMap<>();
            for (RuntimeTask task : tasks) {
                // Include even malformed/unbound declarations in the
                // uniqueness denominator; they must make admission less
                // permissive, never disappear from the proof.
                for (String portId : task.declaredOutgoingPorts()) {
                    sourcesByScope.computeIfAbsent(
                            task.outgoingSourceScope(portId),
                            ignored -> new LinkedHashSet<>()).add(
                            task.sourceKey);
                }
            }
            for (RuntimeTask task : tasks) {
                Set<String> candidates =
                        task.exactOutgoingSourceCandidatePorts;
                if (candidates.isEmpty()
                        || !candidates.equals(task.declaredOutgoingPorts())
                        || !candidates.equals(
                        task.exportConsumerOccurrenceByPort.keySet())) {
                    continue;
                }
                boolean unique = true;
                for (String portId : candidates) {
                    Set<String> sources = sourcesByScope.get(
                            task.outgoingSourceScope(portId));
                    if (sources == null || sources.size() != 1
                            || !sources.contains(task.sourceKey)) {
                        unique = false;
                        break;
                    }
                }
                if (unique) {
                    task.deferredOutgoingSourcePorts.addAll(candidates);
                }
            }
        }

        /**
         * Releases the address of a candidate that ended without being the
         * occurrence, so the next compatible invocation may try for it.
         */
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

        /** Marks durable evidence without clearing a newer live candidate. */
        private synchronized void markOccurrenceClaimed(RuntimeTask task) {
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

        /**
         * Resolves an occurrence-specific instrumentation hook to the stable
         * region entry shared by every sibling hook at that Java method.
         */
        private synchronized RootHookGroup rootHookGroup(
                String instrumentationSelector, String rootMethod) {
            RuntimeTask selected = null;
            for (RuntimeTask task : tasks) {
                if (!task.instrumentationSelector.equals(
                        safe(instrumentationSelector))
                        || !sameRootMethod(task.rootMethod, rootMethod)) {
                    continue;
                }
                if (selected != null && !selected.rootHookGroupKey().equals(
                        task.rootHookGroupKey())) {
                    throw new IllegalStateException(
                            "instrumentation selector addresses multiple "
                                    + "root hook groups: "
                                    + safe(instrumentationSelector));
                }
                selected = task;
            }
            if (selected == null) {
                return new RootHookGroup("UNPLANNED\n"
                        + safe(instrumentationSelector) + "\n"
                        + safe(rootMethod), 1);
            }
            String key = selected.rootHookGroupKey();
            int hooks = 0;
            for (RuntimeTask task : tasks) {
                if (key.equals(task.rootHookGroupKey())) hooks++;
            }
            return new RootHookGroup(key, hooks);
        }

        /** Resolves one lightweight outer hook shared by loop-body tasks. */
        private synchronized RootHookGroup loopRootHookGroup(
                String instrumentationSelector, String rootMethod) {
            RuntimeTask selected = null;
            for (RuntimeTask task : tasks) {
                if (!task.loopBodyRoot
                        || !task.instrumentationSelector.equals(
                        safe(instrumentationSelector))
                        || !sameRootMethod(task.rootMethod, rootMethod)) {
                    continue;
                }
                selected = task;
                break;
            }
            if (selected == null) {
                return new RootHookGroup("UNPLANNED_LOOP_ROOT\n"
                        + safe(rootMethod), 1);
            }
            String key = selected.loopRootHookGroupKey();
            int hooks = 0;
            for (RuntimeTask task : tasks) {
                if (task.loopBodyRoot
                        && key.equals(task.loopRootHookGroupKey())) hooks++;
            }
            return new RootHookGroup(key, hooks);
        }

        /**
         * Counts one real enclosing method entry and freezes which loop task
         * owns all body iterations executed by that invocation.
         */
        private synchronized Set<String> addressLoopRootInvocation(
                String loopRootHookGroupKey, String rootMethod,
                Object receiver, Object[] rootArguments) {
            String threadName = Thread.currentThread().getName();
            SourceRef registeredReceiverSource =
                    RuntimeTraceContext.sourceFor(receiver);
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            Map<String, Integer> actualOrdinalByScope =
                    new LinkedHashMap<>();
            for (RuntimeTask task : tasks) {
                if (!task.loopBodyRoot
                        || !task.loopRootHookGroupKey().equals(
                        safe(loopRootHookGroupKey))
                        || !compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector,
                        task.enclosingRootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                String sourceMismatch = sourceAdmissionMismatch(task,
                        registeredReceiverSource, context);
                if (!sourceMismatch.isEmpty()) {
                    task.noteUnaddressedCandidate(sourceMismatch);
                    continue;
                }
                String requestMismatch = requestMismatch(task,
                        registeredReceiverSource, context);
                if (!requestMismatch.isEmpty()) {
                    task.noteUnaddressedCandidate(requestMismatch);
                    continue;
                }
                if (mayDeferMissingContextToOutgoingAnchor(task,
                        registeredReceiverSource, context)) {
                    continue;
                }
                String scope = task.invocationCounterKey();
                if (!actualOrdinalByScope.containsKey(scope)) {
                    int ordinal = invocationOrdinals.getOrDefault(scope, 0)
                            + 1;
                    invocationOrdinals.put(scope, ordinal);
                    actualOrdinalByScope.put(scope, ordinal);
                }
            }
            Set<String> admitted = new LinkedHashSet<>();
            for (RuntimeTask task : tasks) {
                if (!task.loopBodyRoot
                        || !task.loopRootHookGroupKey().equals(
                        safe(loopRootHookGroupKey))
                        || !compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector,
                        task.enclosingRootArgumentSelector,
                        receiver, rootArguments, threadName)
                        || !sourceAdmissionMismatch(task,
                        registeredReceiverSource,
                        context).isEmpty()
                        || !requestMismatch(task, registeredReceiverSource,
                        context).isEmpty()) {
                    continue;
                }
                Integer ordinal = actualOrdinalByScope.get(
                        task.invocationCounterKey());
                boolean exactOutgoingAddress =
                        mayDeferMissingContextToOutgoingAnchor(task,
                                registeredReceiverSource, context);
                if (!task.acceptsRootInvocation(ordinal,
                        exactOutgoingAddress)) {
                    if (task.attachProducerOccurrenceByPort.isEmpty()) {
                        task.noteUnaddressedCandidate(
                                "matching enclosing root was invocation "
                                        + ordinal + " instead of "
                                        + task.rootContextSelector
                                        .invocationOrdinal);
                    } else {
                        task.noteUnaddressedCandidate(
                                "matching enclosing root carried no selected "
                                        + "communication producer");
                    }
                    continue;
                }
                admitted.add(task.taskId);
            }
            return admitted;
        }

        /** Claims at most one open task for this root invocation. */
        private synchronized RuntimeTask select(String rootHookGroupKey,
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
            Map<String, Integer> actualOrdinalByScope =
                    new LinkedHashMap<>();

            // Count this physical entry once in every matching stable scope.
            // This pass deliberately ignores task completion and candidate
            // ownership: later planned ordinals must still see entries that
            // an earlier task already consumed.
            for (RuntimeTask task : tasks) {
                if (task.loopBodyRoot
                        || !task.rootHookGroupKey().equals(
                        safe(rootHookGroupKey))
                        || !compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector, task.rootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                String sourceMismatch = sourceAdmissionMismatch(task,
                        registeredReceiverSource, context);
                if (!sourceMismatch.isEmpty()) {
                    task.noteUnaddressedCandidate(sourceMismatch);
                    continue;
                }
                String requestMismatch = requestMismatch(task,
                        registeredReceiverSource, context);
                if (!requestMismatch.isEmpty()) {
                    task.noteUnaddressedCandidate(requestMismatch);
                    continue;
                }
                if (mayDeferMissingContextToOutgoingAnchor(task,
                        registeredReceiverSource, context)) {
                    continue;
                }
                String scope = task.invocationCounterKey();
                if (!actualOrdinalByScope.containsKey(scope)) {
                    int ordinal = invocationOrdinals.getOrDefault(scope, 0)
                            + 1;
                    invocationOrdinals.put(scope, ordinal);
                    actualOrdinalByScope.put(scope, ordinal);
                }
            }

            for (int index = 0; index < tasks.size(); index++) {
                RuntimeTask task = tasks.get(index);
                if (!task.rootHookGroupKey().equals(
                        safe(rootHookGroupKey))) continue;
                if (task.blocksAdmissionAfterCompletedGoal()) continue;
                if (task.loopBodyRoot) {
                    if (!enclosingLoopRootAdmits(task)
                            || candidateLive[index]) {
                        continue;
                    }
                    candidateLive[index] = true;
                    return task;
                }
                if (!compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector, task.rootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                if (!sourceAdmissionMismatch(task, registeredReceiverSource,
                        context).isEmpty()
                        || !requestMismatch(task, registeredReceiverSource,
                        context).isEmpty()) continue;
                Integer actualOrdinal = actualOrdinalByScope.get(
                        task.invocationCounterKey());
                boolean exactOutgoingAddress =
                        mayDeferMissingContextToOutgoingAnchor(task,
                                registeredReceiverSource, context);
                if (!task.acceptsRootInvocation(actualOrdinal,
                        exactOutgoingAddress)) {
                    continue;
                }
                if (candidateLive[index]) continue;
                candidateLive[index] = true;
                return task;
            }
            return null;
        }

        private static String requestMismatch(
                RuntimeTask task, SourceRef registeredReceiverSource,
                RuntimeTraceContext.View context) {
            RootContextSelector selector = task.rootContextSelector;
            if (!selector.requestKey.equals(safe(context.requestKey))) {
                return "matching root entered request "
                        + safe(context.requestKey) + " instead of "
                        + selector.requestKey;
            }
            if (!selector.requestApi.equals(safe(context.requestApi))) {
                return "matching root entered request API "
                        + safe(context.requestApi) + " instead of "
                        + selector.requestApi;
            }
            return "";
        }

        /** Entry admission may defer only missing producer context to OUT. */
        private static String sourceAdmissionMismatch(
                RuntimeTask task, SourceRef registeredReceiverSource,
                RuntimeTraceContext.View context) {
            String mismatch = sourceMismatch(task, registeredReceiverSource,
                    context);
            return mismatch.isEmpty()
                    || mayDeferMissingContextToOutgoingAnchor(
                    task, registeredReceiverSource, context) ? "" : mismatch;
        }

        private static boolean mayDeferMissingContextToOutgoingAnchor(
                RuntimeTask task, SourceRef registeredReceiverSource,
                RuntimeTraceContext.View context) {
            RootContextSelector selector = task.rootContextSelector;
            return outgoingProducerMayDeferMissingContext(
                    !task.deferredOutgoingSourcePorts.isEmpty(),
                    registeredReceiverSource, context.source, task.sourceKey,
                    selector.requestKey, selector.requestApi,
                    context.requestKey, context.requestApi);
        }

        /** Empty only when entry-time runtime evidence names this source. */
        private static String sourceMismatch(
                RuntimeTask task, SourceRef registeredReceiverSource,
                RuntimeTraceContext.View context) {
            RootContextSelector selector = task.rootContextSelector;
            SourceRef inherited = context.source;
            boolean receiverMatches = registeredReceiverSource != null
                    && RuntimeTraceContext.sameSourceIdentity(task.sourceKey,
                    registeredReceiverSource.key());
            boolean inheritedMatches = inherited != null
                    && RuntimeTraceContext.sameSourceIdentity(task.sourceKey,
                    inherited.key());
            boolean messageAddressed = inboundMessageAddressMatches(
                    task.attachProducerOccurrenceByPort,
                    task.occurrenceId);
            if (messageAddressed) {
                if (!inboundMessageSourceEvidence(task.sourceKey,
                        registeredReceiverSource, true).isEmpty()) {
                    return "";
                }
                return "matching root receiver belonged to "
                        + registeredReceiverSource.key() + " instead of "
                        + task.sourceKey;
            }
            if (OccurrenceMinter.UNREGISTERED_SOURCE_KEY.equals(
                    task.sourceKey)) {
                return registeredReceiverSource == null && inherited == null
                        ? "" : "matching root carried a registered source "
                        + (registeredReceiverSource == null
                        ? inherited.key() : registeredReceiverSource.key())
                        + " instead of the unregistered source";
            }
            if (selector.inheritedContextAnchor) {
                if (!inheritedMatches) {
                    return inherited == null
                            ? "matching root inherited no source; its anchor "
                            + "names " + task.sourceKey
                            : "matching root inherited " + inherited.key()
                            + " instead of " + task.sourceKey;
                }
                if (registeredReceiverSource != null && !receiverMatches) {
                    return "matching root receiver belonged to "
                            + registeredReceiverSource.key() + " instead of "
                            + task.sourceKey;
                }
                return "";
            }
            if (selector.registeredSourceAnchor) {
                // A replay can reconstruct the logical receiver without
                // repeating its identity-map alias registration.  In that
                // case the exact inherited request context is still positive
                // source evidence.  Never let it override an explicit,
                // conflicting receiver registration.
                if (registeredSourceAnchorMatches(task.sourceKey,
                        registeredReceiverSource, inherited)) {
                    return "";
                }
                if (registeredReceiverSource != null) {
                    return "matching root receiver belonged to "
                        + registeredReceiverSource.key() + " instead of "
                        + task.sourceKey;
                }
                return inherited == null
                        ? "matching root receiver had no registered source "
                        + "and inherited no source; its anchor names "
                        + task.sourceKey
                        : "matching root receiver had no registered source "
                        + "and inherited " + inherited.key()
                        + " instead of " + task.sourceKey;
            }
            return receiverMatches || inheritedMatches ? ""
                    : "matching root carried no evidence for source "
                    + task.sourceKey;
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
        private Method currentRegionEnterEventId;
        private Method symbolizeWithPrefix;
        private Method symbolizeField;
        private Method symbolizeExactField;
        private Method trackContainer;
        private Method getExpression;
        private Method getFieldExpression;
        private Method finishRegion;
        private Method pausePathCondition;
        private Method resumePathCondition;
        private Method getBranchEvents;
        private Method cleanupEnd;
        private Method export;
        private Method attach;
        private Method range;
        private Method selectField;
        private Method armPrimitiveFieldRead;
        private Method confirmPrimitiveFieldRead;
        private Method selectElement;
        private Method selectMap;
        private Method fieldVersions;
        private Method elementVersions;
        private Method mapVersions;

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

        private long currentRegionEnterEventId() throws Exception {
            Object value = currentRegionEnterEventId.invoke(null);
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

        /** Exports one field and reports its session-unique endpoint id. */
        private long exportExpression(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long[] eventOut) throws Exception {
            Object handle = export.invoke(null, owner, declaringClass,
                    fieldName, descriptor, eventOut);
            return handle instanceof Number
                    ? ((Number) handle).longValue() : 0L;
        }

        /**
         * Attaches one live handle. The return value identifies the export;
         * {@code eventOut} receives this attach's session-unique endpoint id.
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

        /** Arms the concrete operand of the immediately following getfield. */
        private long armSharedPrimitiveFieldRead(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long valueBits) throws Exception {
            Object status = armPrimitiveFieldRead.invoke(null, owner,
                    declaringClass, fieldName, descriptor, valueBits);
            return status instanceof Number
                    ? ((Number) status).longValue() : Long.MIN_VALUE;
        }

        /** Consumes the VM's receipt for one armed concrete field operand. */
        private long confirmSharedPrimitiveFieldRead(long token)
                throws Exception {
            Object status = confirmPrimitiveFieldRead.invoke(null, token);
            return status instanceof Number
                    ? ((Number) status).longValue() : Long.MIN_VALUE;
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
            api.currentRegionEnterEventId = method(system,
                    "getCurrentConcolicRegionEnterEventId");
            api.symbolizeWithPrefix = method(system, "symbolize",
                    Object.class, String.class);
            api.symbolizeField = method(system, "symbolizeField",
                    Object.class, String.class, String.class);
            api.symbolizeExactField = method(system, "symbolizeExactField",
                    Object.class, String.class, String.class, String.class,
                    String.class);
            api.trackContainer = method(system, "trackContainerExpression",
                    Object.class, String.class);
            api.getExpression = method(system, "getSymbolicExpression",
                    Object.class);
            api.getFieldExpression = method(system,
                    "getSymbolicFieldExpression", Object.class, String.class,
                    String.class, String.class, Object.class);
            api.finishRegion = method(system, "finishConcolicRegion");
            api.pausePathCondition =
                    method(system, "pauseConcolicPathCondition");
            api.resumePathCondition =
                    method(system, "resumeConcolicPathCondition");
            api.getBranchEvents = method(system, "getConcolicBranchEvents");
            api.cleanupEnd = method(system, "endConcolic");
            api.export = method(system, "exportExpression", Object.class,
                    String.class, String.class, String.class, long[].class);
            api.attach = method(system, "attachExpression", Object.class,
                    String.class, String.class, String.class, long.class,
                    long[].class);
            api.range = method(system, "getConcolicPathConditionRange",
                    int.class, int.class);
            api.selectField = method(system, "selectSharedFieldCarrier",
                    Object.class, String.class, String.class, String.class);
            api.armPrimitiveFieldRead = method(system,
                    "armSharedPrimitiveFieldRead", Object.class,
                    String.class, String.class, String.class, long.class);
            api.confirmPrimitiveFieldRead = method(system,
                    "confirmSharedPrimitiveFieldRead", long.class);
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
