package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
import edu.uva.liftlab.graphchecker.concolic.ExactConcreteBranchObservation;
import edu.uva.liftlab.graphchecker.concolic.SmtModelValueCodec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;

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
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
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
 * GraphChecker itself remains buildable and testable on an ordinary JDK.  On
 * the concolic OpenJDK, one compatible activation is selected, its live-in objects are
 * symbolized, and the region summary is persisted before the VM destroys its
 * symbolic thread context.</p>
 */
public final class ConcolicRegionRuntime {
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
    /** Guarded by {@link #ENGINE_LOCK}. */
    private static int resultPublicationsInFlight;
    private static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    private static final AtomicBoolean ENGINE_BUSY = new AtomicBoolean();
    private static final Object ENGINE_LOCK = new Object();
    /**
     * How long a region root waits for a concurrent activation to release the
     * single symbolic engine before it gives up.  Zero disables waiting.
     */
    static final String ENGINE_WAIT_PROPERTY =
            "causynth.concolic.engine.wait.millis";
    static final String HALT_AFTER_SELECTED_RESULT_PROPERTY =
            "causynth.concolic.halt.after.selected.result";
    static final long DEFAULT_ENGINE_WAIT_MILLIS = 60_000L;
    static final String ENGINE_BUSY_TIMEOUT =
            "ENGINE_BUSY_TIMEOUT: another concolic region held the symbolic "
                    + "engine for the whole wait budget";
    static final String ENGINE_BUSY_INTERRUPTED =
            "ENGINE_BUSY_INTERRUPTED: waiting for the symbolic engine was "
                    + "interrupted";
    /**
     * Why an activation never published a region result.  A skip that never
     * got the engine and a skip that ran and contradicted its recording are
     * different findings, and collapsing them makes a scheduling artifact
     * indistinguishable from an infeasible path.
     */
    static final String SKIP_ENGINE_UNAVAILABLE = "ENGINE_UNAVAILABLE";
    static final String SKIP_NOT_STARTED = "NOT_STARTED";
    static final String SKIP_REPLAY_PREFIX_UNMATCHED =
            "REPLAY_PREFIX_UNMATCHED";
    static final String SKIP_SEED_OUTCOME_CONFLICT = "SEED_OUTCOME_CONFLICT";
    static final String SKIP_INCOMPLETE_OUTPUT_RELATION =
            "INCOMPLETE_OUTPUT_RELATION";
    /**
     * Candidate order for the single symbolic engine.  A recorded entry value
     * is compared value-wise, which cannot decide whether an activation walks
     * the recorded path, so it only ranks candidates; the recorded branch
     * prefix is the sole judgement that refuses one.
     */
    static final int ENTRY_STATE_RANK_MATCHES = 0;
    static final int ENTRY_STATE_RANK_UNDECIDED = 1;
    static final int ENTRY_STATE_RANK_MISMATCH = 2;
    private static final int ENTRY_STATE_RANKS = 3;
    /** Waiting candidates per rank; guarded by {@link #ENGINE_LOCK}. */
    private static final int[] ENGINE_WAITING = new int[ENTRY_STATE_RANKS];
    /**
     * Emits one line per replay milestone to stderr. Long-lived roots make a
     * stalled activation indistinguishable from a slow one; this trace names
     * which hook the replay is inside and how large the accumulated path
     * condition it must re-read has become.
     */
    static final String DIAGNOSTICS_PROPERTY =
            "causynth.concolic.diagnostics";
    private static volatile Boolean diagnostics;
    private static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    private static final ThreadLocal<Long> CURRENT_TOKEN = new ThreadLocal<>();
    /**
     * Dynamic root-invocation ownership used only by injected entry/exit
     * hooks.  Every injected root invocation owns a frame once its wrapper
     * begins, including failed or unselected entries whose token stays zero.
     * Keeping this separate from {@link #CURRENT_TOKEN} prevents any nested
     * invocation from closing its selected caller.
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

    private ConcolicRegionRuntime() {
    }

    /**
     * Copies a Gson tree without linking against Gson's newer tree-copy
     * methods. Application classpaths can provide an older Gson at runtime;
     * a JSON round trip preserves the value and gives callers an independently
     * mutable result across the supported versions.
     */
    @SuppressWarnings("unchecked")
    static <T extends JsonElement> T copyJsonTree(T source) {
        if (source == null) return null;
        return (T) new JsonParser().parse(GSON.toJson(source));
    }

    /**
     * Starts an observation-only subtree before an instrumented method calls
     * back into this runtime. Soot emits this boundary in the analyzed method
     * so runtime/Gson frames are entered while symbolic propagation is muted.
     * The VM still keeps structural shadow frames balanced.
     */
    public static void pauseObservation() {
        try {
            engine().pausePathCondition();
        } catch (Throwable ignored) {
            // A missing/inactive engine is already handled by the region hook.
        }
    }

    /** Completes the observation-only subtree started by {@link #pauseObservation()}. */
    public static void resumeObservation() {
        try {
            engine().resumePathCondition();
        } catch (Throwable ignored) {
            // Resume is intentionally harmless when no region is active.
        }
    }

    /**
     * Accounts for one attempted traversal of an instrumented normal CFG
     * backedge. Calls outside the selected active region are deliberately a
     * no-op. All map and policy operations execute while VM path-condition
     * recording is paused, so this synthetic guard cannot become a symbolic
     * branch event of the program under test.
     *
     * <p>The fixed bound allows exactly {@code K} loop-body iterations. The
     * first body precedes any backedge, so only attempts {@code 1..K-1} may
     * complete. Backedge attempt {@code K}, made after body {@code K}, throws
     * a dedicated {@link Error} before body {@code K+1} can begin. The root
     * catch-all records it as a path cut rather than fabricating a normal loop
     * exit.</p>
     */
    public static void checkLoopBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        ActiveRegion active = activeRegion();
        if (active == null) return;

        EngineApi api = engine();
        boolean paused = false;
        LoopBoundCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            String edge = safe(backedgeId);
            int runtimeMax = active.activation.loopBound
                    .maxBackedgeTraversals();
            if (edge.isEmpty()
                    || instrumentedMaxTraversals != runtimeMax) {
                cut = active.loopBoundCut(edge, runtimeMax, 0L,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            } else {
                long attempted = active.loopBackedges
                        .recordTraversal(active.loopBudgetKey(edge));
                if (attempted >= runtimeMax) {
                    cut = active.loopBoundCut(edge, runtimeMax, attempted,
                            "MAX_LOOP_BODY_ITERATIONS_REACHED");
                }
            }
        } catch (Throwable failure) {
            cut = active.loopBoundCut(safe(backedgeId),
                    active.activation.loopBound.maxBackedgeTraversals(),
                    0L, "BOUND_HOOK_FAILURE:" + rootCause(failure));
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
                                active.activation.loopBound
                                        .maxBackedgeTraversals(),
                                0L, "BOUND_HOOK_RESUME_FAILURE");
                    }
                }
            }
        }
        // A loop cut is the end of this bounded execution path, even if
        // application code catches Error/Throwable above the loop.
        throwCut(active, cut);
    }

    /**
     * Records a guarded loop's completed latch transfer without cutting at
     * the header.  The separate body-entry hook can then let a false header
     * guard exit normally after exactly {@code K} bodies, while rejecting a
     * true guard before body {@code K+1} starts.
     */
    public static void recordLoopBackedge(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = activeRegion();
        if (active == null) return;

        EngineApi api = engine();
        boolean paused = false;
        LoopBoundCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            String loop = safe(loopId);
            int runtimeMax = active.activation.loopBound
                    .maxBackedgeTraversals();
            if (loop.isEmpty()
                    || instrumentedMaxTraversals != runtimeMax) {
                cut = active.loopBoundCut(loop, runtimeMax, 0L,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            } else {
                String budgetLoop = active.loopBudgetKey(loop);
                long completed = active.loopBackedges
                        .recordGuardedTraversal(budgetLoop);
                if (completed > runtimeMax) {
                    cut = active.loopBoundCut(loop, runtimeMax, completed,
                            "LOOP_BODY_ENTRY_HOOK_MISSING");
                }
            }
        } catch (Throwable failure) {
            cut = active.loopBoundCut(safe(loopId),
                    active.activation.loopBound.maxBackedgeTraversals(),
                    0L, "BOUND_HOOK_FAILURE:" + rootCause(failure));
        } finally {
            if (paused) {
                try {
                    api.resumePathCondition();
                } catch (Throwable failure) {
                    active.addUnresolvedOnce(
                            "loop-bound path-condition resume failed: "
                                    + rootCause(failure));
                    if (cut == null) {
                        cut = active.loopBoundCut(safe(loopId),
                                active.activation.loopBound
                                        .maxBackedgeTraversals(),
                                0L, "BOUND_HOOK_RESUME_FAILURE");
                    }
                }
            }
        }
        throwCut(active, cut);
    }

    /**
     * Charges one loop body to the replay resource cap without consulting the
     * unroll bound.
     *
     * <p>Emitted at every loop on the replay path, including the service
     * loops of a long-lived root that no bounded-semantics loop hook covers.
     * Such a loop is not part of the path space the solver reasons about, so
     * it must not spend the unroll budget; what it does spend is the replay's
     * ability to finish, and that is what this hook accounts for.</p>
     */
    public static void checkReplayLoopBody(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = activeRegion();
        if (active == null) return;

        EngineApi api = engine();
        boolean paused = false;
        ReplayLoopResourceCut cut = null;
        try {
            api.pausePathCondition();
            paused = true;
            // This cap counts bodies per loop, so a body-entry edge that also
            // names its guard still spends one ledger.
            String loop = loopIdentity(loopId);
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
        throwCut(active, cut);
    }

    /** Rejects only a transition that would enter body {@code K+1}. */
    public static void checkLoopBodyEntry(
            String loopId, int instrumentedMaxTraversals) {
        ActiveRegion active = activeRegion();
        if (active == null) return;

        EngineApi api = engine();
        boolean paused = false;
        LoopBoundCut cut = null;
        ReplayLoopResourceCut resourceCut = null;
        try {
            api.pausePathCondition();
            paused = true;
            // The edge names the loop it belongs to and the guard that
            // decides this body; the ledger is the loop's alone.
            String loop = loopIdentity(loopId);
            String guardSite = bodyEntryGuardSite(loopId);
            String budgetLoop = active.loopBudgetKey(loop);
            int runtimeMax = active.activation.loopBound
                    .maxBackedgeTraversals();
            diag("LOOP_BODY_ENTRY", loop + " guard=" + guardSite
                    + " charged=" + active.loopBackedges.completed(
                    budgetLoop));
            // Every body spends the replay resource cap, whatever the unroll
            // bound then decides about this one.
            resourceCut = active.chargeLoopBody(loop);
            if (loop.isEmpty()
                    || instrumentedMaxTraversals != runtimeMax) {
                cut = active.loopBoundCut(loop, runtimeMax, 0L,
                        "INSTRUMENTATION_POLICY_MISMATCH");
            } else if (active.enteredBodyOnConcreteGuard(loop, guardSite)) {
                // The unroll bound exists to cap path explosion, which only a
                // symbolically decided continuation can cause.  How often a
                // fully concrete guard repeats is data this replay observes,
                // not a branch it chooses, so it must not spend the budget
                // the symbolic loops in the same activation need.  The
                // symbolic surface stays capped by the container snapshot
                // capacity, and the latch already charged this traversal.
                active.loopBackedges.releaseTraversal(budgetLoop);
            } else if (!active.loopBackedges.canEnterBody(budgetLoop)) {
                cut = active.loopBoundCut(loop, runtimeMax,
                        (long) active.loopBackedges.completed(budgetLoop)
                                + 1L,
                        "MAX_LOOP_BODY_ITERATIONS_REACHED");
            }
        } catch (Throwable failure) {
            cut = active.loopBoundCut(safe(loopId),
                    active.activation.loopBound.maxBackedgeTraversals(),
                    0L, "BOUND_HOOK_FAILURE:" + rootCause(failure));
        } finally {
            if (paused) {
                try {
                    api.resumePathCondition();
                } catch (Throwable failure) {
                    active.addUnresolvedOnce(
                            "loop-bound path-condition resume failed: "
                                    + rootCause(failure));
                    if (cut == null) {
                        cut = active.loopBoundCut(safe(loopId),
                                active.activation.loopBound
                                        .maxBackedgeTraversals(),
                                0L, "BOUND_HOOK_RESUME_FAILURE");
                    }
                }
            }
        }
        // The resource cap outranks the unroll bound: a replay that cannot be
        // carried far enough has no bounded path left to report.
        throwCut(active, resourceCut);
        throwCut(active, cut);
    }

    /** Publishing any cut ends the region as CUT before it is rethrown. */
    private static void throwCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        finish(active.token, "CUT", "", null);
        throw cut;
    }

    /**
     * Opens the exact accessor invocation selected by one activation's
     * symbolize action. Unlike the general runtime recorder this hook emits
     * no trace events: it only retains the caller-site identity and invocation
     * receiver on the current concolic thread until the matching exit hook
     * executes.
     *
     * <p>A zero return means that no selected region is active on this
     * thread. Soot initializes the token to zero and always invokes the exit
     * hook, so disabled and unselected executions remain harmless.</p>
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
                // A context may never cross a region activation. Clearing a
                // stale stack is fail-closed and prevents an old receiver
                // from authorizing a field read in the new activation.
                CURRENT_ACCESSOR_CALL_CONTEXT.remove();
                previous = null;
            }
            long contextToken = ACCESSOR_CONTEXT_TOKEN_COUNTER
                    .incrementAndGet();
            int occurrence = active.nextAccessorCallOccurrence(caller, site,
                    callee);
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
            // exceptional edge. If the token belongs to this stack, discard
            // the whole stack instead of exposing a stale outer context.
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
        synchronized (CONFIG_LOCK) {
            configuration = null;
            engineApi = null;
        }
        ACTIVE.clear();
        CURRENT_TOKEN.remove();
        ROOT_INVOCATION_FRAMES.remove();
        CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        synchronized (ENGINE_LOCK) {
            resultPublicationsInFlight = 0;
            ENGINE_LOCK.notifyAll();
        }
        releaseSymbolicEngine();
    }

    /**
     * Waits until every selected activation already publishing a result has
     * either durably closed its JSONL record or reported a write failure.
     * Process launchers call this before forcibly terminating leaked system
     * threads; otherwise a concurrent {@link #finish} can be killed between
     * writing a large JSON object and its closing brace/newline.
     */
    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        synchronized (ENGINE_LOCK) {
            // ENGINE_BUSY covers the narrow interval after a selected
            // activation is ACTIVE but before finish registers publication.
            // Once finish releases the engine, the publication counter keeps
            // the barrier closed through the durable append.
            while (ENGINE_BUSY.get() || resultPublicationsInFlight > 0) {
                try {
                    ENGINE_LOCK.wait();
                } catch (InterruptedException ignored) {
                    interrupted = true;
                }
            }
        }
        if (interrupted) Thread.currentThread().interrupt();
    }

    static void beginSelectedResultPublication() {
        synchronized (ENGINE_LOCK) {
            resultPublicationsInFlight++;
            ENGINE_LOCK.notifyAll();
        }
    }

    static void endSelectedResultPublication() {
        synchronized (ENGINE_LOCK) {
            if (resultPublicationsInFlight <= 0) {
                throw new IllegalStateException(
                        "selected result publication underflow");
            }
            resultPublicationsInFlight--;
            ENGINE_LOCK.notifyAll();
        }
    }

    /** Test seam for the bounded symbolic-engine reservation. */
    static String reserveSymbolicEngineForTests() {
        return reserveSymbolicEngine(ENTRY_STATE_RANK_UNDECIDED);
    }

    /** Test seam for the ranked reservation. */
    static String reserveSymbolicEngineForTests(int entryStateRank) {
        return reserveSymbolicEngine(entryStateRank);
    }

    /** Test seam releasing the reservation taken above. */
    static void releaseSymbolicEngineForTests() {
        releaseSymbolicEngine();
    }

    /**
     * Called at a statically selected same-thread region root with its actual
     * reference arguments.  Primitive parameter slots are null.
     */
    public static long enterRegion(String rootMethod, Object receiver,
                                   Object[] rootArguments) {
        Configuration config = configuration();
        if (config.task == null || rootMethod == null) {
            return 0L;
        }
        RuntimeTask activation = config.select(rootMethod, receiver,
                rootArguments);
        if (activation == null) {
            return 0L;
        }
        return startSymbolicRegion(activation, receiver,
                activation.observedEntryStateRank(receiver));
    }

    private static long startSymbolicRegion(RuntimeTask activation,
                                            Object receiver,
                                            int entryStateRank) {
        String contention = reserveSymbolicEngine(entryStateRank);
        if (!contention.isEmpty()) {
            writeSkipped(activation, SKIP_ENGINE_UNAVAILABLE, contention);
            return 0L;
        }

        EngineApi api = engine();
        if (!api.available()) {
            releaseSymbolicEngine();
            writeSkipped(activation, SKIP_NOT_STARTED,
                    "custom concolic System API is unavailable");
            return 0L;
        }
        boolean engineStarted = false;
        boolean pathConditionPaused = false;
        long token = 0L;
        try {
            api.start(activation.regionId, activation.taskId);
            engineStarted = true;
            // Region setup performs reflection, collection lookups and
            // JSON-safe bookkeeping. Explicit native symbolize calls
            // temporarily drain this pause depth around the initializer.
            // Do not keep the VM paused across the concrete prefix: Zero
            // decides whether a newly entered Java frame can propagate
            // symbolic state when that frame is pushed. A frame entered while
            // paused cannot be made tracking retroactively when the first
            // selected input is reached.
            api.pausePathCondition();
            pathConditionPaused = true;
            token = TOKEN_COUNTER.incrementAndGet();
            ActiveRegion active = new ActiveRegion(token, activation, receiver,
                    Thread.currentThread());
            ACTIVE.put(token, active);
            CURRENT_TOKEN.set(token);
            active.entrySetup = true;
            symbolizeReceiverFields(active, api);
            active.entrySetup = false;
            diag("REGION_START", "token=" + token
                    + " region=" + safe(activation.regionId));
            api.resumePathCondition();
            pathConditionPaused = false;
            return token;
        } catch (Throwable throwable) {
            if (token != 0L) {
                ACTIVE.remove(token);
                Long current = CURRENT_TOKEN.get();
                if (current != null && current == token) {
                    CURRENT_TOKEN.remove();
                }
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
            releaseSymbolicEngine();
            writeSkipped(activation, SKIP_NOT_STARTED,
                    "engine start failed: " + rootCause(throwable));
            return 0L;
        }
    }

    /**
     * Instrumentation-facing root entry.  A zero-token placeholder is pushed
     * before {@link #enterRegion(String, Object, Object[])} starts the engine,
     * then filled without another allocation.  If entry fails, that exact
     * placeholder remains for the injected exceptional or original-handler
     * cleanup path; this prevents a caught same-root entry failure from
     * exposing an enclosing frame.  Token zero is likewise retained after a
     * successful unselected entry as its exact ownership marker.
     */
    public static long enterRegionFrame(String rootMethod, Object receiver,
                                        Object[] rootArguments) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = new RootInvocationFrame(rootMethod, 0L);
        frames.push(frame);
        long token = enterRegion(rootMethod, receiver, rootArguments);
        frame.token = token;
        return token;
    }

    /**
     * Reserves the single symbolic engine for this activation, waiting for a
     * bounded budget when a concurrent activation already holds it.
     *
     * <p>A workload reaches one region root from several threads, and which
     * of those activations first grabs the engine is decided by scheduling.
     * Discarding a losing activation outright throws away the only evidence
     * the task may ever get, because the winner can still turn out to
     * contradict the recording and emit nothing.  Waiting lets the losers
     * compete in turn.</p>
     *
     * <p>The wait is bounded on purpose: an activation that holds the engine
     * may itself be blocked on progress only the waiting thread can make, and
     * an unbounded wait would deadlock the workload.  The timeout is
     * therefore a named skip reason rather than a silent retry.</p>
     *
     * <p>{@code entryStateRank} orders candidates that are waiting at the
     * same time: an activation whose recorded entry values agree goes before
     * one whose evidence decides nothing, which goes before one that
     * disagrees.  Rank never rejects a candidate, so the last candidate left
     * is always admitted; only the recorded branch prefix refuses one.</p>
     *
     * @return an empty string once reserved, otherwise the skip reason.
     */
    private static String reserveSymbolicEngine(int entryStateRank) {
        int rank = Math.max(0, Math.min(ENTRY_STATE_RANKS - 1,
                entryStateRank));
        long deadline = System.currentTimeMillis() + engineWaitMillis();
        synchronized (ENGINE_LOCK) {
            ENGINE_WAITING[rank]++;
            try {
                while (true) {
                    if (!ENGINE_BUSY.get() && !betterCandidateWaiting(rank)) {
                        ENGINE_BUSY.set(true);
                        return "";
                    }
                    long remaining = deadline - System.currentTimeMillis();
                    if (remaining <= 0L) return ENGINE_BUSY_TIMEOUT;
                    try {
                        ENGINE_LOCK.wait(remaining);
                    } catch (InterruptedException interrupted) {
                        // Thread roots are commonly interrupted during
                        // shutdown.  Preserve that signal for the workload
                        // instead of silently consuming it inside
                        // instrumentation.
                        Thread.currentThread().interrupt();
                        return ENGINE_BUSY_INTERRUPTED;
                    }
                }
            } finally {
                ENGINE_WAITING[rank]--;
                // A candidate that stops waiting -- because it won, gave up or
                // was interrupted -- may be the only reason a worse-ranked one
                // is still deferring.
                ENGINE_LOCK.notifyAll();
            }
        }
    }

    /** Guarded by {@link #ENGINE_LOCK}. */
    private static boolean betterCandidateWaiting(int rank) {
        for (int better = 0; better < rank; better++) {
            if (ENGINE_WAITING[better] > 0) return true;
        }
        return false;
    }

    private static void releaseSymbolicEngine() {
        synchronized (ENGINE_LOCK) {
            ENGINE_BUSY.set(false);
            ENGINE_LOCK.notifyAll();
        }
    }

    /** Wait budget for the single symbolic engine, in milliseconds. */
    static long engineWaitMillis() {
        String configured = safe(System.getProperty(
                ENGINE_WAIT_PROPERTY)).trim();
        if (configured.isEmpty()) return DEFAULT_ENGINE_WAIT_MILLIS;
        try {
            return Math.max(0L, Long.parseLong(configured));
        } catch (NumberFormatException malformed) {
            return DEFAULT_ENGINE_WAIT_MILLIS;
        }
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
                    // declared reference argument with null.  A null Java
                    // reference has no object that the VM can symbolize. The
                    // applied assignment remains recorded, while any zero-PC
                    // concrete branch stays observation-only.
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
        int occurrence = active.currentMethodArgumentMaterializationOccurrence(
                method, argumentIndex);
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

    /**
     * Applies a solver model at an exact in-region helper parameter.
     * Repeated calls are selected by an activation-local ordinal, just like
     * repeated local-definition materializations.
     */
    public static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return boxedOrReference;
        int occurrence = active.nextMethodArgumentMaterializationOccurrence(
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

    /**
     * Materializes the primitive value consumed by one exact {@code getstatic}
     * site.  Static JVM state is process-global, so the hook deliberately
     * symbolizes the activation-local consumed value instead of mutating the
     * real static field and leaking a replay assignment into another region.
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
        int occurrence = active.nextFieldMaterializationOccurrence(
                method, unitIndex);
        // An accessor can be an exact causal slot without being a new
        // symbolic live-in.  In particular, a field written earlier in this
        // same region already carries its symbolic expression and must not be
        // re-symbolized as an independent variable.  Record that the exact
        // slot was observed before applying the written-field guard.
        for (SymbolizeAction action : active.activation.declaredSymbolize) {
            if (action.matchesField(method, unitIndex, owner,
                    fieldSignature, fieldName)
                    && action.acceptsDirectFieldOccurrence(occurrence)) {
                active.observedInputSlots.add(action.symbol);
            }
        }
        if (active.writtenFields.contains(owner, fieldSignature)) {
            return;
        }
        active.snapshotReferenceAliasSources(owner);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName)
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
                boolean assignmentFailed = false;
                Object materializedContainer = null;
                for (ModelAssignment assignment
                        : active.fieldAssignments(action)) {
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

                EngineApi api = engine();
                Field exactField = declaredInstanceField(leafOwner,
                        action.exactLeafFieldSignature());
                if (exactField == null) {
                    active.addUnresolvedOnce(action.symbol
                            + ": exact field declaration is unavailable");
                    continue;
                }
                Object value = exactField.get(leafOwner);
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
                    active.recordSymbolizedObject(action.symbol,
                            materializedContainer);
                } else if (value != null && value != MissingValue.INSTANCE
                        && containerValue(value)) {
                    requireTrackedContainer(api, value, action.symbol);
                    ensurePathRecordingStarted(active);
                    active.recordSymbolizedObject(action.symbol, value);
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

    /**
     * Applies a sparse associative replay model to the key used by this
     * execution, rather than to the concrete key observed in an earlier run.
     * The container identity and access ordinal form the replay selector; the
     * key and map cardinality remain concrete workload state.
     */
    public static void materializeAssociativeRead(Object container,
                                                  Object key) {
        ActiveRegion active = activeRegion();
        if (active == null || !(container instanceof Map<?, ?>)) return;
        String inputSymbol = active.symbolizedObjectPort(container);
        if (inputSymbol.isEmpty()) return;
        int occurrence = active.nextAssociativeAccessOccurrence(inputSymbol);
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

    public static void recordFieldWrite(Object owner,
                                        String fieldSignature) {
        ActiveRegion active = activeRegion();
        if (active != null) {
            active.writtenFields.add(owner, fieldSignature);
        }
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

    /**
     * Builds one concrete branch execution witness.  Deliberately carries no
     * path condition, no VM event id and no occurrence ordinal so that the
     * importer can only read "this site ran, and this is the way it went".
     */
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
     * region return. The injected code supplies the exact leaf owner, field,
     * and value so the VM can distinguish a preserved pre-state shadow from
     * a concrete write on this replay path.
     */
    public static void recordRegionExitFieldOutput(
            String captureBindingId, Object fieldOwner, Object fieldValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request =
                active.activation.regionExitFieldCapture(
                        captureBindingId);
        if (request == null || !active.captureEligible(request)) return;
        if (request.occurrenceScoped()) {
            active.nextOutputCaptureOccurrence(request);
            active.addUnresolvedOnce(request.captureBindingId()
                    + ": exact bounded heap-write occurrence requires a "
                    + "mutation-site output capture hook");
            return;
        }
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!withinBoundedOutputWindow(occurrence)) return;

        recordRegionExitFieldOutput(active, request, fieldOwner, fieldValue,
                occurrence);
    }

    /** Records one exact argument value at the configured protocol call. */
    public static void recordCallArgumentOutput(
            String captureBindingId, Object value) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
                captureBindingId);
        if (request == null || !request.capturesCallArgument()
                || !active.captureEligible(request)) return;
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!withinBoundedOutputWindow(occurrence)) return;

        JsonObject row = new JsonObject();
        row.addProperty("captureBindingId", request.captureBindingId());
        addOutputCaptureOccurrence(row, request, occurrence, occurrence);
        try {
            EngineApi api = engine();
            if (containerValue(value)
                    && !snapshotOutputContainer(value, api)) {
                throw new IllegalStateException(
                        "call argument is not a supported container");
            }
            JsonElement expression = engineExpression(
                    api.expression(value));
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException(
                        "custom VM returned no call-argument expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": call-argument output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
        }
        finishAtExactOutputBoundary(active);
    }

    /**
     * Starts one definition-invocation-local occurrence stream.  The trace
     * call id that selected this relation is discovery evidence only; replay
     * counts the mutator executions from one at each actual method entry.
     */
    public static void beginMutationMethodStateOutput(
            String captureBindingId) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()
                || !request.definitionInvocationScoped()) {
            return;
        }
        diag("MUTATION_ENTER", safe(captureBindingId));
        active.beginMutationMethodStateOutput(request);
    }

    /**
     * Selects the exact mutator occurrence whose receiver will be captured
     * when the enclosing mutation method completes normally.  Deferring the
     * snapshot prevents a multi-write method from exporting a partial batch.
     */
    public static void recordMutationStateOutput(
            String captureBindingId, Object container) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()
                || !active.captureEligible(request)) return;
        MutationCaptureIndex index =
                active.nextMutationOutputCaptureOccurrence(request);
        if (index == null) return;
        diag("MUTATION_SITE", safe(captureBindingId)
                + " occ=" + index.selection + " version=" + index.version);
        if (!withinBoundedOutputWindow(index.selection)) return;

        active.deferMutationStateOutput(request, container, index);
    }

    /** Emits a selected mutation receiver at its method's normal exit. */
    public static void recordMutationMethodExitStateOutput(
            String captureBindingId) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
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
            if (!snapshotOutputContainer(pending.container, api)) {
                throw new IllegalStateException(
                        "mutation receiver is not a supported container");
            }
            JsonElement expression = engineExpression(
                    api.expression(pending.container));
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
        }
        finishAtExactOutputBoundary(active);
    }

    /** Captures one direct instance-field definition at the exact putfield. */
    public static void recordFieldWriteStateOutput(
            String captureBindingId, Object fieldOwner, Object fieldValue) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
                captureBindingId);
        if (request == null || !request.capturesFieldWriteState()
                || !active.captureEligible(request)) return;
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!withinBoundedOutputWindow(occurrence)) return;

        JsonObject row = outputCaptureRow(request, occurrence);
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
                JsonObject identity = concreteReferenceIdentity(active,
                        field, fieldValue);
                if (identity == null) {
                    throw new IllegalStateException(
                            "custom VM returned no field-write expression");
                }
                row.add("referenceIdentity", identity);
            } else {
                row.add("expression", expression);
            }
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": field-write output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
        }
        finishAtExactOutputBoundary(active);
    }

    /** Ends the relation at the first semantic boundary with every output. */
    private static void finishAtExactOutputBoundary(ActiveRegion active) {
        if (active != null && !active.finished.get()
                && active.hasCompleteExactOutputBoundary()) {
            finish(active.token, "OUTPUT_BOUNDARY", "", null);
        }
    }

    private static JsonObject outputCaptureRow(
            OutputCaptureSpec request, int occurrence) {
        // Captures counted straight off the port already run monotonically
        // across the boundary, so their selection index is their version.
        return outputCaptureRow(request, occurrence, occurrence);
    }

    private static JsonObject outputCaptureRow(OutputCaptureSpec request,
            int occurrence, int versionOrdinal) {
        JsonObject row = new JsonObject();
        row.addProperty("captureBindingId", request.captureBindingId());
        addOutputCaptureOccurrence(row, request, occurrence, versionOrdinal);
        return row;
    }

    private static void recordRegionExitFieldOutput(
            ActiveRegion active, OutputCaptureSpec request,
            Object fieldOwner, Object fieldValue, int occurrence) {

        JsonObject row = outputCaptureRow(request, occurrence);

        EngineApi api = engine();
        try {
            JsonElement expression;
            DeclaredField declared = null;
            if (containerValue(fieldValue)) {
                // A tracked container relation may still be rooted at an
                // unconstrained STATE.  Re-snapshot the concrete final
                // members so key set/cardinality stay frozen while selected
                // element fields remain symbolic in the path guard.
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
                JsonObject identity = concreteReferenceIdentity(active,
                        declared, fieldValue);
                if (identity == null) {
                    throw new IllegalStateException("custom VM returned no "
                            + "normal-exit field expression");
                }
                row.add("referenceIdentity", identity);
            } else {
                row.add("expression", expression);
            }
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

    /** Names a reference output the VM never symbolised. */
    static final String CONCRETE_REFERENCE_IDENTITY_AUTHORITY =
            "CONCRETE_REFERENCE_IDENTITY_RELATION_V1";

    /**
     * States what a reference-valued write actually related.
     *
     * <p>The custom VM has no expression for a reference: there is no value
     * to constrain, only an object to hand on.  That is still a real
     * relation — this write says exactly which object the consumer receives —
     * and the replay knows it exactly, by identity.  Recording it keeps the
     * producer's output observable for alias passing without inventing a
     * symbolic value the VM does not have; a composition that needs a scalar
     * leaf below this reference must find that leaf its own producer or say
     * so.  Only a reference qualifies: a primitive with no expression is a
     * genuine capture failure and must stay one.</p>
     */
    private static JsonObject concreteReferenceIdentity(
            ActiveRegion active, DeclaredField field, Object value) {
        if (active == null || field == null) return null;
        String descriptor = javaTypeDescriptor(field.type());
        if (!descriptor.startsWith("L") && !descriptor.startsWith("[")) {
            return null;
        }
        JsonObject identity = new JsonObject();
        identity.addProperty("authority",
                CONCRETE_REFERENCE_IDENTITY_AUTHORITY);
        identity.addProperty("fieldSignature", field.signature());
        identity.addProperty("javaType", field.type());
        identity.addProperty("objectId", active.objectToken(value));
        identity.addProperty("runtimeType", value == null ? ""
                : value.getClass().getName());
        return identity;
    }

    /**
     * States what a region's own root output related, when it related no
     * value.
     *
     * <p>A demanded output published as the region's return value has no
     * capture site to hook: there is no write, only the value the activation
     * hands back.  The VM is asked for it directly, and for a plain object it
     * answers with an observation carrying no expression — the same answer it
     * gives for a reference-valued write, and it means the same thing here:
     * an object was handed on and no value inside it was related.  Recording
     * the identity keeps that a stated relation instead of an unexplained
     * empty capture; whether an alias is what this port may publish is the
     * importer's judgement, because only the closure declares the port's
     * type.  A value the VM did relate, a boxed primitive it could not, and a
     * thrown exception all stay outside this: none of them is an object this
     * activation handed on as its output.</p>
     */
    private static JsonObject rootOutputReferenceIdentity(
            ActiveRegion active, JsonElement observation, Object output) {
        if (active == null || output == null
                || output instanceof Throwable
                || observation == null || !observation.isJsonObject()) {
            return null;
        }
        JsonObject wrapper = observation.getAsJsonObject();
        JsonElement expression = wrapper.get("expression");
        if (expression != null && !expression.isJsonNull()) return null;
        // The VM names a descriptor only for a boxed primitive, whose
        // missing expression is a genuine capture failure, never an alias.
        if (!string(wrapper, "javaTypeDescriptor").isEmpty()) return null;
        JsonObject identity = new JsonObject();
        identity.addProperty("authority",
                CONCRETE_REFERENCE_IDENTITY_AUTHORITY);
        identity.addProperty("objectId", active.objectToken(output));
        identity.addProperty("runtimeType", output.getClass().getName());
        return identity;
    }

    private static void addOutputCaptureOccurrence(JsonObject row,
            OutputCaptureSpec request, int occurrence, int versionOrdinal) {
        row.addProperty("outputSiteId", request.outputSiteId());
        row.addProperty("outputOccurrence", occurrence);
        row.addProperty("outputVersionOrdinal", versionOrdinal);
        row.addProperty("replayOccurrence", request.replayOccurrence());
    }

    private static boolean exactOutputBoundaryCapture(
            OutputCaptureSpec request) {
        return request != null && (request.capturesCallArgument()
                || request.capturesFieldWriteState()
                || request.capturesMutationState());
    }

    /**
     * Admits an observation of the recorded output relation.
     *
     * <p>The recorded ordinal is provenance, not replay identity.  The task's
     * semantic boundary is selected by its static endpoint.  The binding,
     * static site, positive bounded occurrence, and engine-produced relation
     * must agree; input and branch evidence are composed later rather than
     * revalidated at the output hook.</p>
     */
    private static boolean successfulExactOutputCapture(
            OutputCaptureSpec request, JsonObject capture) {
        if (request == null || capture == null
                || !request.captureBindingId().equals(
                string(capture, "captureBindingId"))) {
            return false;
        }
        if (!observedOutputRelation(capture)) return false;
        return !request.occurrenceScoped()
                || request.outputSiteId().equals(
                string(capture, "outputSiteId"))
                && withinBoundedOutputWindow(integer(capture,
                "outputOccurrence", -1));
    }

    /**
     * True when the row carries a relation: a symbolic expression, or the
     * exact runtime identity of a reference the VM never symbolised.
     */
    private static boolean observedOutputRelation(JsonObject capture) {
        JsonElement expression = capture.get("expression");
        if (expression != null && !expression.isJsonNull()) return true;
        JsonElement identity = capture.get("referenceIdentity");
        return identity != null && identity.isJsonObject()
                && CONCRETE_REFERENCE_IDENTITY_AUTHORITY.equals(
                string(identity.getAsJsonObject(), "authority"));
    }

    /**
     * Admits any positive replay-local occurrence of an output site.
     *
     * <p>The occurrence counter numbers every activation-local execution of
     * the capture site, nested calls and multiple loop nests included, so it
     * is not a loop body counter and the CFG loop bound does not cap it: a
     * replay whose every loop stays within the bound can still reach one
     * site more often than the per-loop bound.  The bounded window itself is
     * enforced by the loop-cut policy; refusing the ordinal here silently
     * discarded relations the bounded replay legitimately produced.</p>
     */
    private static boolean withinBoundedOutputWindow(int occurrence) {
        return occurrence >= 1;
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
            // One admitted observation completes the boundary.  A later
            // occurrence is another version of the same relation, not a
            // second relation, so several of them are not a contradiction.
            if (successfulRows < 1) return false;
        }
        return true;
    }

    /**
     * True when the VM captured at least one output the task actually asks
     * for.  Resource-bounded completion is per port: successful ports from
     * this one VM path are retained, while every other demanded port remains
     * an explicit gap and keeps the summary relationally incomplete.
     */
    private static boolean anyExactOutputRelation(
            boolean capturesOutputRelation,
            List<OutputCaptureSpec> requests,
            List<JsonObject> captures) {
        if (!capturesOutputRelation || requests == null || requests.isEmpty()
                || captures == null || captures.isEmpty()) {
            return false;
        }
        for (OutputCaptureSpec request : requests) {
            if (!exactOutputBoundaryCapture(request)) continue;
            for (JsonObject capture : captures) {
                if (successfulExactOutputCapture(request, capture)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * True once every branch-replay site the task demands has executed at
     * least once in this activation.
     *
     * <p>The task plan names the branch sites the producer relation replays,
     * and a replay that captured its outputs but never reached one of them
     * has not yet done the work the plan asked for: closing there discards
     * that site's decision and every later version of the same relation.
     * Both kinds of observation count, because a symbolic mapping and a
     * concrete witness each attest that the site executed.  The bounded
     * window stays capped by the loop-cut policy, so a demanded site this
     * replay cannot reach ends the activation at its cut instead.</p>
     */
    static boolean demandedBranchSitesObserved(
            Collection<String> demandedSites, Set<String> observedSites) {
        if (demandedSites == null) return true;
        for (String site : demandedSites) {
            if (site != null && !site.isEmpty()
                    && (observedSites == null
                    || !observedSites.contains(site))) {
                return false;
            }
        }
        return true;
    }

    /**
     * True when the decision that entered a loop body was attested to carry
     * no symbolic expression.
     *
     * <p>Only a symbolically decided continuation can explode the path space,
     * so only such a loop spends the unroll budget; a concrete guard's trip
     * count is data this replay observes.  The decision that answers for a
     * body is the one this loop's own guard made, which the instrumentation
     * names on the edge it split.  When that guard did decide - it is a
     * branch site of the symbolic slice - it is the only witness accepted,
     * and a branch inside the body can no longer stand in for it: such an
     * impostor runs between two body entries and shares the loop's method, so
     * a concrete one would release a symbolically guarded loop and a symbolic
     * one charges a loop the replay merely walks.</p>
     *
     * <p>A guard outside the slice never decides anything this replay can
     * see.  No witness for it can be produced, and demanding one would charge
     * the unroll bound for every concrete walk over recorded data - a cut on
     * loops the solver was never offered a choice about.  Such a loop keeps
     * the evidence this replay does have, its own method's attested decision,
     * exactly as before; naming that guard in the symbolic slice is what
     * would answer it exactly.  Its work is not unaccounted for either way:
     * every body it runs is charged to the replay resource cap.</p>
     */
    static boolean concreteGuardEnteredBody(
            String loopId, String guardSiteId, boolean guardDecides,
            String decisionSiteId, boolean decisionConcrete) {
        int marker = safe(loopId).indexOf("#loop:");
        String decision = safe(decisionSiteId);
        if (!decisionConcrete || marker <= 0 || decision.isEmpty()) {
            return false;
        }
        String guard = safe(guardSiteId);
        if (guardDecides && !guard.isEmpty()) {
            // The guard decides this loop, so nothing else answers for it.
            return decision.equals(guard);
        }
        // A guard that has never decided is outside the slice, and no witness
        // for it exists to demand.  The loop's method is the narrowest scope
        // its continuation can be attested in at all.
        return decision.startsWith(loopId.substring(0, marker) + "#u");
    }

    /** Separates a body-entry edge's loop from the guard that decides it. */
    private static final String BODY_ENTRY_GUARD_MARKER = "@guard:u";

    /**
     * The loop whose ledger a body-entry edge spends, which is the identity
     * the latch hooks of the same loop are given.
     */
    static String loopIdentity(String encodedLoopId) {
        String encoded = safe(encodedLoopId);
        int marker = encoded.indexOf(BODY_ENTRY_GUARD_MARKER);
        return marker < 0 ? encoded : encoded.substring(0, marker);
    }

    /**
     * The branch site whose decision enters the body, or the empty string
     * when the instrumentation named none for this edge.
     */
    static String bodyEntryGuardSite(String encodedLoopId) {
        String encoded = safe(encodedLoopId);
        int marker = encoded.indexOf(BODY_ENTRY_GUARD_MARKER);
        if (marker < 0) return "";
        String loop = encoded.substring(0, marker);
        int loopMarker = loop.indexOf("#loop:");
        if (loopMarker <= 0) return "";
        String unitIndex = encoded.substring(
                marker + BODY_ENTRY_GUARD_MARKER.length());
        if (unitIndex.isEmpty()) return "";
        for (int index = 0; index < unitIndex.length(); index++) {
            char digit = unitIndex.charAt(index);
            if (digit < '0' || digit > '9') return "";
        }
        return loop.substring(0, loopMarker) + "#u" + unitIndex;
    }

    /**
     * True when an accessor-return action accepts the activation-local
     * occurrence the replay just counted for its caller/site/callee stream.
     * The refined trace and {@link ActiveRegion} use that same stream key;
     * the helper-bounded ordinal is only a retention-capacity coordinate and
     * may restart at one for several calls inside this activation.
     */
    static boolean acceptsAccessorOccurrenceForTests(
            JsonObject action, int actualOccurrence) {
        return new SymbolizeAction(action)
                .acceptsAccessorOccurrence(actualOccurrence);
    }

    static boolean acceptsDirectFieldOccurrenceForTests(
            JsonObject action, int actualOccurrence) {
        return new SymbolizeAction(action)
                .acceptsDirectFieldOccurrence(actualOccurrence);
    }

    static int maxLoopBodiesForTests(JsonObject encodedTask, String loopId) {
        return new RuntimeTask(ExecutionTask.decode(encodedTask))
                .maxLoopBodies(loopId);
    }

    /** Test seam for exact-output boundary completion without a custom VM. */
    static boolean exactOutputBoundaryReachedForTests(
            JsonObject encodedTask, JsonArray encodedCaptures) {
        ExecutionTask task = ExecutionTask.decode(encodedTask);
        List<JsonObject> captures = new ArrayList<>();
        if (encodedCaptures != null) {
            for (JsonElement element : encodedCaptures) {
                if (!element.isJsonObject()) return false;
                captures.add(element.getAsJsonObject());
            }
        }
        return completeExactOutputBoundary(
                task.goalKind().capturesOutputRelation(),
                task.outputCaptures(), captures);
    }

    static boolean incompleteRelationOnlyBoundaryForTests(
            JsonObject encodedTask, JsonArray encodedCaptures,
            String exitKind) {
        ExecutionTask task = ExecutionTask.decode(encodedTask);
        List<JsonObject> captures = new ArrayList<>();
        if (encodedCaptures != null) {
            for (JsonElement element : encodedCaptures) {
                if (!element.isJsonObject()) return false;
                captures.add(element.getAsJsonObject());
            }
        }
        return incompleteRelationOnlyBoundary(new RuntimeTask(task),
                captures, exitKind);
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

    /** Test seam for semantic-slot output capture selection. */
    static boolean outputCaptureEligibleForTests(
            JsonObject encodedTask, String captureBindingId,
            JsonArray encodedSymbolized, JsonArray encodedCaptures) {
        return outputCaptureEligibleForTests(encodedTask, captureBindingId,
                encodedSymbolized, new JsonArray(), encodedCaptures);
    }

    static boolean outputCaptureEligibleForTests(
            JsonObject encodedTask, String captureBindingId,
            JsonArray encodedSymbolized, JsonArray encodedObserved,
            JsonArray encodedCaptures) {
        RuntimeTask task = new RuntimeTask(ExecutionTask.decode(encodedTask));
        ActiveRegion active = new ActiveRegion(1L, task, null,
                Thread.currentThread());
        if (encodedSymbolized != null) {
            for (JsonElement element : encodedSymbolized) {
                if (!element.isJsonPrimitive()) return false;
                active.symbolized.add(element.getAsString());
            }
        }
        if (encodedObserved != null) {
            for (JsonElement element : encodedObserved) {
                if (!element.isJsonPrimitive()) return false;
                active.observedInputSlots.add(element.getAsString());
            }
        }
        if (encodedCaptures != null) {
            for (JsonElement element : encodedCaptures) {
                if (!element.isJsonObject()) return false;
                active.outputCaptures.add(element.getAsJsonObject());
            }
        }
        return active.captureEligible(task.outputCapture(captureBindingId));
    }

    /** Test seam for per-port resource-cut completion. */
    static boolean resourceCutCapturedOutputForTests(
            JsonObject encodedTask, JsonArray encodedCaptures) {
        ExecutionTask task = ExecutionTask.decode(encodedTask);
        List<JsonObject> captures = new ArrayList<>();
        if (encodedCaptures != null) {
            for (JsonElement element : encodedCaptures) {
                if (!element.isJsonObject()) return false;
                captures.add(element.getAsJsonObject());
            }
        }
        return anyExactOutputRelation(
                task.goalKind().capturesOutputRelation(),
                task.outputCaptures(), captures);
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

    /**
     * A complete snapshot has no failure-relevance proof with which to choose
     * sparse cells. It therefore fits the canonical capacity or fails closed;
     * callers must never silently retain the first bounded physical members.
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

    /** Normal region exit. */
    public static void exitRegion(long token, Object returnValue,
                                  String primitiveValue) {
        finish(token, "NORMAL", "", returnValue);
    }

    /**
     * Invocation-exact normal cleanup used by injected roots.  This method is
     * intentionally no-throw: instrumentation bookkeeping must never turn a
     * normal program return into an exception (or let the synthetic catch-all
     * pop an enclosing frame a second time).
     */
    public static void exitRegionFrame(String rootMethod, Object returnValue,
                                       String primitiveValue) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(rootMethod);
            if (frame != null && frame.token != 0L) {
                exitRegion(frame.token, returnValue, primitiveValue);
            }
        } catch (Throwable ignored) {
            // Runtime observation is fail-closed and cannot alter the return.
        }
    }

    /** Exceptional region exit. */
    public static void throwRegion(long token, Throwable throwable) {
        finish(token, "THROW",
                throwable == null ? "" : throwable.getClass().getName(),
                throwable);
    }

    /**
     * Invocation-exact exceptional cleanup used by the synthetic catch-all.
     * The original throwable is rethrown by injected bytecode; consequently
     * every runtime failure is swallowed here so it cannot replace it.
     */
    public static void throwRegionFrame(String rootMethod,
                                        Throwable throwable) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(rootMethod);
            if (frame != null && frame.token != 0L) {
                if ("CUT".equals(exceptionalExitKind(throwable))) {
                    finish(frame.token, "CUT", "", throwable);
                } else {
                    throwRegion(frame.token, throwable);
                }
            }
        } catch (Throwable ignored) {
            // Preserve the program's original throwable identity.
        }
    }

    static String exceptionalExitKind(Throwable throwable) {
        return throwable instanceof LoopBoundCut ? "CUT" : "THROW";
    }

    private static RootInvocationFrame popRootInvocationFrame(
            String rootMethod) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = frames.peek();
        if (frame == null) {
            ROOT_INVOCATION_FRAMES.remove();
            return null;
        }
        boolean matches = rootMethod == null
                ? frame.rootMethod == null
                : rootMethod.equals(frame.rootMethod);
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
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String rootMethod, long token) {
            this.rootMethod = rootMethod;
            this.token = token;
        }
    }

    /**
     * Reserves a VM-attested branch event immediately before the original
     * conditional executes.  The returned handle is activation-local and is
     * consumed by the matching post-branch resolve hook.
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
        if (active.activation.relationOnlySeed()) {
            // A producer seed exports the relation observed at its semantic
            // output boundary.  Reading the whole accumulated path condition
            // at every branch is redundant (and quadratic on system traces):
            // the output hooks already capture the symbolic relation.
            active.takePreparedBranch(preparedHandle);
            return observedOutcome;
        }
        if (!active.pathRecordingStarted) {
            // The symbolic gate is still closed, so no VM event exists and no
            // path condition may be read. The branch did execute, though, and
            // a recorded site is attested by execution, not by solvability.
            try {
                active.recordConcreteBranchWitness(method, unitIndex,
                        observedOutcome);
                // No input has been materialized yet, so nothing this region
                // decides can carry a symbolic expression.
                active.noteBranchDecision(method, unitIndex, true);
                finishAtExactOutputBoundary(active);
            } catch (Throwable ignored) {
                // Observation must never alter the workload's own outcome.
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
        boolean stopAfterBranch = false;
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
            // The contract may have just been consumed, which is the other
            // half of a replay's boundary; the witness hook above ran before
            // this branch reached the contract and could not see it.
            finishAtExactOutputBoundary(active);
            stopAfterBranch = solverWitness
                    && replayTargetMatched
                    && active.activation.stopAfterBranch(
                    siteId(method, unitIndex), prepared.occurrence);
            return observedOutcome;
        } catch (Throwable throwable) {
            active.addUnresolvedOnce("branch/PC exact-event observation "
                    + "failed: " + rootCause(throwable));
            return observedOutcome;
        } finally {
            if (paused) resumePathCondition(active, api);
            if (stopAfterBranch) {
                finish(active.token, "TARGET_REACHED", "", null);
            } else if (replayContradicted) {
                // Release the engine here rather than at this activation's own
                // return: the branch that just executed already decided that
                // nothing publishable can follow.
                finish(active.token, "REPLAY_PREFIX_CONTRADICTED", "", null);
            }
        }
    }

    /**
     * Exact multiway counterpart of {@link #resolveBranch}. Successor ids use
     * the static case-key order followed by default; they are not collapsed
     * into the VM event's case-vs-default Boolean envelope.
     */
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
        if (active.activation.relationOnlySeed()) {
            active.takePreparedBranch(preparedHandle);
            return observedSuccessorIndex;
        }
        if (!active.pathRecordingStarted) return observedSuccessorIndex;
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
            // The VM emitted no symbolic branch event.  This branch is
            // outside the selected symbolic slice and supplies neither a
            // flippable decision nor a path assumption.
            return false;
        }
        String siteId = safe(method) + "#u" + unitIndex;
        int baseline = active.lastPathConditionSize;
        boolean noVmCondition = vmEventHasNoConditions(api, vmEventId);
        PathConditionElements conditions;
        int rawPathConditionSize;
        int attestationBaseline;
        if (noVmCondition) {
            // An exact conditionless event cannot contribute a branch guard.
            // Avoid serializing and parsing the full accumulated PC merely to
            // record a concrete observation.
            conditions = PathConditionElements.EMPTY;
            rawPathConditionSize = baseline;
            attestationBaseline = 0;
        } else {
            diag("PC_READ_BEGIN", siteId + " occ=" + occurrence);
            String raw = api.pathCondition();
            diag("PC_READ_END", siteId + " occ=" + occurrence
                    + " chars=" + (raw == null ? -1 : raw.length()));
            conditions = PathConditionElements.of(raw);
            rawPathConditionSize = conditions.size();
            attestationBaseline = baseline;
            diag("PC_PARSED", siteId + " occ=" + occurrence
                    + " conditions=" + rawPathConditionSize
                    + " mode=" + conditions.mode());
        }
        VmBranchEventAttestation vmAttestation = attestVmBranchEvent(api,
                active, siteId, expression, observedOutcome, vmEventId,
                occurrence, conditions, attestationBaseline);
        int conditionIndex = vmAttestation.valid
                && vmAttestation.conditionIndices.size() == 1
                ? vmAttestation.conditionIndices.get(0) : -1;
        JsonObject mapping = branchMapping(method, unitIndex, occurrence);
        // Exact VM ownership is one condition for an IfStmt.  Do not assign
        // every unrelated predicate accumulated since the previous hook to
        // this source branch.
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
                BranchWitness witness = BranchWitness.vmPc(siteId,
                        safe(method), unitIndex, occurrence,
                        observedOutcome, semanticCondition, conditionIndex,
                        branchPredicateMetadata(rawOperator,
                                semanticOperator));
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
        if (pathConditionShrank) {
            mapping.addProperty("mappingWarning",
                    "path condition shrank between branch hooks");
        } else if (!vmAttestation.valid) {
            mapping.addProperty("mappingWarning",
                    "VM exact branch event rejected: "
                            + vmAttestation.error);
        } else if (conditionIndex < 0) {
            mapping.addProperty("mappingWarning",
                    "no newly added target-method condition matches selected branch");
        }
        active.lastPathConditionSize = rawPathConditionSize;
        active.branchMappings.add(mapping);
        // A decision the VM attested owns no path condition carried no
        // symbolic expression.  Anything less than an attestation leaves the
        // question open, and an open question must be charged.
        active.noteBranchDecision(method, unitIndex, vmAttestation.valid
                && vmAttestation.conditionIndices.isEmpty());
        if (mapping.has("witness") || mapping.has("concreteObservation")) {
            // A marker without either authority carries no decision into the
            // summary, so it must not attest a recorded outcome either.
            active.witnessOutcome(siteId, observedOutcome);
            // This may be the last demanded branch-replay site, which is half
            // of the boundary condition; the captures alone never re-check it.
            finishAtExactOutputBoundary(active);
        }
        return vmAttestation.valid && conditionIndex >= 0;
    }

    private static boolean vmEventHasNoConditions(
            EngineApi api, long eventId) throws Exception {
        JsonElement parsed = parseJson(api.branchEvents());
        if (!parsed.isJsonObject()) return false;
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
        return matches == 1 && selected != null
                && integer(selected, "conditionCount", -1) == 0
                && array(selected, "conditionIndices").size() == 0;
    }

    private static JsonObject branchPredicateMetadata(
            String rawOperator, String semanticOperator) {
        JsonObject metadata = new JsonObject();
        metadata.addProperty("predicateNormalization",
                safe(rawOperator).equals(safe(semanticOperator))
                        ? BranchWitness.IDENTITY_NORMALIZATION
                        : BranchWitness.CMP_NORMALIZATION);
        return metadata;
    }

    private static void recordSwitchBranchPaused(
            ActiveRegion active, EngineApi api, String method, int unitIndex,
            String expression, int occurrence, SwitchExpectation expected,
            long vmEventId) throws Exception {
        String siteId = safe(method) + "#u" + unitIndex;
        PathConditionElements conditions = PathConditionElements.of(
                api.pathCondition());
        int baseline = active.lastPathConditionSize;
        VmBranchEventAttestation attestation = attestVmBranchEvent(api,
                active, siteId, expression, expected.caseArm(), vmEventId,
                occurrence, conditions, baseline, expected);
        List<Integer> conditionIndices = attestation.valid
                ? attestation.conditionIndices
                : Collections.<Integer>emptyList();
        JsonObject mapping = branchMapping(method, unitIndex, occurrence);
        mapping.addProperty("rawPathConditionSize", conditions.size());
        mapping.addProperty("rawPathConditionBaseline", baseline);
        if (!attestation.valid) {
            mapping.addProperty("mappingWarning",
                    "VM exact switch event rejected: "
                            + attestation.error);
            active.addUnresolvedOnce(siteId
                    + ": exact switch event attestation failed: "
                    + attestation.error);
        } else if (conditionIndices.isEmpty()) {
            mapping.addProperty("mappingWarning",
                    "switch selector was concrete; no symbolic arm guard "
                            + "is available for path closure");
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

    private static VmBranchEventAttestation attestVmBranchEvent(
            EngineApi api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, PathConditionElements conditions, int baseline) {
        return attestVmBranchEvent(api, active, siteId, expression,
                observedOutcome, eventId, occurrence, conditions, baseline,
                null);
    }

    private static VmBranchEventAttestation attestVmBranchEvent(
            EngineApi api, ActiveRegion active, String siteId,
            String expression, boolean observedOutcome, long eventId,
            int occurrence, PathConditionElements conditions, int baseline,
            SwitchExpectation switchExpectation) {
        if (eventId <= 0L) {
            return VmBranchEventAttestation.invalid(
                    "marker returned a non-positive event id");
        }
        final JsonElement parsed;
        try {
            parsed = parseJson(api.branchEvents());
        } catch (Throwable throwable) {
            return VmBranchEventAttestation.invalid(
                    "event stream is not readable: " + rootCause(throwable));
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
        // Such an observation can validate replay identity, but it supplies
        // no condition that a path worklist may negate or redirect.
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
            String conditionPosition = conditionCodePosition(condition);
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

    /**
     * Ends an activation whose completed evidence already contradicts its
     * recording, giving the single symbolic engine back before constructing a
     * summary that the runtime must discard.
     *
     * <p>A replay-prefix contradiction is final at the deciding branch.  A
     * seed-outcome contradiction is checked only once the selected bounded
     * activation finishes, because a later visit to the same site may still
     * witness the recorded outcome.  At either final boundary, retaining the
     * engine for summary construction can cost a sibling activation its whole
     * wait budget for a result that cannot be published.</p>
     */
    private static void abandonActivation(
            ActiveRegion active, long token, String skipKind, String reason) {
        try {
            cleanupContradictedActivation(token);
        } finally {
            releaseSymbolicEngine();
        }
        writeSkipped(active.activation, skipKind, reason);
    }

    /**
     * Rejects an incomplete relation root while preserving the exact partial
     * evidence needed to distinguish a wrong root from a wrong boundary.
     */
    private static void abandonIncompleteRelation(
            ActiveRegion active, long token, String reason) {
        try {
            cleanupContradictedActivation(token);
        } finally {
            releaseSymbolicEngine();
        }
        JsonObject evidence = new JsonObject();
        evidence.add("symbolizedInputs", GSON.toJsonTree(active.symbolized));
        evidence.add("outputCaptures", GSON.toJsonTree(
                active.outputCaptures));
        JsonArray missing = new JsonArray();
        for (OutputCaptureSpec request : active.activation.outputCaptures) {
            if (!active.hasSuccessfulOutputCapture(request)) {
                missing.add(request.captureBindingId());
            }
        }
        evidence.add("missingOutputCaptureBindingIds", missing);
        evidence.addProperty("runtimeThread", active.thread.getName());
        evidence.addProperty("runtimeReceiverClass",
                active.receiver == null ? ""
                        : active.receiver.getClass().getName());
        writeSkipped(active.activation, SKIP_INCOMPLETE_OUTPUT_RELATION,
                reason, evidence);
    }

    private static void cleanupContradictedActivation(long token) {
        try {
            engine().cleanupAfterFailure();
        } finally {
            Long current = CURRENT_TOKEN.get();
            if (current != null && current == token) {
                CURRENT_TOKEN.remove();
            }
        }
    }

    /** Actions on the two sides of a completed seed's final admission gate. */
    interface CompletedSeedResultActions {
        void cleanupRejectedSeed();

        void publishRejectedSeed(String conflict);

        void buildAcceptedResult();
    }

    /**
     * Applies the seed-outcome judgement at a completed activation boundary.
     * The rejected side owns engine release here, before the accepted side's
     * potentially large result construction can be entered.
     */
    static void completeSeedResultAtBoundary(
            Map<String, Set<Boolean>> recorded,
            Map<String, Set<Boolean>> witnessed,
            CompletedSeedResultActions actions) {
        String conflict = seedOutcomeConflict(recorded, witnessed);
        if (conflict.isEmpty()) {
            actions.buildAcceptedResult();
            return;
        }
        try {
            actions.cleanupRejectedSeed();
        } finally {
            try {
                releaseSymbolicEngine();
            } finally {
                // Cleanup is best effort.  Even if it fails, leave durable
                // evidence that this completed activation was intentionally
                // rejected rather than silently losing the selected result.
                actions.publishRejectedSeed(conflict);
            }
        }
    }

    private static void finish(long token, String exitKind,
                               String exceptionType, Object output) {
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.finished.compareAndSet(false, true)
                || !ACTIVE.remove(token, active)) {
            return;
        }
        beginSelectedResultPublication();
        try {
        // Exact call-site traps normally close every accessor scope first.
        // Region cleanup is the final fail-closed boundary for malformed or
        // externally interrupted control flow.
        clearAccessorCallContexts(token);
        diag("REGION_FINISH", "token=" + token + " exit=" + safe(exitKind)
                + " captures=" + active.outputCaptures.size());
        if (active.replayPrefixContradicted()) {
            abandonActivation(active, token,
                    SKIP_REPLAY_PREFIX_UNMATCHED,
                    "activation contradicts the recorded replay prefix: "
                            + active.replayProgress.failure());
            return;
        }
        if (incompleteRelationOnlyBoundary(active.activation,
                active.outputCaptures, exitKind)) {
            abandonIncompleteRelation(active, token,
                    "compatible root ended before every demanded semantic "
                            + "output boundary was observed");
            return;
        }
        // Replay tasks retain their existing admission path.  Seed-outcome
        // evidence is a completion gate only for non-replay seed tasks.
        if (active.activation.replayContract != null) {
            buildAndPublishResult(active, token, exitKind,
                    exceptionType, output);
            return;
        }
        // The activation is now finished and removed from ACTIVE, so its
        // witnessed outcome set cannot widen any further.  The completion
        // gate owns the reject-or-build order and releases a rejected seed
        // before the accepted side can enter large summary construction.
        completeSeedResultAtBoundary(active.activation.seedOutcomes,
                active.witnessedOutcomes,
                new CompletedSeedResultActions() {
                    @Override
                    public void cleanupRejectedSeed() {
                        cleanupContradictedActivation(token);
                    }

                    @Override
                    public void publishRejectedSeed(String conflict) {
                        writeSkipped(active.activation,
                                SKIP_SEED_OUTCOME_CONFLICT,
                                "activation contradicts a recorded seed "
                                        + "outcome: " + conflict);
                    }

                    @Override
                    public void buildAcceptedResult() {
                        buildAndPublishResult(active, token, exitKind,
                                exceptionType, output);
                    }
                });
        } finally {
            endSelectedResultPublication();
        }
    }

    private static void buildAndPublishResult(
            ActiveRegion active, long token, String exitKind,
            String exceptionType, Object output) {
        JsonObject result = new JsonObject();
        EngineApi api = engine();
        boolean engineFinished = false;
        String rawEngineSummary = null;
        // A loop-bound cut is itself the end of the bounded path.  A replay
        // resource cut normally means the activation answered nothing, but
        // an output-relation task may already have published demanded ports
        // before a long-lived service loop spends the remaining replay
        // budget.  Keep those real VM captures as one bounded prefix; any
        // other demanded port remains an explicit incomplete-relation gap.
        boolean boundedPathOutputExit = "CUT".equals(exitKind)
                && active.activation.capturesOutputRelation
                && active.loopBoundCut != null
                && active.replayResourceCut == null;
        boolean boundedResourceOutputExit = "CUT".equals(exitKind)
                && active.capturedOutputBeforeReplayResourceCut();
        boolean boundedOutputExit = boundedPathOutputExit
                || boundedResourceOutputExit;
        String completedExitKind = boundedOutputExit
                ? "BOUNDED" : exitKind;
        try {
            // Everything below is observational bookkeeping.  Pause PC
            // recording before any null checks, Gson work, or string building
            // can reuse a symbolic value and manufacture a false condition.
            api.pausePathCondition();
            if (!active.activation.symbolize.isEmpty()
                    && !active.pathRecordingStarted) {
                active.addUnresolvedOnce(
                        "NO_SELECTED_INPUT_MATERIALIZED");
            }
            if ("NORMAL".equals(completedExitKind)
                    || "BOUNDED".equals(completedExitKind)
                    && !boundedResourceOutputExit) {
                captureTrackedFieldOutputs(active);
            }
            populateCompletedResult(result, active, completedExitKind,
                    exceptionType, output);
            if (!"CUT".equals(completedExitKind)
                    && !"BOUNDED".equals(completedExitKind)
                    && !"OUTPUT_BOUNDARY".equals(completedExitKind)) {
                try {
                    String expression = api.expression(output);
                    JsonElement observation = parseJson(expression);
                    result.add("rootOutputExpression", observation);
                    JsonObject identity = rootOutputReferenceIdentity(
                            active, observation, output);
                    if (identity != null) {
                        result.add("rootOutputReferenceIdentity", identity);
                    }
                } catch (Throwable throwable) {
                    result.addProperty("outputExpressionError",
                            rootCause(throwable));
                }
            }
            String summary = api.finish();
            engineFinished = true;
            if (jsonObjectEnvelope(summary)) {
                // The VM already serialized this large object.  Keep it raw
                // and splice it into the JSONL record below; parsing and then
                // re-serializing it under the interpreter is needlessly
                // quadratic for real system paths.
                rawEngineSummary = summary;
            } else {
                result.addProperty("engineSummaryError",
                        "VM summary is not a JSON object");
            }
        } catch (Throwable throwable) {
            result.addProperty("engineSummaryError", rootCause(throwable));
        } finally {
            if (!engineFinished) {
                api.cleanupAfterFailure();
            }
            Long current = CURRENT_TOKEN.get();
            if (current != null && current == token) {
                CURRENT_TOKEN.remove();
            }
            releaseSymbolicEngine();
        }
        // If isolation failed before metadata construction, add the minimum
        // identity only after cleanup has removed the symbolic VM context.
        if (!result.has("event")) {
            addResultIdentity(result, active, exitKind, exceptionType);
        }
        if (active.activation.replayContract != null
                && !active.replayProgress.complete()) {
            writeSkipped(active.activation, SKIP_REPLAY_PREFIX_UNMATCHED,
                    "no compatible activation matched replay prefix: "
                            + active.replayProgress.failure());
            return;
        }
        boolean written = appendResult(result, rawEngineSummary);
        if (Boolean.getBoolean(HALT_AFTER_SELECTED_RESULT_PROPERTY)) {
            // A concolic replay is an isolated worker.  Long-running system
            // tests need not finish after the selected bounded activation has
            // durably emitted its VM summary.
            Runtime.getRuntime().halt(written ? 0 : 2);
        }
    }

    /**
     * Captures outputs rooted at a nested heap object observed during the
     * region.  Such an object is not necessarily reachable from the thread
     * entry receiver at return time, so the field-access hook is the exact
     * runtime authority for its owner identity.
     */
    private static void captureTrackedFieldOutputs(ActiveRegion active) {
        for (OutputCaptureSpec request : active.activation.outputCaptures) {
            if (!request.capturesRegionExitField()) continue;
            if (!active.captureEligible(request)
                    || active.hasOutputCapture(request.captureBindingId())
                    || active.hasObservedOutputCapture(request)) {
                continue;
            }
            if (request.occurrenceScoped()) {
                active.addUnresolvedOnce(request.captureBindingId()
                        + ": exact bounded heap-write occurrence requires a "
                        + "mutation-site output capture hook");
                continue;
            }
            Object owner = active.fieldAccessOwner(
                    request.accessRootInputPort());
            if (owner == null) continue;
            Object value = readExactField(owner, request.fieldSignature());
            if (value == MissingValue.INSTANCE) {
                active.addUnresolvedOnce(request.captureBindingId()
                        + ": exact nested output field is unavailable");
                continue;
            }
            int occurrence = active.nextOutputCaptureOccurrence(request);
            if (withinBoundedOutputWindow(occurrence)) {
                recordRegionExitFieldOutput(active, request, owner, value,
                        occurrence);
            }
        }
    }

    private static void populateCompletedResult(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType, Object output) {
        addResultIdentity(result, active, exitKind, exceptionType);
        if (output instanceof Throwable && !"CUT".equals(exitKind)) {
            result.add("exceptionChain", exceptionChain((Throwable) output));
        }
        if (active.loopBoundCut != null) {
            result.add("pathCut", copyJsonTree(active.loopBoundCut));
        }
        if (active.replayResourceCut != null) {
            result.add("replayResourceCut",
                    copyJsonTree(active.replayResourceCut));
        }
        result.add("loopBackedgeTraversals",
                active.loopBackedges.toJson());
        result.add("replayLoopBodies",
                active.loopBackedges.bodiesToJson());
        active.validateRegionExitFieldCaptures(exitKind);
        result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
        result.add("symbolizedInputs", GSON.toJsonTree(active.symbolized));
        result.add("branchMappings", GSON.toJsonTree(active.branchMappings));
        if (!active.concreteBranchWitnesses.isEmpty()) {
            result.add("concreteBranchWitnesses",
                    GSON.toJsonTree(active.concreteBranchWitnesses));
        }
        result.add("outputCaptures", GSON.toJsonTree(active.outputCaptures));
    }

    private static void addResultIdentity(
            JsonObject result, ActiveRegion active, String exitKind,
            String exceptionType) {
        result.addProperty("event", "CONCOLIC_REGION_RESULT");
        result.addProperty("schemaVersion", 1);
        result.addProperty("taskId", active.activation.taskId);
        result.addProperty("exitKind", exitKind);
        result.addProperty("exceptionType", safe(exceptionType));
    }

    private static void symbolizeReceiverFields(ActiveRegion active, EngineApi api) {
        for (SymbolizeAction action : active.activation.symbolize) {
            // Nested/shared heap fields are materialized on their real owner at
            // the field-access hook. Looking them up on an unrelated region
            // root is incorrect and creates unresolved heap ports.
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
                requireTrackedContainer(api, value, action.symbol);
                ensurePathRecordingStarted(active);
                active.recordSymbolizedObject(action.symbol, value);
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
        if (!writeModeledField(owner,
                action.exactLeafFieldSignature(path), assignment)) {
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
                active.recordModelAssignment(assignment);
            }
        }
        Object fresh = freshPrimitiveBox(modeled);
        try {
            EngineApi api = engine();
            api.symbolizeField(fresh, "value", action.symbol);
            ensurePathRecordingStarted(active);
            active.symbolized.add(action.symbol);
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
            ModelAssignment assignment) {
        return writeModeledField(owner, fieldSignature, assignment,
                MissingValue.INSTANCE);
    }

    private static boolean writeModeledField(
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
            // decoding.  Otherwise a NULL model for a String-typed field is
            // silently materialized as the four-character string "null".
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

    private enum EntryStateVerdict { MATCHES, DIFFERS, UNDECIDED }

    private static boolean referenceTypeDescriptor(String descriptor) {
        String value = safe(descriptor);
        return value.startsWith("L") || value.startsWith("[");
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
                requireTrackedContainer(api, value, action.symbol);
            } else {
                api.symbolize(value, action.symbol);
            }
            ensurePathRecordingStarted(active);
            active.symbolized.add(action.symbol);
            if (value != null && !liveArray) {
                active.recordSymbolizedObject(action.symbol, value);
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
        if (owner == null || declared == null) return null;
        Class<?> type = owner.getClass();
        while (type != null && !declared.owner().equals(type.getName())) {
            type = type.getSuperclass();
        }
        if (type == null) return null;
        while (type != null) {
            try {
                Field field = type.getDeclaredField(declared.name());
                if (Modifier.isStatic(field.getModifiers())
                        || !javaTypeDescriptor(declared.type()).equals(
                        javaTypeDescriptor(field.getType().getTypeName()))) {
                    return null;
                }
                if (!field.isAccessible()) field.setAccessible(true);
                return field;
            } catch (NoSuchFieldException inherited) {
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

    /**
     * Returns null only when no lightweight accessor scope is active. A
     * present scope is authoritative, including a negative result; this is
     * what prevents the recorder fallback from accepting the right site on a
     * different invocation receiver.
     */
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

    private static void clearAccessorCallContexts(long regionToken) {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        if (context != null && context.regionToken == regionToken) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        }
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

    private static String conditionCodePosition(JsonElement condition) {
        if (condition == null || !condition.isJsonObject()) {
            return "";
        }
        return string(condition.getAsJsonObject(), "_code_position");
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

    /**
     * Resolves the Java boolean value selected by a Jimple zero test.  JVM
     * boolean-returning operations are consumed by {@code ifeq}/{@code ifne},
     * while the engine can retain the original higher-level Boolean IR (for
     * example an {@code OpStrExpression}) instead of manufacturing a numeric
     * {@code BinaryExpression}.  Attestation must relate those two exact
     * representations without treating arbitrary integer comparisons as
     * Boolean predicates.
     */
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
     * semantics are not part of the exact codec.  The operation set mirrors
     * the exact String predicate lowering in both SMT encoders.
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
        JsonObject normalized = copyJsonTree(original);
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
     * input becomes symbolic. The VM itself remains unpaused across the
     * concrete prefix so later Java frames retain the ability to propagate
     * symbolic state. Before this gate opens, branch hooks create no mappings
     * and do not parse the VM path condition. Materialization hooks still use
     * their own balanced observation pause.
     */
    private static void ensurePathRecordingStarted(ActiveRegion active) {
        if (active.pathRecordingStarted) return;
        active.pathRecordingStarted = true;
    }

    /**
     * Reports the first recorded branch outcome an activation drove the other
     * way.
     *
     * <p>A recording and its replay are two executions of the same concurrent
     * workload, so which activation first reaches a lazily shared region is
     * decided by scheduling.  An activation whose witnesses contradict a
     * recorded decision cannot attest the seed however it finishes, and
     * keeping it consumes the single result the task is allowed to emit.
     * Reporting the conflict lets that activation be skipped so a later one
     * competes, exactly as for a replay prefix that never matched.</p>
     *
     * <p>Only a witnessed contradiction counts.  A recorded site this
     * activation never decided may still be decided by a later one, and a
     * site the recording never planned is a whole-summary judgement the
     * importer owns; neither is a reason to discard evidence here.</p>
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

    /**
     * Records that an activation published nothing, and why.  {@code skipKind}
     * is the machine-readable half: a skip that never obtained the engine is
     * a scheduling outcome, while a skip that ran and contradicted its
     * recording is a finding about the path, and a reader that cannot tell
     * them apart reports one as the other.
     */
    private static void writeSkipped(RuntimeTask activation, String skipKind,
                                     String reason) {
        writeSkipped(activation, skipKind, reason, null);
    }

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
        boolean written = appendResult(result);
        int haltStatus = terminalSelectedSkipHaltStatus(skipKind, reason,
                written);
        if (haltStatus >= 0 && Boolean.getBoolean(
                HALT_AFTER_SELECTED_RESULT_PROPERTY)) {
            // A durable terminal skip is not a successful replay result.
            // Exit promptly but nonzero so the caller records the abandoned
            // replay instead of running the rest of a long-lived workload.
            Runtime.getRuntime().halt(haltStatus);
        }
    }

    static int terminalSelectedSkipHaltStatus(
            String skipKind, String reason, boolean written) {
        // A busy timeout belongs to a losing concurrent activation.  The
        // activation that owns the engine may still be producing the one
        // selected result, so halting here would kill valid evidence.  Keep
        // the skip as a scheduling diagnostic and let the owner finish.
        boolean terminal = SKIP_NOT_STARTED.equals(skipKind)
                && safe(reason).startsWith(
                "custom concolic System API is unavailable");
        if (!terminal) return -1;
        return written ? 3 : 2;
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
     * channels.  Long-running thread roots commonly exit because their owner
     * interrupts them during shutdown; that interrupt must not discard the
     * VM summary produced by the root's finally path.
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
     * trace can never manufacture a condition of the program under test. Every
     * failure here is swallowed: an observation must not alter the workload.
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
            System.err.println("CAUSYNTH-DIAG|"
                    + System.currentTimeMillis() + "|t"
                    + Thread.currentThread().getId() + "|heapMB"
                    + (Runtime.getRuntime().totalMemory()
                    - Runtime.getRuntime().freeMemory()) / 1048576L + "|"
                    + safe(event) + "|" + safe(detail));
        } catch (Throwable ignored) {
            // Diagnostics never fail the replay.
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

    /**
     * Indexed access to a serialized path condition without materializing
     * every element.
     *
     * <p>A branch hook needs exactly two facts from that document: how many
     * conditions the VM has accumulated, and the one element the VM's exact
     * event says this branch owns - an index the event stream, a few kilobytes
     * wide, already carries.  Building the whole tree to learn them costs one
     * object per node of a document that reaches tens of megabytes in a
     * long-lived replay, and every node but one is then dropped unread.  A
     * single pass records where each element begins and ends, and a requested
     * element is parsed from those same characters by the same parser.</p>
     *
     * <p>The scan accepts only what it can prove is a JSON array of complete
     * values; anything else - a non-array document, an unterminated string, a
     * lenient extension - is handed to the tree parser, so a document this
     * scanner does not understand is read exactly as it was before.</p>
     */
    static final class PathConditionElements {
        static final PathConditionElements EMPTY =
                new PathConditionElements(new JsonArray());
        private static final String SCAN_MODE = "SCAN";
        private static final String TREE_MODE = "TREE";

        private final String raw;
        private final int[] bounds;
        private final JsonArray tree;
        private final int size;

        private PathConditionElements(String raw, int[] bounds) {
            this.raw = raw;
            this.bounds = bounds;
            this.tree = null;
            this.size = bounds.length / 2;
        }

        private PathConditionElements(JsonArray tree) {
            this.raw = null;
            this.bounds = null;
            this.tree = tree;
            this.size = tree.size();
        }

        /**
         * Reads a serialized path condition.  A document that is not an array
         * of values carries no conditions, which is what the tree parser
         * reported for it before.
         */
        static PathConditionElements of(String raw) {
            int[] bounds = scanElements(raw);
            if (bounds != null) return new PathConditionElements(raw, bounds);
            JsonElement parsed = parseJson(raw);
            return parsed.isJsonArray()
                    ? new PathConditionElements(parsed.getAsJsonArray())
                    : EMPTY;
        }

        int size() {
            return size;
        }

        JsonElement get(int index) {
            if (index < 0 || index >= size) {
                throw new IndexOutOfBoundsException(
                        "path condition index " + index + " of " + size);
            }
            if (tree != null) return tree.get(index);
            return parseJson(raw.substring(
                    bounds[2 * index], bounds[2 * index + 1]));
        }

        /** Which reader answered, for the replay's own diagnostics. */
        String mode() {
            return tree == null ? SCAN_MODE : TREE_MODE;
        }

        /**
         * Bounds of every element of a JSON array, or {@code null} when the
         * document is not one this scanner can split with certainty.
         */
        private static int[] scanElements(String raw) {
            if (raw == null) return null;
            // One copy the scan can index directly.  A replay VM interprets
            // every bytecode, and a bounds-checked accessor call per character
            // of a document this size is most of the work otherwise.
            char[] document = raw.toCharArray();
            int length = document.length;
            int index = skipWhitespace(document, 0);
            if (index >= length || document[index] != '[') return null;
            index = skipWhitespace(document, index + 1);
            if (index >= length) return null;
            int[] bounds = new int[64];
            int count = 0;
            if (document[index] == ']') {
                index++;
            } else {
                while (true) {
                    if (!valueStart(document[index])) return null;
                    int end = skipValue(document, index);
                    if (end <= index) return null;
                    if (2 * count == bounds.length) {
                        bounds = Arrays.copyOf(bounds, 2 * bounds.length);
                    }
                    bounds[2 * count] = index;
                    bounds[2 * count + 1] = end;
                    count++;
                    index = skipWhitespace(document, end);
                    if (index >= length) return null;
                    char delimiter = document[index];
                    if (delimiter == ']') {
                        index++;
                        break;
                    }
                    if (delimiter != ',') return null;
                    index = skipWhitespace(document, index + 1);
                    if (index >= length) return null;
                }
            }
            return skipWhitespace(document, index) == length
                    ? Arrays.copyOf(bounds, 2 * count) : null;
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

    private enum MissingValue { INSTANCE }

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

    /** Activation-local counter for repeated executions of one static
     * output-capture hook.  A new region activation owns a new counter, so no
     * runtime event id or process-global invocation ordinal becomes replay
     * identity. */
    static final class OutputCaptureOccurrenceCounter {
        private final Map<String, Integer> occurrences =
                new LinkedHashMap<>();

        int observe(String captureBindingId, String outputSiteId) {
            String key = key(captureBindingId, outputSiteId);
            int occurrence = occurrences.getOrDefault(key, 0) + 1;
            occurrences.put(key, occurrence);
            return occurrence;
        }

        int observed(String captureBindingId, String outputSiteId) {
            return occurrences.getOrDefault(
                    key(captureBindingId, outputSiteId), 0);
        }

        private static String key(String captureBindingId,
                                  String outputSiteId) {
            String binding = safe(captureBindingId);
            return binding + "\u0000"
                    + firstNonBlank(outputSiteId, binding);
        }
    }

    /** Activation-local ordinals for repeated live-in materializations. */
    static final class MaterializationOccurrenceCounter {
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
            return occurrences.getOrDefault("ARGUMENT\u0000" + safe(method)
                    + "#arg" + argumentIndex, 0);
        }

        int field(String method, int unitIndex) {
            return observe("FIELD\u0000" + safe(method) + "#u"
                    + unitIndex);
        }

        private int observe(String key) {
            int occurrence = occurrences.getOrDefault(key, 0) + 1;
            occurrences.put(key, occurrence);
            return occurrence;
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

    /**
     * The two indices a selected mutation carries.
     *
     * <p>{@code selection} answers "which mutation inside this definition
     * invocation", so it restarts with every invocation; that scoping is what
     * lets one invocation reject an ambiguous choice of containers.
     * {@code version} answers "which version of this port's state", so it runs
     * monotonically across the activation's whole output boundary.  One field
     * cannot be both: two invocations each publishing their first selected
     * mutation are two distinct versions of the same port.
     */
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
        private PendingMutationCapture pending;
        private boolean ambiguousContainer;

        /** How this invocation absorbed one selected mutation. */
        enum Selection { ANCHORED, FOLDED, AMBIGUOUS, IGNORED }

        /**
         * A mutation relation denotes the container state at the definition
         * invocation's normal exit.  Repeating the selected mutator on the
         * same receiver is therefore the ordinary fold (addKeys puts every
         * key in one invocation) and keeps the first mutation as the anchor.
         * Only a second, different receiver makes the exit snapshot
         * ambiguous, and that poisons the whole invocation rather than
         * letting a later mutation re-anchor it.
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

        PendingMutationCapture pendingForTests() {
            return pending;
        }
    }

    private static final class ActiveRegion {
        private final long token;
        private final RuntimeTask activation;
        private final Object receiver;
        private final Thread thread;
        private final AtomicBoolean finished = new AtomicBoolean();
        private final List<String> symbolized = new ArrayList<>();
        private final List<String> unresolved = new ArrayList<>();
        private final Set<String> unresolvedUnique = new LinkedHashSet<>();
        private final List<JsonObject> branchMappings = new ArrayList<>();
        /**
         * Branches this activation executed before its symbolic gate opened.
         * They are pure execution observations: no path condition, no VM
         * event, and deliberately no occurrence ordinal, so nothing here can
         * be mistaken for a solvable predicate.  Their only use is attesting
         * that a recorded site really was reached.
         */
        private final List<JsonObject> concreteBranchWitnesses =
                new ArrayList<>();
        private final List<JsonObject> outputCaptures = new ArrayList<>();
        private final Set<String> materialized = new LinkedHashSet<>();
        private final Set<String> observedInputSlots =
                new LinkedHashSet<>();
        private final Set<String> appliedModelAssignments =
                new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        // Outcomes this activation actually witnessed at each static branch
        // site, restricted to the mappings a summary keeps.  A seed replay is
        // attested against the recorded outcome set of the same sites.
        private final Map<String, Set<Boolean>> witnessedOutcomes =
                new LinkedHashMap<>();
        private final MaterializationOccurrenceCounter
                materializationOccurrences =
                new MaterializationOccurrenceCounter();
        private final Map<String, Integer> accessorCallOccurrences =
                new LinkedHashMap<>();
        private final OutputCaptureOccurrenceCounter outputCaptureOccurrences =
                new OutputCaptureOccurrenceCounter();
        private final Map<String, List<String>> guardedOutputCaptureFailures =
                new LinkedHashMap<>();
        private final Map<String, PendingMutationCapture>
                pendingMutationCaptures = new LinkedHashMap<>();
        private final Map<String, Deque<MutationMethodScope>>
                mutationMethodScopes = new LinkedHashMap<>();
        private final Deque<Long> loopBudgetScopes = new ArrayDeque<>();
        private final LoopBackedgeBudget loopBackedges;
        private final Map<Long, PreparedBranch> preparedBranches =
                new LinkedHashMap<>();
        private final IdentityHashMap<Object, Long> objectTokens =
                new IdentityHashMap<>();
        private final IdentityHashMap<Object, Map<String, Object>>
                referenceAliasSnapshots = new IdentityHashMap<>();
        private final ReplayFieldWrites writtenFields =
                new ReplayFieldWrites();
        private final Map<Long, String> symbolizedObjectPorts =
                new LinkedHashMap<>();
        private final Map<String, Object> fieldAccessOwners =
                new LinkedHashMap<>();
        private final Set<String> ambiguousFieldAccessOwners =
                new LinkedHashSet<>();
        private final Map<String, Integer> associativeAccessOccurrences =
                new LinkedHashMap<>();
        private final ReplayProgress replayProgress;
        private final Set<String> decidedSites = new LinkedHashSet<>();
        private String lastDecisionSite = "";
        private boolean lastDecisionConcrete;
        private int replayCaptureWatermark = -1;
        private long nextObjectToken = 1L;
        private long preparedBranchSequence;
        private long loopBudgetScopeSequence;
        private int lastPathConditionSize;
        private JsonObject loopBoundCut;
        private JsonObject replayResourceCut;
        private boolean entrySetup;
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
         * Charges one body of this loop to the replay resource cap, returning
         * the cut that ends the activation once the cap is spent.
         *
         * <p>The cut detail is always recorded in {@code replayResourceCut}.
         * It is not itself an unresolved symbolic input: admission preserves
         * demanded ports captured before the cut.  If none was captured the
         * cap remains a resource-cut gap; otherwise uncaptured demanded ports
         * are reported individually and keep the prefix incomplete.</p>
         */
        private ReplayLoopResourceCut chargeLoopBody(String loopId) {
            int maxBodies = activation.maxLoopBodies(loopId);
            long entered = loopBackedges.recordBody(loopId);
            if (entered <= maxBodies) return null;
            ReplayLoopResourceCut cut = new ReplayLoopResourceCut(
                    loopId, maxBodies, entered);
            if (replayResourceCut == null) {
                replayResourceCut = cut.toJson();
            }
            return cut;
        }

        /**
         * Whether a replay-resource cut happened strictly after the VM had
         * captured at least one demanded output relation.
         *
         * <p>For a flip, captures made before the replay source decision are
         * deliberately excluded by {@link #replayCaptureWatermark}.  We do
         * not require unrelated recorded tail branches to run: the captured
         * producer prefix is the semantic boundary this task asked for.</p>
         */
        private boolean capturedOutputBeforeReplayResourceCut() {
            if (!activation.capturesOutputRelation
                    || replayResourceCut == null
                    || !ReplayLoopResourceCut.valid(replayResourceCut)
                    || !replayProgress.complete()) {
                return false;
            }
            List<JsonObject> captures = replayCaptureWatermark < 0
                    ? outputCaptures
                    : outputCaptures.subList(replayCaptureWatermark,
                    outputCaptures.size());
            return anyExactOutputRelation(
                    activation.capturesOutputRelation,
                    activation.outputCaptures, captures);
        }

        private LoopBoundCut loopBoundCut(
                String backedgeId, int maxTraversals,
                long attemptedTraversal, String reason) {
            LoopBoundCut cut = new LoopBoundCut(backedgeId, maxTraversals,
                    attemptedTraversal, reason);
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

        /**
         * Records that a branch executed while the symbolic gate was still
         * closed.  A concrete prefix decides real branches, and a recording
         * that saw one of them is describing execution that did happen; the
         * replay simply has no symbolic evidence to offer about it.
         *
         * <p>Only the first outcome of each kind per site is kept.  How often
         * an environment-sized loop revisits a site is not part of any
         * contract, and bounding this ledger by the instrumented slice keeps
         * a long concrete prefix from exhausting the replay heap.</p>
         */
        private void recordConcreteBranchWitness(
                String method, int unitIndex, boolean outcome) {
            String site = siteId(method, unitIndex);
            Set<Boolean> seen = witnessedOutcomes.get(site);
            if (seen != null && seen.contains(outcome)) return;
            witnessOutcome(site, outcome);
            concreteBranchWitnesses.add(concreteBranchWitness(
                    method, unitIndex, outcome));
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
                // The demanded decision has only just been made.  Every
                // relation captured before it is a version the flip did not
                // produce, so the boundary must wait for a later one.
                replayCaptureWatermark = outputCaptures.size();
            }
            return matched;
        }

        /**
         * Whether this activation has already walked a branch the recorded
         * replay prefix forbids.  The judgement is monotone: {@link
         * ReplayProgress} refuses to advance once it has named a
         * contradiction, so a prefix that is merely unfinished -- the state of
         * every activation that is still progressing normally -- never
         * answers true here.
         */
        private boolean replayPrefixContradicted() {
            return activation.replayContract != null
                    && replayProgress.failed();
        }

        /**
         * Records how the branch that just executed was decided, so the loop
         * hooks can tell a symbolically chosen continuation from a concrete
         * one.  The site is kept, not merely the method: only the branch that
         * decides a loop's continuation says anything about that loop's
         * guard, and the body of the loop holds branches of the same method.
         */
        private void noteBranchDecision(
                String method, int unitIndex, boolean concrete) {
            lastDecisionSite = siteId(method, unitIndex);
            lastDecisionConcrete = concrete;
            decidedSites.add(lastDecisionSite);
        }

        /**
         * True when this loop's own guard decided this body and was attested
         * to carry no symbolic expression.  An unattested, missing, or
         * foreign decision answers nothing and is charged to the budget.
         */
        private boolean enteredBodyOnConcreteGuard(
                String loopId, String guardSiteId) {
            boolean concrete = concreteGuardEnteredBody(loopId, guardSiteId,
                    decidedSites.contains(safe(guardSiteId)),
                    lastDecisionSite, lastDecisionConcrete);
            lastDecisionSite = "";
            lastDecisionConcrete = false;
            return concrete;
        }

        private int nextLocalMaterializationOccurrence(
                String method, int unitIndex, String local) {
            return materializationOccurrences.local(method, unitIndex,
                    local);
        }

        private int nextMethodArgumentMaterializationOccurrence(
                String method, int argumentIndex) {
            return materializationOccurrences.methodArgument(method,
                    argumentIndex);
        }

        private int currentMethodArgumentMaterializationOccurrence(
                String method, int argumentIndex) {
            return materializationOccurrences.observedMethodArgument(
                    method, argumentIndex);
        }

        private int nextFieldMaterializationOccurrence(
                String method, int unitIndex) {
            return materializationOccurrences.field(method, unitIndex);
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
            // The boundary-wide count orders this port's versions; it is never
            // replay identity, which stays the path seed.
            int version = outputCaptureOccurrences.observe(
                    request.captureBindingId(), request.outputSiteId());
            return new MutationCaptureIndex(++scope.observed, version);
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
         * executes it.  Long-lived region roots may call the same bounded
         * helper repeatedly; sharing one counter across those calls would cut
         * a later call after the earlier call spent part of its budget.
         */
        private String loopBudgetKey(String loopId) {
            return loopBudgetScopes.isEmpty() ? safe(loopId)
                    : LoopBackedgeBudget.scoped(loopId,
                    loopBudgetScopes.peek());
        }

        private boolean hasObservedOutputCapture(OutputCaptureSpec request) {
            return outputCaptureOccurrences.observed(
                    request.captureBindingId(), request.outputSiteId()) > 0;
        }

        private PreparedBranch prepareBranch(
                String method, int unitIndex, String expression,
                EngineApi api) throws Exception {
            String site = safe(method) + "#u" + unitIndex;
            if (!api.exactBranchEventsAvailable()) {
                addUnresolvedOnce(site
                        + ": custom JDK exact branch-event API is required");
                return null;
            }
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
            boolean outputBoundary = "OUTPUT_BOUNDARY".equals(exitKind)
                    && activation.capturesOutputRelation
                    && hasCompleteExactOutputBoundary();
            if ("OUTPUT_BOUNDARY".equals(exitKind) && !outputBoundary) {
                addUnresolvedOnce("INCOMPLETE_EXACT_OUTPUT_BOUNDARY");
            }
            boolean normal = "NORMAL".equals(exitKind)
                    || activation.capturesOutputRelation
                    && ("BOUNDED".equals(exitKind) || outputBoundary);
            for (OutputCaptureSpec request : activation.outputCaptures) {
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
                            + " hook occurrence(s) and captured " + matches);
                } else if (!normal && matches != 0) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": field output captured on " + exitKind
                            + " exit");
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

        private boolean captureEligible(OutputCaptureSpec request) {
            if (request == null || hasSuccessfulOutputCapture(request)) {
                return false;
            }
            return activation.capturePrerequisitesSatisfied(
                    request.captureBindingId(), symbolized,
                    observedInputSlots);
        }

        private boolean hasSuccessfulOutputCapture(
                OutputCaptureSpec request) {
            for (JsonObject capture : outputCaptures) {
                if (successfulExactOutputCapture(request, capture)) {
                    return true;
                }
            }
            return false;
        }

        private boolean hasCompleteExactOutputBoundary() {
            // A replay contract is consumed one hook after the branch it
            // demands is witnessed, so a window that closes on the witness
            // alone discards the very decision the flip was solved for.
            if (!replayProgress.complete()) return false;
            // A flip is asked what its decision does to the relation, so the
            // versions captured before that decision cannot answer it.
            List<JsonObject> captures = replayCaptureWatermark < 0
                    ? outputCaptures
                    : outputCaptures.subList(replayCaptureWatermark,
                    outputCaptures.size());
            boolean sites = activation.relationOnlySeed()
                    || demandedBranchSitesObserved(
                    activation.branchPolicies.keySet(),
                    witnessedOutcomes.keySet());
            boolean relation = completeExactOutputBoundary(
                    activation.capturesOutputRelation,
                    activation.outputCaptures, captures);
            diag("BOUNDARY_CHECK", "sites=" + sites
                    + " relation=" + relation
                    + " watermark=" + replayCaptureWatermark
                    + " captures=" + outputCaptures.size()
                    + " eligible=" + captures.size());
            return sites && relation;
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

        private Object fieldAccessOwner(String symbol) {
            String key = safe(symbol);
            return ambiguousFieldAccessOwners.contains(key)
                    ? null : fieldAccessOwners.get(key);
        }

        private void addUnresolvedOnce(String detail) {
            String value = safe(detail);
            if (!value.isEmpty() && unresolvedUnique.add(value)) {
                unresolved.add(value);
            }
        }

        /**
         * Holds one occurrence's capture failure without yet calling it a
         * gap.  A bounded replay observes the site several times, and a
         * failure at one occurrence says nothing about the relation when
         * another occurrence produced it; only a binding that never captured
         * anything has actually lost its output.
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

        private long objectToken(Object value) {
            if (value == null) return 0L;
            Long existing = objectTokens.get(value);
            if (existing != null) return existing;
            long token = nextObjectToken++;
            objectTokens.put(value, token);
            return token;
        }

        private void recordSymbolizedObject(String symbol, Object value) {
            long objectToken = objectToken(value);
            String previous = symbolizedObjectPorts.get(objectToken);
            symbolizedObjectPorts.put(objectToken, previous == null
                    || previous.equals(symbol) ? symbol : "");
        }

        private String symbolizedObjectPort(Object value) {
            Long token = value == null ? null : objectTokens.get(value);
            if (token == null) return "";
            return safe(symbolizedObjectPorts.get(token));
        }

        private int nextAssociativeAccessOccurrence(String inputSymbol) {
            int occurrence = associativeAccessOccurrences.getOrDefault(
                    inputSymbol, 0) + 1;
            associativeAccessOccurrences.put(inputSymbol, occurrence);
            return occurrence;
        }

        private int nextAccessorCallOccurrence(
                String caller, String site, String callee) {
            String key = safe(caller) + "\n" + safe(site) + "\n"
                    + safe(callee);
            int occurrence = accessorCallOccurrences.getOrDefault(key, 0) + 1;
            accessorCallOccurrences.put(key, occurrence);
            return occurrence;
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

        private boolean hasAppliedExactNullReferenceAssignment(
                SymbolizeAction action) {
            if (action == null || !action.declaresReferenceInput()) {
                return false;
            }
            int matches = 0;
            for (ModelAssignment assignment : activation.modelAssignments) {
                if (assignment.matches(action, null)
                        && assignment.exactNullReferenceModel(action)
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

        /**
         * Returns the traversal the latch charged for a body the header then
         * entered on a concrete guard.  The latch runs before that guard is
         * decided, so it cannot know which budget the transfer belongs to.
         */
        void releaseTraversal(String loopId) {
            int completed = traversals.getOrDefault(loopId, 0);
            if (completed > 0) traversals.put(loopId, completed - 1);
        }

        long recordGuardedTraversal(String loopId) {
            int completed = traversals.getOrDefault(loopId, 0);
            long next = (long) completed + 1L;
            if (next <= maxTraversals) {
                traversals.put(loopId, (int) next);
            }
            return next;
        }

        boolean canEnterBody(String loopId) {
            return completed(loopId) < maxTraversals;
        }

        int completed(String loopId) {
            return traversals.getOrDefault(loopId, 0);
        }

        static String scoped(String loopId, long invocation) {
            return safe(loopId) + SCOPE_SEPARATOR + invocation;
        }

        private static String unscoped(String loopId) {
            int separator = safe(loopId).indexOf(SCOPE_SEPARATOR);
            return separator < 0 ? safe(loopId)
                    : safe(loopId).substring(0, separator);
        }

        /**
         * Counts one body of this loop against the replay resource cap and
         * returns the body number just entered.
         *
         * <p>Separate from {@link #traversals}: that ledger is the unroll
         * bound, which only a symbolically decided continuation spends.  This
         * one is spent by every body, so a concrete walk and an uninstrumented
         * service loop are both accounted for.</p>
         */
        long recordBody(String loopId) {
            long entered = (long) bodies.getOrDefault(loopId, 0) + 1L;
            bodies.put(loopId, (int) Math.min(entered, Integer.MAX_VALUE));
            return entered;
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            for (Map.Entry<String, Integer> entry : traversals.entrySet()) {
                String loopId = unscoped(entry.getKey());
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
     *
     * <p>Distinct from {@link LoopBoundCut}: an unroll cut is a modelled
     * boundary of the bounded semantics.  A resource cut bounds replay work.
     * It remains a gap unless an output-relation task had already captured a
     * demanded output.  Captured ports may become a {@code BOUNDED} prefix;
     * missing demanded ports remain explicit and keep it incomplete.</p>
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
        private final long attemptedTraversal;
        private final String reason;

        LoopBoundCut(String backedgeId, int maxTraversals,
                     long attemptedTraversal, String reason) {
            super("concolic path cut at " + safe(backedgeId)
                    + " after " + maxTraversals
                    + " loop body iterations");
            this.backedgeId = safe(backedgeId);
            this.maxTraversals = maxTraversals;
            this.attemptedTraversal = attemptedTraversal;
            this.reason = safe(reason);
        }

        JsonObject toJson() {
            JsonObject encoded = new JsonObject();
            encoded.addProperty("kind", "LOOP_BOUND");
            encoded.addProperty("backedgeId", backedgeId);
            encoded.addProperty("maxBackedgeTraversals", maxTraversals);
            encoded.addProperty("maxLoopBodyIterations", maxTraversals);
            encoded.addProperty("attemptedTraversal", attemptedTraversal);
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
        private final List<String> fieldPath;
        private final String javaType;
        private final boolean observedEntryState;
        private final boolean observedNullLeaf;
        private final boolean observedReferenceLeaf;
        private final String observedPrimitiveValue;
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
            String explicitLeafSignature = string(json,
                    "leafFieldSignature");
            this.fieldPaths = new ArrayList<>(
                    FieldPathSpec.paths(json, "fieldPaths"));
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
            // field per hop.  Every prefix of that path is symbolized on its
            // own, so register each prefix against the declaration of the
            // field it ends at; otherwise only a one-hop path could name its
            // exact leaf and a deeper port would symbolize nothing.
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
            this.observedEntryState = json.has("observed")
                    && bool(json, "observed", false);
            this.observedPrimitiveValue = string(json, "primitiveValue");
            DeclaredField entryLeaf = FieldPathSpec.declaredField(
                    leafFieldSignaturesByPath.get(
                            joinFieldPath(this.fieldPath)));
            this.observedReferenceLeaf = entryLeaf != null
                    && referenceTypeDescriptor(javaTypeDescriptor(
                    entryLeaf.type()));
            this.observedNullLeaf = json.has("valueObjectId")
                    && !json.get("valueObjectId").isJsonNull()
                    && integer(json, "valueObjectId", -1) == 0;
        }

        /**
         * Returns whether this activation's live entry state agrees with the
         * value this occurrence was observed to read.  Only a leaf that the
         * evidence can actually decide participates; an unresolvable hop
         * leaves the activation eligible rather than silently rejecting it.
         */
        private EntryStateVerdict observedEntryStateVerdict(Object receiver) {
            if (!observedEntryState || !"RECEIVER_FIELD".equals(location)
                    || fieldPath.isEmpty()) {
                return EntryStateVerdict.UNDECIDED;
            }
            Object owner = receiver;
            for (int hop = 0; hop < fieldPath.size(); hop++) {
                String signature = leafFieldSignaturesByPath.get(
                        joinFieldPath(fieldPath.subList(0, hop + 1)));
                if (owner == null || signature == null) {
                    return EntryStateVerdict.UNDECIDED;
                }
                owner = readExactField(owner, signature);
                if (owner == MissingValue.INSTANCE) {
                    return EntryStateVerdict.UNDECIDED;
                }
            }
            if (!observedPrimitiveValue.isEmpty()) {
                return observedPrimitiveValue.equals(String.valueOf(owner))
                        ? EntryStateVerdict.MATCHES
                        : EntryStateVerdict.DIFFERS;
            }
            if (!observedReferenceLeaf) return EntryStateVerdict.UNDECIDED;
            return observedNullLeaf == (owner == null)
                    ? EntryStateVerdict.MATCHES : EntryStateVerdict.DIFFERS;
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

        private boolean acceptsAccessorOccurrence(int actualOccurrence) {
            return acceptsOccurrence(actualOccurrence);
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
         * materialization.  The runtime hook observes the consumed primitive
         * value rather than mutating process-global state, but model matching
         * must still use the same declared field path that the solver bound.
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
                                     String signature, String actualField) {
            return matchesField(actualMethod, actualUnitIndex, owner,
                    signature, actualField, null);
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
            // Accessor actions name their caller's invoke site in
            // accessSites, while this hook runs at the implementation's
            // field read. The exact accessor context below joins those two
            // sites and is authoritative for this case.
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
                    && !acceptsAccessorOccurrence(
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
            // statically known access owner.  Matching such an action by the
            // leaf name alone aliases unrelated same-named fields (for
            // example ExportedBlockKeys.allKeys and
            // BlockTokenSecretManager.allKeys).  Only an explicit owner or an
            // exact declared-field signature is authoritative enough to
            // symbolize a concrete field access.
            return !accessOwnerClass.isEmpty()
                    || !safe(signature).isEmpty()
                    && cell.contains(safe(signature));
        }

        private Object leafOwner(Object accessOwner) {
            return resolveFieldPathLeafOwner(accessOwner, fieldPath);
        }

        /**
         * Returns the exact declaration of the scalar/array leaf that will
         * actually be symbolized.  For a projected path the root hook
         * signature is deliberately not a fallback: it describes a
         * different heap field and would turn an intermediate reference into
         * a primitive action.
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
            this.engineSymbol = string(json, "engineSymbol");
            this.inputSymbol = string(json, "inputSymbol");
            this.valueType = string(json, "valueType");
            this.value = string(json, "value");
            this.referenceSourceInputSymbol = string(json,
                    "referenceSourceInputSymbol");
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
                    engineSymbol,
                    inputSymbol + ":" + joinFieldPath(path));
        }

        private boolean exactNullReferenceModel(SymbolizeAction action) {
            return action != null && action.declaresReferenceInput()
                    && inputSymbol.equals(action.symbol)
                    && modelIsNull
                    && ("NULL".equalsIgnoreCase(valueType)
                    || "null".equalsIgnoreCase(value));
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


    private static final class RootContextSelector {
        private final boolean present;
        private final String receiverRuntimeClass;
        private final String threadName;

        private RootContextSelector(boolean present,
                                    String receiverRuntimeClass,
                                    String threadName) {
            this.present = present;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = stableReplayThreadContext(threadName);
        }

        private static RootContextSelector from(JsonObject selector) {
            String kind = string(selector, "kind");
            if ("GLOBAL_INVOCATION".equals(kind)) {
                return new RootContextSelector(false, "", "");
            }
            String receiverClass = string(selector, "receiverClass");
            String thread = selector.has("thread")
                    ? string(selector, "thread") : "";
            if (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || !"RECEIVER_CONTEXT".equals(kind)
                    || selector.has("thread") && (thread.isEmpty()
                    || !thread.equals(thread.trim()))) {
                throw new IllegalArgumentException(
                        "rootSelector requires GLOBAL_INVOCATION or an exact "
                                + "RECEIVER_CONTEXT");
            }
            return new RootContextSelector(true, receiverClass, thread);
        }

        private boolean matches(Object receiver, String actualThreadName) {
            if (!present || receiver == null
                    || !receiverRuntimeClass.equals(
                    receiver.getClass().getName())) {
                return false;
            }
            return threadName.isEmpty()
                    || threadName.equals(stableReplayThreadContext(
                    actualThreadName));
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

    /**
     * Activation-local matcher for a solver replay.  It consumes only stable
     * static branch sites and region-local occurrences; trace call ids and
     * cross-run invocation ordinals never enter this state.
     */
    static final class ReplayProgress {
        private final List<ReplayEvent> expected = new ArrayList<>();
        private int next;
        private String failure = "prefix not yet observed";

        ReplayProgress(BranchReplayContract contract) {
            if (contract == null) return;
            for (BranchWitness witness : contract.orderedPrefix()) {
                // Several VM predicates may belong to one source branch.
                // The source-level activation selector consumes the exact
                // branch event once, not each internal VM decision.
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
        private final String regionId;
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
        private final Map<String, Set<String>> capturePrerequisites;
        private final Set<String> executionScopeMethods;
        private final BranchReplayContract replayContract;
        private final Map<String, Set<Boolean>> seedOutcomes;
        private final String stopAfterBranchSite;
        private final int stopAfterBranchOccurrence;
        private RuntimeTask(ExecutionTask task) {
            if (!task.executable()) {
                throw new IllegalArgumentException(
                        "runtime task must be executable");
            }
            JsonObject rootSelector = task.rootSelector();
            this.taskId = task.taskId();
            this.regionId = task.regionId();
            this.rootMethod = task.rootMethod();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            this.rootArgumentSelector = RootArgumentSelector.from(
                    rootSelector);
            this.declaredSymbolize = new ArrayList<>();
            this.symbolize = new ArrayList<>();
            this.branchPolicies = new LinkedHashMap<>();
            this.seedOutcomes = new LinkedHashMap<>();
            this.loopBound = task.loopBound();
            this.modelAssignments = new ArrayList<>();
            this.outputCaptures = new ArrayList<>();
            this.capturesOutputRelation =
                    task.goalKind().capturesOutputRelation();
            this.capturePrerequisites = new LinkedHashMap<>();
            this.executionScopeMethods = new LinkedHashSet<>();
            if (task.outputClosure() != null) {
                this.executionScopeMethods.addAll(
                        task.outputClosure().executionScope().methods());
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
            JsonObject stopAfterBranch = object(task.json(),
                    "stopAfterBranch");
            this.stopAfterBranchSite = string(stopAfterBranch, "siteId");
            this.stopAfterBranchOccurrence = integer(stopAfterBranch,
                    "occurrence", -1);
            for (JsonElement element : task.inputActions().all()) {
                JsonObject encoded = element.getAsJsonObject();
                SymbolizeAction action = new SymbolizeAction(encoded);
                this.declaredSymbolize.add(action);
                if (InputActionCatalog.Mode.SYMBOLIC.name().equals(
                        string(encoded, "mode"))) {
                    this.symbolize.add(action);
                }
            }
            indexCapturePrerequisites(task.outputClosure());
            boolean seedTask = this.replayContract == null
                    && !task.pathSeedKey().isEmpty()
                    && !relationOnlySeed();
            for (JsonElement element : task.branches()) {
                JsonObject branch = element.getAsJsonObject();
                String siteId = string(branch, "siteId");
                branchPolicies.put(siteId, string(branch, "policy"));
                if (seedTask) {
                    recordSeedOutcomes(siteId, branch.get("occurrences"));
                }
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
        }

        private boolean relationOnlySeed() {
            return capturesOutputRelation && replayContract == null;
        }

        private void indexCapturePrerequisites(
                OutputClosureContract closure) {
            if (closure == null) return;
            Set<String> symbolicPorts = new LinkedHashSet<>();
            Set<String> declaredPorts = new LinkedHashSet<>();
            for (SymbolizeAction action : symbolize) {
                symbolicPorts.add(action.symbol);
            }
            for (SymbolizeAction action : declaredSymbolize) {
                declaredPorts.add(action.symbol);
            }
            for (OutputClosureContract.Member member : closure.members()) {
                Set<String> required = new LinkedHashSet<>();
                Set<String> memberInputs = new LinkedHashSet<>();
                for (JsonElement element : array(member.slice(),
                        "inputPorts")) {
                    if (element.isJsonPrimitive()) {
                        String port = safe(element.getAsString());
                        memberInputs.add(port);
                        if (symbolicPorts.contains(port)) required.add(port);
                    }
                }
                String anchor = string(member.slice(),
                        "captureAnchorPort");
                if (!anchor.isEmpty()) {
                    if (!memberInputs.contains(anchor)
                            || !declaredPorts.contains(anchor)) {
                        throw new IllegalArgumentException(
                                "output capture anchor is not a declared "
                                        + "member input: " + anchor);
                    }
                    required.clear();
                    required.add(anchor);
                }
                for (JsonElement element : member.captures()) {
                    String binding = string(element.getAsJsonObject(),
                            "captureBindingId");
                    if (binding.isEmpty()
                            || capturePrerequisites.put(binding,
                            Collections.unmodifiableSet(
                                    new LinkedHashSet<>(required))) != null) {
                        throw new IllegalArgumentException(
                                "duplicate or missing output capture binding");
                    }
                }
            }
        }

        private boolean capturePrerequisitesSatisfied(
                String captureBindingId, List<String> symbolizedInputs,
                Set<String> observedInputs) {
            Set<String> required = capturePrerequisites.get(
                    safe(captureBindingId));
            if (required == null) return false;
            for (String port : required) {
                boolean present = observedInputs != null
                        && observedInputs.contains(port);
                for (String symbolized : symbolizedInputs) {
                    if (port.equals(symbolized)
                            || safe(symbolized).startsWith(port + ".")) {
                        present = true;
                        break;
                    }
                }
                if (!present) return false;
            }
            return true;
        }

        /**
         * Body entries this loop may run before the replay is cut.
         *
         * <p>A loop declared by a method the output closure names walks the
         * data the slice is stated over, so it is given the larger cap.  Every
         * other loop on an ordinary replay path is a service loop of the
         * long-lived root and receives the smaller resource cap.</p>
         */
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
         * site.  A malformed contract simply leaves the site unindexed: the
         * importer owns the fail-closed judgement over the whole summary, and
         * discarding an activation here on incomplete evidence would lose the
         * only result the task may emit.
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
                JsonElement outcome = element.getAsJsonObject().get(
                        "outcome");
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
            return validBranchPolicy(policy) ? policy : "EXPLORE";
        }

        private boolean stopAfterBranch(String siteId, int occurrence) {
            return !stopAfterBranchSite.isEmpty()
                    && stopAfterBranchSite.equals(safe(siteId))
                    && stopAfterBranchOccurrence == occurrence;
        }

        private static boolean validBranchPolicy(String policy) {
            return "EXPLORE".equals(policy)
                    || "PATH_ASSUMPTION".equals(policy);
        }

        private OutputCaptureSpec regionExitFieldCapture(
                String captureBindingId) {
            OutputCaptureSpec match = outputCapture(captureBindingId);
            return match != null && match.capturesRegionExitField()
                    ? match : null;
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

        private int observedEntryStateRank(Object receiver) {
            return ConcolicRegionRuntime.observedEntryStateRank(
                    declaredSymbolize, receiver);
        }

    }

    private static final class Configuration {
        private final Path resultFile;
        private final RuntimeTask task;

        private Configuration(Path resultFile, RuntimeTask task) {
            this.resultFile = resultFile;
            this.task = task;
        }

        private RuntimeTask select(String rootMethod, Object receiver,
                                     Object[] rootArguments) {
            return compatibleRoot(task.rootMethod, rootMethod,
                    task.rootContextSelector, task.rootArgumentSelector,
                    receiver, rootArguments, Thread.currentThread().getName())
                    ? task : null;
        }

        private static Configuration load() {
            String planValue = safe(System.getProperty(
                    "causynth.concolic.task.plan")).trim();
            String selectedTask = safe(System.getProperty(
                    "causynth.concolic.task.id")).trim();
            if (planValue.isEmpty()) {
                return new Configuration(null, null);
            }
            String resultValue = safe(System.getProperty(
                    "causynth.concolic.results")).trim();
            if (selectedTask.isEmpty() || resultValue.isEmpty()) {
                throw new IllegalStateException("Concolic runtime requires "
                        + "task id and result path with a task plan");
            }
            Path result = Paths.get(resultValue);
            Path plan = Paths.get(planValue);
            if (!Files.isRegularFile(plan)) {
                throw new IllegalStateException(
                        "Concolic task plan not found: " + plan);
            }
            RuntimeTask selected = null;
            try (BufferedReader reader = Files.newBufferedReader(plan,
                    StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) continue;
                    JsonElement parsed = new JsonParser().parse(line);
                    if (!parsed.isJsonObject() || selected != null) {
                        throw new IllegalStateException(
                                "task plan must contain exactly one object");
                    }
                    selected = new RuntimeTask(ExecutionTask.decode(
                            parsed.getAsJsonObject()));
                    if (!selected.taskId.equals(selectedTask)) {
                        throw new IllegalStateException(
                                "task plan contains non-selected task "
                                        + selected.taskId);
                    }
                }
            } catch (IOException | RuntimeException exception) {
                throw new IllegalStateException("Causynth rejected "
                        + "task plan " + plan + ": "
                        + exception.getMessage(), exception);
            }
            if (selected == null) {
                throw new IllegalStateException("Selected execution task "
                        + selectedTask + " is absent in " + plan);
            }
            return new Configuration(result, selected);
        }
    }

    /**
     * Orders several occurrences of one region template without any global
     * invocation ordinal.  Two occurrences of the same root differ because
     * they read different state on entry, and an occurrence whose live entry
     * values still agree with the recording is the better candidate for the
     * single engine.
     *
     * <p>This is a value-wise comparison -- string equality for primitives,
     * null against non-null for references -- so it can say which candidate
     * looks more like the recorded one but not whether a candidate walks the
     * recorded path.  It therefore ranks and never refuses: the recorded
     * branch prefix is the only judgement allowed to reject an activation,
     * and a rejected activation gives the engine back at once.</p>
     */
    static int observedEntryStateRank(
            List<SymbolizeAction> declared, Object receiver) {
        int rank = ENTRY_STATE_RANK_UNDECIDED;
        for (SymbolizeAction action : declared) {
            EntryStateVerdict verdict =
                    action.observedEntryStateVerdict(receiver);
            if (verdict == EntryStateVerdict.DIFFERS) {
                return ENTRY_STATE_RANK_MISMATCH;
            }
            if (verdict == EntryStateVerdict.MATCHES) {
                rank = ENTRY_STATE_RANK_MATCHES;
            }
        }
        return rank;
    }

    private static boolean compatibleRoot(
            String selectedMethod, String actualMethod,
            RootContextSelector context, RootArgumentSelector arguments,
            Object receiver, Object[] rootArguments, String threadName) {
        if (!safe(selectedMethod).equals(safe(actualMethod))) return false;
        if (context.present && !context.matches(receiver, threadName)) {
            return false;
        }
        return !arguments.present || arguments.matches(rootArguments);
    }

    /** Test seam for the ordinal-free replay selector. */
    static boolean compatibleRootForTests(
            JsonObject rootSelector, String selectedMethod,
            String actualMethod, Object receiver, Object[] rootArguments,
            String threadName) {
        return compatibleRoot(selectedMethod, actualMethod,
                RootContextSelector.from(rootSelector),
                RootArgumentSelector.from(rootSelector), receiver,
                rootArguments, threadName);
    }

    private static final class EngineApi {
        private final Method startRegion;
        private final Method symbolizeWithPrefix;
        private final Method symbolizeField;
        private final Method symbolizeExactField;
        private final Method snapshotContainer;
        private final Method trackContainer;
        private final Method getExpression;
        private final Method getFieldExpression;
        private final Method finishRegion;
        private final Method getPathCondition;
        private final Method pausePathCondition;
        private final Method resumePathCondition;
        private final Method markBranch;
        private final Method getBranchEvents;
        private final Method cleanupEnd;

        private EngineApi(Method startRegion,
                          Method symbolizeWithPrefix, Method symbolizeField,
                          Method symbolizeExactField,
                          Method snapshotContainer,
                          Method trackContainer,
                          Method getExpression,
                          Method getFieldExpression,
                          Method finishRegion, Method getPathCondition,
                          Method pausePathCondition,
                          Method resumePathCondition,
                          Method markBranch, Method getBranchEvents,
                          Method cleanupEnd) {
            this.startRegion = startRegion;
            this.symbolizeWithPrefix = symbolizeWithPrefix;
            this.symbolizeField = symbolizeField;
            this.symbolizeExactField = symbolizeExactField;
            this.snapshotContainer = snapshotContainer;
            this.trackContainer = trackContainer;
            this.getExpression = getExpression;
            this.getFieldExpression = getFieldExpression;
            this.finishRegion = finishRegion;
            this.getPathCondition = getPathCondition;
            this.pausePathCondition = pausePathCondition;
            this.resumePathCondition = resumePathCondition;
            this.markBranch = markBranch;
            this.getBranchEvents = getBranchEvents;
            this.cleanupEnd = cleanupEnd;
        }

        private boolean available() {
            return startRegion != null
                    && symbolizeWithPrefix != null
                    && symbolizeExactField != null
                    && trackContainer != null
                    && getExpression != null
                    && getFieldExpression != null
                    && finishRegion != null
                    && getPathCondition != null
                    && pausePathCondition != null
                    && resumePathCondition != null
                    && cleanupEnd != null;
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

        private void symbolize(Object value, String prefix) throws Exception {
            symbolizeWithPrefix.invoke(null, value, prefix);
        }

        private void symbolizeField(Object owner, String field, String prefix)
                throws Exception {
            if (symbolizeField == null) {
                throw new UnsupportedOperationException(
                        "custom concolic System.symbolizeField API is unavailable");
            }
            symbolizeField.invoke(null, owner, field, prefix);
        }

        private void symbolizeExactField(
                Object owner, String fieldSignature, String prefix)
                throws Exception {
            DeclaredField field = FieldPathSpec.declaredField(
                    safe(fieldSignature));
            if (symbolizeExactField == null) {
                throw new UnsupportedOperationException(
                        "custom concolic exact-field API is unavailable");
            }
            if (field == null) {
                throw new UnsupportedOperationException(
                        "no exact declared field for symbolized leaf: "
                                + safe(fieldSignature));
            }
            symbolizeExactField.invoke(null, owner, field.owner(),
                    field.name(), javaTypeDescriptor(field.type()), prefix);
        }

        private boolean snapshotContainer(
                Object value, Object[] keys, Object[] values, int kind)
                throws Exception {
            if (snapshotContainer == null) {
                throw new UnsupportedOperationException(
                        "custom concolic container-snapshot API is unavailable");
            }
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

        private String pathCondition() throws Exception {
            return String.valueOf(getPathCondition.invoke(null));
        }

        private void pausePathCondition() throws Exception {
            pausePathCondition.invoke(null);
        }

        private void resumePathCondition() throws Exception {
            resumePathCondition.invoke(null);
        }

        private boolean exactBranchEventsAvailable() {
            return markBranch != null && getBranchEvents != null;
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

        private static EngineApi load() {
            Class<System> system = System.class;
            return new EngineApi(
                    method(system, "startConcolicRegion", String.class, String.class),
                    method(system, "symbolize", Object.class, String.class),
                    method(system, "symbolizeField", Object.class,
                            String.class, String.class),
                    method(system, "symbolizeExactField", Object.class,
                            String.class, String.class, String.class,
                            String.class),
                    method(system, "snapshotContainerExpression",
                            Object.class, Object[].class, Object[].class,
                            int.class),
                    method(system, "trackContainerExpression",
                            Object.class, String.class),
                    method(system, "getSymbolicExpression", Object.class),
                    method(system, "getSymbolicFieldExpression",
                            Object.class, String.class, String.class,
                            String.class, Object.class),
                    method(system, "finishConcolicRegion"),
                    method(system, "getPathCondition"),
                    method(system, "pauseConcolicPathCondition"),
                    method(system, "resumeConcolicPathCondition"),
                    method(system, "markConcolicBranch",
                            String.class, int.class),
                    method(system, "getConcolicBranchEvents"),
                    method(system, "endConcolic"));
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
