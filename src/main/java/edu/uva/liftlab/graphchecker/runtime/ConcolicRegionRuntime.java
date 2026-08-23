package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;
import edu.uva.liftlab.graphchecker.concolic.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.concolic.BranchReplayContract;
import edu.uva.liftlab.graphchecker.concolic.BranchWitness;
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
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.contract.ExecutionTask;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.contract.InputActionCatalog;
import edu.uva.liftlab.graphchecker.contract.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.contract.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.contract.OutputCaptureSpec;
import edu.uva.liftlab.graphchecker.contract.OutputClosureContract;
import edu.uva.liftlab.graphchecker.contract.RegionInstancePlan;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringReader;
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
    /**
     * Guards the process-exit barrier alone.  Symbolic execution is no longer
     * serialized: with a workload session open, several campaign tasks may be
     * live on different threads at the same time.
     */
    private static final Object PUBLICATION_LOCK = new Object();
    private static final AtomicLong PUBLICATION_THREAD_COUNTER =
            new AtomicLong();
    /**
     * JSON decoding and durable result publication must not hold an RPC
     * handler after its VM-owned read-outs are complete.  The campaign is
     * bounded, so a small fixed daemon pool with a bounded queue is enough;
     * daemon threads cannot keep an otherwise finished workload alive, while
     * {@link #awaitSelectedResultPublications()} remains the explicit durable
     * publication barrier.
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
     * publication.  This is the first half of the process-exit barrier: an
     * activation becomes live before its region is ACTIVE and stops being
     * live only once {@link #finish} has registered its publication or the
     * activation has been abandoned.  Without it the barrier would open in
     * the interval between the two.  Guarded by {@link #PUBLICATION_LOCK}.
     */
    private static int liveSelectedRegions;
    private static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    /**
     * Monotonic ordinal of one recorded-evidence read-out batch.
     *
     * <p>It is the only recency answer this layer publishes. A bounded VM
     * store evicts its oldest entries, so "the snapshot with more rows" is not
     * "the later snapshot", and a consumer that ranked read-outs by size would
     * routinely keep the stale one. The counter is process-wide and shared by
     * every activation, so two batches are always comparable.</p>
     */
    private static final AtomicLong EVIDENCE_SNAPSHOTS = new AtomicLong();
    static final String HALT_AFTER_SELECTED_RESULT_PROPERTY =
            "causynth.concolic.halt.after.selected.result";
    /**
     * Why an activation never published a region result.  A skip that was
     * never admitted and a skip that ran and contradicted its recording are
     * different findings, and collapsing them makes a plan artifact
     * indistinguishable from an infeasible path.
     */
    static final String SKIP_NOT_STARTED = "NOT_STARTED";
    static final String SKIP_REPLAY_PREFIX_UNMATCHED =
            "REPLAY_PREFIX_UNMATCHED";
    static final String SKIP_SEED_OUTCOME_CONFLICT = "SEED_OUTCOME_CONFLICT";
    /**
     * A candidate ran to its terminal and was not the occurrence its plan row
     * addressed: it ran on another source, or inside another request scope.
     *
     * <p>Not a failure of the occurrence and not a coverage gap.  It is the
     * ordinary answer of an address that names a cause rather than a
     * position: the run held an activation of the same root that this plan
     * row did not mean, so the address stays open for the next one.</p>
     */
    static final String SKIP_OCCURRENCE_ANCHOR_UNMATCHED =
            "OCCURRENCE_ANCHOR_UNMATCHED";
    /**
     * A target candidate ran to its terminal without reaching the target
     * event its plan row declared.
     *
     * <p>Not a failure and not a coverage gap: it is the ordinary answer of
     * an address that several activations of one region on one source can
     * satisfy.  The address stays open for the next candidate.</p>
     */
    static final String SKIP_TARGET_EVENT_NOT_REACHED =
            "TARGET_EVENT_NOT_REACHED";
    /**
     * The source this occurrence is anchored on never existed in this run.
     *
     * <p>A refusal and a coverage statement are different findings and this
     * separates them.  {@link #SKIP_OCCURRENCE_ANCHOR_UNMATCHED} says the
     * activation belongs to another owner - the address worked and rejected
     * it.  This says no activation could have matched, because the anchored
     * logical source and lifecycle epoch were never registered here at all:
     * the replay is a narrower envelope than the recording, typically because
     * it did not reach a restart that the recording did.  Collapsing the two
     * would hide that, and the epoch cannot be dropped from the address to
     * avoid it - post-rotation state is the phenomenon, so equating epochs
     * would erase what the model exists to express.</p>
     */
    static final String SKIP_ANCHOR_SOURCE_NEVER_EXISTED =
            "ANCHOR_EPOCH_NOT_REACHED";
    /**
     * The region root was still running when the workload ended, so this
     * occurrence never reached {@code NORMAL}, {@code THROW} or a bounded
     * {@code CUT}.
     *
     * <p>A coarse occurrence ends at its own terminal, so an activation that
     * has none has published nothing and never will.  Naming it per task is
     * the difference between a campaign that fails closed on one occurrence
     * and a campaign that waits for a service thread forever.</p>
     */
    static final String SKIP_TERMINAL_NEVER_REACHED =
            "TERMINAL_NEVER_REACHED";
    /**
     * How long the process-exit barrier waits for a live activation that is
     * making no instrumented progress.
     *
     * <p>Not a task budget and not a semantic bound: the barrier runs after
     * the workload's own control flow has ended, so every activation still
     * live belongs to a thread the workload does not wait for.  The wait is
     * restarted by any publication or by any loop body those activations
     * still charge, so it is only ever spent on an occurrence that is doing
     * nothing at all.</p>
     */
    private static final long TERMINAL_GRACE_MILLIS = 30_000L;
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
    /** Session this JVM opened for its workload, or zero when it opened none. */
    private static volatile long workloadSessionId;

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
     * Mutes this layer's own bookkeeping for the duration of one evidence
     * call, and must be paired with {@link #endBookkeeping()} in a finally.
     *
     * <p>Every evidence entry point below - handoff, selected boundary, shared-state
     * selection and read-out - is entered through this pair.  It has to be:
     * this layer reflects, parses JSON, builds strings and walks collections
     * holding the very objects the workload symbolized, and an unmuted call
     * records hundreds of conditions of GraphChecker's own control flow into
     * the workload's path condition and mints session expressions for
     * GraphChecker's own strings.  That is not merely noise - the summary
     * would claim conditions the program never evaluated, and a writer's path
     * guard would be conjoined with its observer's.</p>
     *
     * <p>The mute spans the native call as well, which is safe: every VM
     * operation this layer invokes is an explicit one, admitted by an active
     * context rather than by an unpaused one.</p>
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
     * backedge. Calls outside the selected active region are deliberately a
     * no-op. All map and policy operations execute while VM path-condition
     * recording is paused, so this synthetic guard cannot become a symbolic
     * branch event of the program under test.
     *
     * <p>The fixed bound allows exactly {@code K} loop-body iterations. The
     * first body precedes any backedge, so only attempts {@code 1..K-1} may
     * complete. Backedge attempt {@code K}, made after body {@code K}, closes
     * symbolic observation before body {@code K+1}. The application loop then
     * continues concretely: a modeling bound must not terminate a service
     * thread in the workload.</p>
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
            int runtimeMax = instrumentedMaxTraversals;
            if (edge.isEmpty() || !loopBoundMatchesPlan(
                    active, edge, runtimeMax)) {
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
                    instrumentedMaxTraversals,
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
                                instrumentedMaxTraversals,
                                0L, "BOUND_HOOK_RESUME_FAILURE");
                    }
                }
            }
        }
        endAtCut(active, cut);
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
     * invocation. Repeated guard evaluations in the same invocation must
     * observe the same value; a disagreement is retained as a coverage gap,
     * never rewritten into a condition-loop prefix.
     */
    public static void recordLoopCardinality(
            String loopId, int cardinality) {
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
        ActiveRegion active = activeRegion();
        if (active == null) return;
        beginBookkeeping();
        try {
            active.completeLoopCardinality(safe(loopId));
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Confirms that a loop hook was emitted from this task plan.
     *
     * <p>The immutable class tree already carries the selected K_L.  When
     * the hook names a declared guard, the task must state exactly that same
     * value; otherwise a stale tree is refused.  A latch with no declaration
     * may carry the bound resolved from another guard of the same natural
     * loop, so it is only checked against the plan's admitted range.</p>
     */
    private static boolean loopBoundMatchesPlan(
            ActiveRegion active, String encodedLoopId, int bound) {
        return active.activation.loopBound.acceptsInstrumentedBound(
                encodedLoopId, bound);
    }

    /**
     * Publishes the bounded prefix and detaches symbolic observation.
     *
     * <p>No tool exception enters the application. The remaining iterations
     * execute normally with no active symbolic region; the emitted relation
     * still ends at {@code CUT}.</p>
     */
    private static void endAtCut(ActiveRegion active, Error cut) {
        if (cut == null) return;
        finishRootInvocation(active.token, "CUT", "", null);
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
        // A publication owns the configuration and test hooks that were live
        // when it was queued.  Never clear or replace those objects while a
        // daemon publisher can still observe them.  Live activations are not
        // waited here: reset is also the recovery path for a test whose setup
        // failed after entering a region but before reaching its terminal.
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
        ACTIVE.clear();
        CURRENT_TOKEN.remove();
        ROOT_INVOCATION_FRAMES.remove();
        CURRENT_ACCESSOR_CALL_CONTEXT.remove();
        PENDING_RESPONSE_ATTACH_PORTS.remove();
        INBOUND_RESPONSE_PRODUCER_ARM.remove();
        beforePublicationDecodeForTests = null;
        synchronized (RESPONSE_ARM_LOCK) {
            IN_FLIGHT_RESPONSE_PRODUCER_ARMS.clear();
        }
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
     * Waits until every selected activation that is live or already
     * publishing a result has either durably closed its JSONL record or
     * reported a write failure.  Process launchers call this before forcibly
     * terminating leaked system threads; otherwise a concurrent
     * {@link #finish} can be killed between writing a large JSON object and
     * its closing brace/newline.
     */
    public static void awaitSelectedResultPublications() {
        boolean interrupted = false;
        List<ActiveRegion> stranded = new ArrayList<>();
        synchronized (PUBLICATION_LOCK) {
            // The live-region count covers the interval after a selected
            // activation is ACTIVE but before finish registers publication.
            // Once finish has registered it, the publication counter keeps
            // the barrier closed through the durable append.
            long progress = liveRegionProgress();
            long deadline = System.nanoTime()
                    + TERMINAL_GRACE_MILLIS * 1_000_000L;
            while (liveSelectedRegions > 0
                    || resultPublicationsInFlight > 0) {
                long remaining = deadline - System.nanoTime();
                if (remaining <= 0L) {
                    // Nothing published and no body ran for the whole grace.
                    // A durable append in flight is always waited out: it is
                    // finite and its region has already reached its terminal.
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

    /**
     * Names one activation whose root never reached a terminal.
     *
     * <p>The VM is deliberately untouched.  The root's thread is still
     * running and still owns that symbolic context; detaching it from here
     * would take the path condition away from a thread that is using it, and
     * a summary read out from another thread would not be this occurrence's.
     * What this publishes is the exact statement that matters: the task ran,
     * it never terminated, and it has no relation to import.</p>
     */
    private static void strandWithoutTerminal(ActiveRegion active) {
        if (!active.finished.compareAndSet(false, true)) return;
        active.abandoned = true;
        ACTIVE.remove(active.token, active);
        endLiveSelectedRegion();
        JsonObject evidence = new JsonObject();
        evidence.addProperty("runtimeThread", active.thread.getName());
        evidence.addProperty("runtimeThreadState",
                active.thread.getState().name());
        evidence.addProperty("chargedLoopBodies", active.chargedLoopBodies);
        // A count, not the rows: the root's thread still owns that list, and
        // half a relation with no terminal is not evidence of one anyway.
        evidence.addProperty("outputCaptureCount",
                active.outputCaptures.size());
        writeSkipped(active.activation, SKIP_TERMINAL_NEVER_REACHED,
                "the region root was still running "
                        + TERMINAL_GRACE_MILLIS
                        + "ms after the workload ended and charged no loop "
                        + "body in that time, so this occurrence reached no "
                        + "NORMAL, THROW or bounded CUT terminal",
                evidence);
    }

    /**
     * Marks one selected activation live.  It is called before the region can
     * become ACTIVE, so no window exists in which a started activation is
     * invisible to the process-exit barrier.
     */
    static void beginLiveSelectedRegion() {
        synchronized (PUBLICATION_LOCK) {
            liveSelectedRegions++;
            PUBLICATION_LOCK.notifyAll();
        }
    }

    /**
     * Marks one selected activation no longer live.  Every path that ends an
     * activation -- refusal, start failure, abandonment, or a finished
     * result -- calls this exactly once, and the result paths call it only
     * after {@link #beginSelectedResultPublication} has taken over.
     */
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
     * <p>The workload owns this lifetime, not a region: with the session open
     * a region exit no longer tears down the expression arena, broker,
     * symbolic heap, field versions, or event ledger, so an expression a
     * producer exported survives that producer's thread and region until the
     * workload ends.  Opening does not attach the caller; a thread gains
     * symbolic state only by entering a region.</p>
     *
     * <p>It is a no-op when no concolic campaign is configured, and a no-op on
     * a JDK without the natives -- an ordinary JDK must keep running the same
     * workloads, and an activation there already names the missing API.</p>
     *
     * @return an empty string on success, otherwise a named diagnostic
     */
    public static String openWorkloadSession() {
        if (configuration().tasks.isEmpty()) return "";
        EngineApi api = engine();
        if (!api.workloadSessionAvailable()) return "";
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
        workloadSessionId = status;
        return "";
    }

    /**
     * Closes the session opened by {@link #openWorkloadSession}.
     *
     * <p>A close is refused while threads remain attached, and the session
     * stays usable when that happens.  That outcome is reported by name: a
     * workload that leaked a live region has lost the guarantee that the
     * session tore down exactly once, and silence would hide it.</p>
     *
     * @return an empty string on success or when nothing was opened,
     *         otherwise a named diagnostic
     */
    public static String closeWorkloadSession() {
        // Closing the workload is the general durability boundary, regardless
        // of which launcher owns it.  Publication threads use no VM context,
        // but they are daemon threads and may otherwise be stopped after this
        // method returns with a result still only in memory.
        awaitSelectedResultPublications();
        long sessionId = workloadSessionId;
        if (sessionId == 0L) return "";
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
        return admitted == null ? null
                : startSymbolicRegion(admitted, receiver);
    }

    /**
     * Decides which planned occurrence this root invocation admits, muted.
     *
     * <p>The decision itself is this bridge's own control flow over the
     * workload's own objects: {@code RootContextSelector.matches} compares the
     * root receiver against {@code null} and against a declared class, and a
     * campaign instruments one entry hook per plan row, so every later hook on
     * a thread that already holds a selected symbolic object evaluates that
     * comparison again.  Unmuted, each evaluation appended a condition of
     * GraphChecker's own to the workload's path condition, and the occurrence
     * summary would state a branch the program never took.  The first
     * two conditions of the first full RPC-slice campaign were exactly this.
     *
     * <p>The mute cannot extend into {@link #startSymbolicRegion}: Zero
     * decides whether a newly entered Java frame may propagate symbolic state
     * when that frame is pushed, so the region start owns its own pause
     * discipline and must not inherit one.</p>
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
     * Starts one planned region occurrence.  A task owns one VM region, one
     * path condition and one result row; symbolic values cross RPC boundaries
     * through the VM handoff broker rather than by sharing a Java activation.
     */
    private static ActiveRegion startSymbolicRegion(
            RuntimeTask admitted, Object receiver) {
        beginLiveSelectedRegion();
        EngineApi api = engine();
        if (!api.available()) {
            writeSkipped(admitted, SKIP_NOT_STARTED,
                    "custom concolic System API is unavailable");
            configuration().releaseCandidate(admitted);
            endLiveSelectedRegion();
            return null;
        }
        boolean engineStarted = false;
        boolean pathConditionPaused = false;
        ActiveRegion active = null;
        try {
            api.start(admitted.regionId, admitted.taskId);
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
            active = new ActiveRegion(TOKEN_COUNTER.incrementAndGet(),
                    admitted, receiver, Thread.currentThread());
            ACTIVE.put(active.token, active);
            CURRENT_TOKEN.set(active.token);
            // A delivery can establish the causal request immediately before
            // the selected handler entry.  Snapshot that already-current
            // context now; later SEND/RECEIVE events continue to add context
            // through observeCausalSource.
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
                // long-lived receiver has no alias of its own.  An inherited
                // submitter context (the in-process test driver is the common
                // case) is not evidence that this receiver belongs to that
                // submitter and must not poison terminal attribution.
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
                    "engine start failed: " + rootCause(throwable));
            configuration().releaseCandidate(admitted);
            endLiveSelectedRegion();
            return null;
        }
    }

    /** Performs the declared entry setup for one selected occurrence. */
    private static void prepare(ActiveRegion active) {
        if (active.prepared) return;
        active.prepared = true;
        active.entrySetup = true;
        try {
            symbolizeReceiverFields(active, engine());
        } finally {
            active.entrySetup = false;
        }
        selectDeclaredSharedCarriers(active);
        for (JsonObject gate : active.activation.readCutGates) {
            installReadCutGate(gate);
        }
    }

    /**
     * Instrumentation-facing root entry.  A zero-token placeholder is pushed
     * before {@link #enterRegion(String, String, Object, Object[])} starts the
     * engine,
     * then filled without another allocation.  If entry fails, that exact
     * placeholder remains for the injected exceptional or original-handler
     * cleanup path; this prevents a caught same-root entry failure from
     * exposing an enclosing frame.  Token zero is likewise retained after a
     * successful unselected entry as its exact ownership marker.
     */
    public static long enterRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        // Several hooks for one selected root may appear in nested replay
        // helpers. Count the outer root once and leave an exact token-zero
        // frame for the nested hook's own exit cleanup.
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
        selectAccessOwnerSharedCarriers(active, owner, fieldSignature, true,
                method, unitIndex, occurrence);
        // An accessor can be an exact causal slot without being a new
        // symbolic live-in.  In particular, a field written earlier in this
        // same region already carries its symbolic expression and must not be
        // re-symbolized as an independent variable.  Record that the exact
        // slot was observed before applying the written-field guard.
        for (SymbolizeAction action : active.activation.declaredSymbolize) {
            if (action.matchesField(method, unitIndex, owner,
                    fieldSignature, fieldName)
                    && action.acceptsDirectFieldOccurrence(occurrence)
                    && !active.plannedProducerPrerequisitePending(
                    action.symbol)) {
                active.observedInputSlots.add(action.symbol);
            }
        }
        boolean writtenInThisRegion = active.writtenFields.contains(
                owner, fieldSignature);
        if (writtenInThisRegion) {
            boolean composedInput = false;
            for (SymbolizeAction action : active.activation.symbolize) {
                if (action.intraRegionComposedInput()
                        && action.matchesField(method, unitIndex, owner,
                        fieldSignature, fieldName)
                        && action.acceptsDirectFieldOccurrence(occurrence)) {
                    composedInput = true;
                    break;
                }
            }
            if (!composedInput) return;
        }
        active.snapshotReferenceAliasSources(owner);
        for (SymbolizeAction action : active.activation.symbolize) {
            if (!action.matchesField(method, unitIndex, owner, fieldSignature,
                    fieldName)
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
                // an earlier selected output.  A replay may reach the same
                // static accessor with a different concrete pre-state; seed
                // the observed primitive before creating the symbolic leaf
                // so this replay represents the selected trace case.  A
                // solver assignment, when present, remains authoritative.
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
                if (action.observedFieldReceiverRoot()
                        && "BOUNDED_CONTAINER_STATE".equals(
                        action.symbolicDemand)
                        && value instanceof Map<?, ?>) {
                    // The runtime trace selected this exact access site and
                    // supplied the actual declaring-field receiver.  Select
                    // the map itself now, before the following get/put/remove
                    // executes.  No object search or value matching occurs.
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
     * The container identity and access ordinal form the replay selector; the
     * key and map cardinality remain concrete workload state.
     *
     * <p>This hook mutes itself, in the shape {@link #checkLoopBackedge} uses:
     * the thread-local region check happens first and returns before any
     * engine call, and only an admitted call pays the pause/resume pair.  The
     * pipeline currently brackets the call site with
     * {@code pauseObservation()} / {@code resumeObservation()}, so an
     * inactive hook paid two reflective invokes into a native gate before
     * reaching the {@code activeRegion() == null} return above - and HDFS
     * startup is {@code HashMap}-intensive, so it paid them in hot startup
     * code.  With the mute owned here, that bracket is redundant and can be
     * dropped from the emitter (CausynthPipeline.java:2346-2373).  It must not
     * be dropped before this half lands: without a mute, the map lookups,
     * string building and container write below would record this layer's own
     * control flow into the workload's path condition.</p>
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
        String inputSymbol = active.symbolizedInputPort(container);
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

    /**
     * Selects a declared access-owner carrier on the object a selected field
     * store is about to write, before the store executes.
     *
     * <p>A location publishes versions only from the moment it is selected,
     * and the VM refuses a selection once the slot exists.  Binding this shape
     * at reads alone therefore made every writer publish nothing: the reader's
     * selection created the store, its {@code INITIAL} version held the
     * already-written concrete value, and the producer's symbolic expression
     * had no version to live in.  Selecting here is the same exact-access
     * binding as at a read - the declaring object is the one this store
     * touches, never a searched-for same-named receiver - taken one bytecode
     * earlier, so the store's own {@code putfield} publishes the writer's
     * expression as a {@code WRITE} version over a pre-write initial.</p>
     */
    public static void selectFieldWriteCarrier(Object owner,
                                               String fieldSignature) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return;
        selectAccessOwnerSharedCarriers(active, owner, fieldSignature, false,
                "", -1, -1);
    }

    /**
     * Records a stable logical source a live occurrence just entered.
     *
     * <p>Called by {@link RuntimeTraceContext} whenever a thread establishes
     * its logical source, which an application does inside its own entry
     * method rather than before it.  This is one of the two ways an
     * occurrence is attributed; the other is the source registered for its
     * own receiver, which is what a long-lived service that never opens a
     * request scope on these threads relies on.  Only GraphChecker's own
     * strings are compared, so this needs no observation mute of its own.</p>
     */
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
     * Mints one exact source root selected by the current execution task.
     *
     * <p>The application calls this at the definition boundary, before the
     * value is inserted into any selected state.  An undeclared source is a
     * no-op.  A declared source is materialized once, on the exact field, and
     * its VM expression is recorded as the cross-case identity authority.</p>
     */
    public static boolean symbolizeConfiguredSourceField(
            String sourceId, Object owner, String fieldSignature) {
        ActiveRegion active = activeRegion();
        if (active == null || owner == null) return false;
        RuntimeTask.SourceField source = active.activation.sourceFields.get(
                safe(sourceId));
        if (source == null) return false;
        if (!source.fieldSignature.equals(safe(fieldSignature))) {
            active.addUnresolvedOnce(source.sourceId
                    + ": configured source field differs from runtime hook");
            return false;
        }
        int claim = active.claimSymbolicSource(source.sourceId, owner);
        if (claim < 0) return false;
        // The caller performs a concrete-equivalent Map re-key only for the
        // first successful materialization.  Re-entering the hook for the
        // same owner must not append another mutation sequence.
        if (claim == 0) return false;
        beginBookkeeping();
        try {
            Field field = declaredInstanceField(owner,
                    source.fieldSignature);
            if (field == null || !field.getType().isPrimitive()) {
                throw new IllegalStateException(
                        "configured source is not an exact primitive field");
            }
            ModelAssignment assignment = active.configuredSourceAssignment(
                    source.sourceId, source.fieldSignature);
            if (assignment != null) {
                if (!writeModeledField(owner, source.fieldSignature,
                        assignment)) {
                    throw new IllegalStateException(
                            "configured source model could not be written");
                }
                active.recordModelAssignment(assignment);
            }
            String symbol = configuredSourceSymbol(
                    active.activation.occurrenceId, source.sourceId);
            EngineApi api = engine();
            api.symbolizeExactField(owner,
                    exactFieldSignature(field), symbol);
            ensurePathRecordingStarted(active);
            Object value = field.get(owner);
            JsonElement expression = engineExpression(api.fieldExpression(
                    owner, field.getDeclaringClass().getName(),
                    field.getName(), javaTypeDescriptor(
                            field.getType().getTypeName()),
                    value));
            JsonObject evidence = SymbolicSourceEvidence.event(
                    source.sourceId, active.activation.occurrenceId,
                    source.fieldSignature, expression);
            active.recordSymbolicSource(source.sourceId, evidence);
            active.symbolized.add("SOURCE:" + source.sourceId);
            return true;
        } catch (Throwable failure) {
            active.releaseSymbolicSourceClaim(source.sourceId, owner);
            active.addUnresolvedOnce(source.sourceId
                    + ": exact symbolic source materialization failed: "
                    + rootCause(failure));
            return false;
        } finally {
            endBookkeeping();
        }
    }

    /** Stable VM name shared by every materialization of one exact source. */
    private static String configuredSourceSymbol(
            String sourceOccurrenceId, String sourceId) {
        return SymbolicSourceEvidence.engineLabel(
                sourceOccurrenceId, sourceId);
    }

    /** Names a source-side invariant failure without changing the workload. */
    public static void rejectConfiguredSourceField(
            String sourceId, String detail) {
        ActiveRegion active = activeRegion();
        if (active == null
                || !active.activation.sourceFields.containsKey(
                safe(sourceId))) {
            return;
        }
        active.addUnresolvedOnce(safe(sourceId)
                + ": CONFIGURED_SYMBOLIC_SOURCE_REJECTED: " + safe(detail));
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
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

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
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

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
    }

    /** Records that a declared communication response site was reached. */
    public static void recordCommunicationEffect(String captureBindingId) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
                captureBindingId);
        if (request == null || !request.capturesCommunicationEffect()
                || !active.captureEligible(request)) return;
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

        JsonObject row = outputCaptureRow(request, occurrence);
        row.addProperty("interactionKind", "COMMUNICATION_EFFECT");
        row.addProperty("authority", "INSTRUMENTED_INTERACTION_SITE_V1");
        active.outputCaptures.add(row);
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
     * Gives a selected arithmetic Atomic RMW a primitive pre-state shadow.
     * The custom VM then replaces that exact {@code value} shadow with the
     * post-state expression when the concrete Atomic method returns.
     */
    public static void prepareAtomicMutationStateOutput(
            String captureBindingId, Object receiver) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        OutputCaptureSpec request = active.activation.outputCapture(
                captureBindingId);
        if (request == null || !request.capturesMutationState()
                || !active.captureEligible(request)) return;
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
            if (configuration().selectedMapProducer(active.activation,
                    request.outputPort())) {
                if (!(pending.container instanceof Map)) {
                    throw new IllegalStateException(
                            "selected Map producer output is not a Map: "
                                    + request.outputPort());
                }
                long versionId = api.currentSharedMapVersion(
                        pending.container);
                String failure = active.stageMapVersion(
                        request.outputPort(), versionId);
                if (!failure.isEmpty()) {
                    active.addUnresolvedOnce(failure);
                    throw new IllegalStateException(failure);
                }
            }
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": mutation-state output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            finishAtCompletedStateInteraction(active, request);
        }
    }

    /**
     * Closes a state-producing replay at its last selected interaction.
     *
     * <p>The region template may be a long-lived service function, but a
     * selected mutation/field-write output is an event boundary.  Keeping the
     * VM attached until the service thread returns records unrelated loop
     * turns and can perturb the distributed system itself.  Call arguments
     * and communication effects deliberately do not use this terminal: their
     * expression still has to cross the VM handoff broker before the sender
     * may detach.</p>
     */
    private static void finishAtCompletedStateInteraction(
            ActiveRegion active, OutputCaptureSpec request) {
        if (active == null || request == null
                || !(request.capturesMutationState()
                || request.capturesFieldWriteState())
                || !active.demandedOutputRelationComplete()) {
            return;
        }
        try {
            finish(active.token, "NORMAL", "", null);
        } catch (Throwable failure) {
            active.addUnresolvedOnce(
                    "state interaction terminal failed: "
                            + rootCause(failure));
        }
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
        if (!active.boundedOutputVersionSlot(request, occurrence)) return;

        JsonObject row = outputCaptureRow(request, occurrence);
        try {
            EngineApi api = engine();
            JsonElement expression = active.activation
                    .recordedPrimitiveOutput(request);
            DeclaredField field = null;
            if (expression != null) {
                // A closed primitive relation with no symbolic inputs is the
                // exact recorded constant. Replaying a long-lived service
                // root is not a stable way to rediscover which repetition
                // produced it.
            } else if (containerValue(fieldValue)) {
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
            stageSelectedFieldVersion(active, request, fieldOwner, api);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(),
                    request.captureBindingId()
                    + ": field-write output capture failed: "
                    + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            finishAtCompletedStateInteraction(active, request);
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
                throw new IllegalStateException("custom VM returned no "
                        + "normal-exit field expression");
            }
            row.add("expression", expression);
            stageSelectedFieldVersion(active, request, fieldOwner, api);
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

    /** Stages the native version backing one selected field output port. */
    private static void stageSelectedFieldVersion(
            ActiveRegion active, OutputCaptureSpec request,
            Object fieldOwner, EngineApi api) throws Exception {
        if (active == null || request == null
                || !configuration().selectedFieldProducer(
                active.activation, request.outputPort())) {
            return;
        }
        DeclaredField field = FieldPathSpec.declaredField(
                request.fieldSignature());
        if (field == null) {
            throw new IllegalStateException(
                    "selected field producer output has no exact field: "
                            + request.outputPort());
        }
        if (!api.sharedFieldProducerAdmissionAvailable()) {
            throw new IllegalStateException(
                    "custom VM field producer-state API is unavailable");
        }
        long versionId = api.currentSharedFieldVersion(fieldOwner,
                field.owner(), field.name(),
                javaTypeDescriptor(field.type()));
        String failure = active.stageFieldVersion(
                request.outputPort(), versionId);
        if (!failure.isEmpty()) {
            active.addUnresolvedOnce(failure);
            throw new IllegalStateException(failure);
        }
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
                || request.capturesCommunicationEffect()
                || request.capturesHandoffBoundLeaf()
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
        if (request.capturesCommunicationEffect()) {
            if (!"COMMUNICATION_EFFECT".equals(
                    string(capture, "interactionKind"))
                    || !"INSTRUMENTED_INTERACTION_SITE_V1".equals(
                    string(capture, "authority"))) {
                return false;
            }
        } else if (!observedOutputRelation(capture)) {
            return false;
        }
        return !request.occurrenceScoped()
                || request.outputSiteId().equals(
                string(capture, "outputSiteId"))
                && integer(capture, "outputOccurrence", -1) >= 1;
    }

    /** True when the row carries an engine-produced symbolic relation. */
    private static boolean observedOutputRelation(JsonObject capture) {
        JsonElement expression = capture.get("expression");
        return expression != null && !expression.isJsonNull();
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

    /** Test seam for the relation-seed branch-recording fast path. */
    static boolean relationSeedSkipsBranchForTests(
            JsonObject encodedTask, String method, int unitIndex) {
        RuntimeTask task = new RuntimeTask(ExecutionTask.decode(encodedTask));
        return skipsRelationSeedBranch(task, siteId(method, unitIndex));
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

    /** Test seam for incomplete-relation capture-binding diagnostics. */
    static JsonArray missingOutputCaptureBindingIdsForTests(
            JsonObject encodedTask, JsonArray encodedCaptures) {
        RuntimeTask task = new RuntimeTask(ExecutionTask.decode(encodedTask));
        ActiveRegion active = new ActiveRegion(1L, task, null,
                Thread.currentThread());
        if (encodedCaptures != null) {
            for (JsonElement element : encodedCaptures) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "output capture row must be an object");
                }
                active.outputCaptures.add(element.getAsJsonObject());
            }
        }
        return missingOutputCaptureBindingIds(active);
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

    /**
     * Result of one VM symbolic-expression export or attach.
     *
     * <p>A successful attach is represented by the VM ledger's
     * {@code VALUE_HANDOFF} edge. This object carries only the live broker
     * answer needed by the bridge; failures carry one named gap.</p>
     */
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

        private long exportEventId() {
            return ok() ? longInteger(record, "exportEventId", 0L) : 0L;
        }

        @Override
        public String toString() {
            return "HandoffResult[" + stage + " status=" + status
                    + (ok() ? "" : " " + reason())
                    + " handle=" + handle + "]";
        }
    }

    /**
     * Exports one exact field through the live VM broker.
     *
     * <p>This is the complete reflective ABI used by application adapters.
     * Protocol provenance stays in their Java trace; it is neither needed nor
     * accepted here because the returned live handle is the propagation
     * identity.</p>
     */
    public static HandoffResult exportSymbolicLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        CommunicationHandoffSpec declared = manualCommunicationHandoffSite(
                declaringClass, fieldName, descriptor, true);
        return exportSymbolicLeaf(owner, declaringClass, fieldName,
                descriptor, declared == null ? "" : declared.portId());
    }

    /**
     * Attaches one live broker handle to one exact destination field.
     *
     * <p>The VM validates handle ownership and destination storage. No
     * exchange, attempt, direction or leaf annotation is admitted as another
     * pairing key; successful propagation is the VM's {@code VALUE_HANDOFF}
     * edge.</p>
     */
    public static HandoffResult receiveSymbolicLeaf(
            Object owner, String declaringClass, String fieldName,
            String descriptor, long handle) {
        CommunicationHandoffSpec declared = manualCommunicationHandoffSite(
                declaringClass, fieldName, descriptor, false);
        if (declared != null) {
            return attachDeclaredCommunicationExpression(owner,
                    declaringClass, fieldName, descriptor,
                    new HeaderHandle(true, handle, "", ""), declared);
        }
        beginBookkeeping();
        try {
            return record(attach(owner, declaringClass, fieldName, descriptor,
                    handle));
        } finally {
            endBookkeeping();
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
        if (!api.expressionHandoffAvailable()) {
            return record(unavailable(RpcExpressionHandoff.STAGE_EXPORT, 0L,
                    "this JDK exposes no symbolic expression handoff API"));
        }
        long handle;
        try {
            handle = api.exportExpression(owner, declaringClass, fieldName,
                    descriptor);
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
            if (status == RpcExpressionHandoff.NOT_SYMBOLIC) {
                // This guarded execution has a concrete leaf, not a broken
                // symbolic handoff.  Preserve its exact VM expression as the
                // producer case's constant output, but publish no handoff
                // attestation or VALUE_HANDOFF claim.  A later replay in
                // which the leaf becomes symbolic will take the success path
                // below and publish the real VM edge instead.
                recordHandoffBoundLeafOutput(owner, declaringClass,
                        fieldName, descriptor, result, declaredPortId);
                return result;
            }
            return record(result);
        }
        HandoffResult result = new HandoffResult(
                RpcExpressionHandoff.STAGE_EXPORT,
                RpcExpressionHandoff.OK, handle, new JsonObject());
        record(result);
        recordHandoffBoundLeafOutput(owner, declaringClass, fieldName,
                descriptor, result, declaredPortId);
        return result;
    }

    /**
     * Captures an output relation only when this export is the exact
     * handoff-bound component requested by the task.
     *
     * <p>The capture asks the VM for the expression of the exact live field at
     * the same export which minted the handoff handle.  That expression may
     * have been created locally or attached by an earlier interaction; a Java
     * input projection is neither required nor allowed to replace it.</p>
     *
     * <p>The exchange is named by the selected occurrence, not by the recorded
     * exchange id.  {@code exchangeId} is minted by the transport of the
     * session that produced it - a Hadoop IPC {@code clientId:callId}, a
     * per-JVM SASL counter - so the plan's id belongs to the discovery
     * session and never equals the one this replay mints for the same cut.
     * Comparing them refused every handoff-bound leaf capture ever planned.
     * README {@code RPC-1}: a stale discovery id produces a gap, never an
     * equality, so it is not a match key here either.  What identifies the
     * capture is the declared port the instrumented hook already carries.
     * Explicit adapters whose local call has no port id use the semantic leaf
     * name and materialize every bounded candidate as a guarded alternative;
     * attempt, direction and exchange are provenance, not another matcher.</p>
     */
    private static void recordHandoffBoundLeafOutput(
            Object owner, String declaringClass, String fieldName,
            String descriptor, HandoffResult result, String declaredPortId) {
        ActiveRegion active = activeRegion();
        if (active == null) {
            if (result != null) diag("HANDOFF_CAPTURE_IGNORED",
                    "no-active-region");
            return;
        }
        if (result == null
                || !RpcExpressionHandoff.STAGE_EXPORT.equals(result.stage)
                || !result.ok()
                && result.status != RpcExpressionHandoff.NOT_SYMBOLIC) {
            return;
        }
        List<OutputCaptureSpec> requests = handoffBoundLeafCaptures(
                active, declaredPortId);
        if (requests.isEmpty()) {
            diag("HANDOFF_CAPTURE_IGNORED", "task="
                    + safe(active.activation.taskId)
                    + " reason=not-declared");
            return;
        }
        for (OutputCaptureSpec request : requests) {
            recordHandoffBoundLeafOutput(active, owner, declaringClass,
                    fieldName, descriptor, result, request);
        }
    }

    private static void recordHandoffBoundLeafOutput(
            ActiveRegion active, Object owner, String declaringClass,
            String fieldName, String descriptor, HandoffResult result,
            OutputCaptureSpec request) {
        if (!active.captureEligible(request)) {
            diag("HANDOFF_CAPTURE_IGNORED", "task="
                    + safe(active.activation.taskId) + " binding="
                    + request.captureBindingId()
                    + " reason=prerequisites-incomplete");
            return;
        }
        int occurrence = active.nextOutputCaptureOccurrence(request);
        if (!active.boundedOutputVersionSlot(request, occurrence)) {
            diag("HANDOFF_CAPTURE_IGNORED", "task="
                    + safe(active.activation.taskId) + " binding="
                    + request.captureBindingId() + " occurrence="
                    + occurrence + " reason=outside-bounded-slot");
            return;
        }

        JsonObject row = outputCaptureRow(request, occurrence);
        try {
            Field field = declaredInstanceField(owner, declaringClass,
                    fieldName, descriptor);
            if (field == null) {
                throw new IllegalStateException(
                        "exported field differs from planned component");
            }
            Object value = field.get(owner);
            EngineApi api = engine();
            JsonElement expression;
            if (containerValue(value)) {
                // A concrete array/container has no scalar field shadow for
                // getFieldExpression to return.  Capture the same complete,
                // fixed-cardinality state used by every other container
                // output boundary.  Symbolic elements remain symbolic in the
                // VM snapshot; concrete elements become constants.
                if (!snapshotOutputContainer(value, api)) {
                    throw new IllegalStateException(
                            "exported container has no VM snapshot model");
                }
                expression = engineExpression(api.expression(value));
            } else {
                expression = engineExpression(api.fieldExpression(
                        owner, declaringClass, fieldName, descriptor, value));
            }
            if (expression == null || expression.isJsonNull()) {
                throw new IllegalStateException(
                        "custom VM returned no handoff field expression");
            }
            row.add("expression", expression);
        } catch (Throwable throwable) {
            active.addGuardedOutputCaptureFailure(
                    request.captureBindingId(), request.captureBindingId()
                            + ": handoff-bound output capture failed: "
                            + rootCause(throwable));
        } finally {
            active.outputCaptures.add(row);
            diag("HANDOFF_CAPTURE", "task="
                    + safe(active.activation.taskId) + " binding="
                    + request.captureBindingId() + " occurrence=" + occurrence
                    + " expression=" + row.has("expression"));
        }
    }

    /**
     * The bounded plan row this occurrence declares for the exported port.
     * The instrumented call carries that exact static identity; recovering a
     * candidate from a semantic leaf path would recreate the deleted RPC join.
     */
    private static List<OutputCaptureSpec> handoffBoundLeafCaptures(
            ActiveRegion active, String declaredPortId) {
        List<OutputCaptureSpec> requests = new ArrayList<>();
        if (safe(declaredPortId).isEmpty()) return requests;
        for (OutputCaptureSpec candidate
                : active.activation.outputCaptures) {
            if (!candidate.capturesHandoffBoundLeaf()
                    || !candidate.outputPort().equals(declaredPortId)) {
                continue;
            }
            requests.add(candidate);
        }
        return requests;
    }

    /**
     * Attaches one receive whose destination this occurrence's plan declares
     * as a communication port.
     *
     * <p>Every successful receive files its evidence here, declared or not.
     * A leaf an adapter discovered structurally - a protobuf field of a
     * serialized payload, say - exports and attaches through the same broker
     * and produces the same {@code VALUE_HANDOFF} edge as a catalog-declared
     * port does; recording only the declared ones would leave the undeclared
     * edge in the VM ledger and nowhere in this run's evidence, which is
     * worse than refusing it, because a refusal is at least a named blocker.
     * The declared port is passed in rather than looked up: recovering it
     * from the leaf path here would be the second join protocol
     * {@code RPC-1} forbids.</p>
     */
    private static HandoffResult attachDeclaredCommunicationExpression(
            Object owner, String declaringClass, String fieldName,
            String descriptor, HeaderHandle carried,
            CommunicationHandoffSpec declared) {
        beginBookkeeping();
        try {
            HandoffResult result = record(attach(owner, declaringClass,
                    fieldName, descriptor, carried.handle));
            if (result.ok()) {
                recordVmHandoffEvent(declared, result, owner, declaringClass,
                        fieldName, descriptor, carried.producerTaskId,
                        carried.producerOccurrenceId);
            }
            return result;
        } finally {
            endBookkeeping();
        }
    }

    /**
     * The one instance field a declared communication port crosses on.
     *
     * <p>The broker addresses a leaf by an exact instance field of a concrete
     * owner, and a cut argument, a cut return and a server-entry parameter
     * are all locals.  Both sides of one cut therefore present the value on
     * this carrier, which is what makes the exported and the attached leaf
     * the same declared sort.  The carrier changes no program value: on a JDK
     * without the handoff natives the receiver reads back exactly the
     * concrete value it was handed.</p>
     */
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
    // Hadoop RPC-header bridge
    // ------------------------------------------------------------------

    /**
     * Exact producer admissions armed by selected callers, indexed only by
     * the live request exchange that can consume them.
     */
    private static final Map<String, ResponseProducerArm>
            IN_FLIGHT_RESPONSE_PRODUCER_ARMS = new LinkedHashMap<>();
    private static final Object RESPONSE_ARM_LOCK = new Object();
    /** Exact response ports named immediately before this thread's next cut. */
    private static final ThreadLocal<Set<String>>
            PENDING_RESPONSE_ATTACH_PORTS = new ThreadLocal<Set<String>>() {
                @Override
                protected Set<String> initialValue() {
                    return new LinkedHashSet<>();
                }
            };
    /** The exact response producer task authorized by this request delivery. */
    private static final ThreadLocal<ResponseProducerArm>
            INBOUND_RESPONSE_PRODUCER_ARM = new ThreadLocal<>();

    /**
     * One caller-selected response producer admission.  This is scheduling
     * authority only: it names the already-planned producer task and carries
     * no value, payload identity or expression.  The VM handle transported in
     * Hadoop's real RPC header remains the only value authority.
     */
    private static final class ResponseProducerArm {
        private final String producerTaskId;
        private final Set<String> portIds;
        private final String failure;

        private ResponseProducerArm(String producerTaskId,
                                    Set<String> portIds, String failure) {
            this.producerTaskId = safe(producerTaskId);
            this.portIds = Collections.unmodifiableSet(
                    new LinkedHashSet<>(portIds));
            this.failure = safe(failure);
        }

        private boolean valid() {
            return !producerTaskId.isEmpty() && failure.isEmpty()
                    && !portIds.isEmpty();
        }

        private boolean authorizes(RuntimeTask task) {
            return valid() && task != null
                    && producerTaskId.equals(task.taskId)
                    && !task.responseExportPortIds.isEmpty()
                    && portIds.containsAll(task.responseExportPortIds);
        }
    }

    /** One leaf read directly from the current Hadoop Call's wire header. */
    private static final class HeaderHandle {
        private static final HeaderHandle MISSING =
                new HeaderHandle(false, 0L, "", "");
        private final boolean present;
        private final long handle;
        private final String producerTaskId;
        private final String producerOccurrenceId;

        private HeaderHandle(boolean present, long handle,
                             String producerTaskId,
                             String producerOccurrenceId) {
            this.present = present;
            this.handle = handle;
            this.producerTaskId = safe(producerTaskId);
            this.producerOccurrenceId = safe(producerOccurrenceId);
        }
    }

    /**
     * Optional reflection boundary to Hadoop's RPC-header implementation.
     *
     * <p>GraphChecker has no compile-time Hadoop dependency.  Export hands the
     * opaque broker token immediately to Hadoop, whose next request/response
     * header serializes it.  Attach asks Hadoop's current {@code Client.Call}
     * or {@code Server.Call}; there is deliberately no GraphChecker-side
     * outbound, in-flight, or inbound leaf table.</p>
     */
    private static final class RpcHeaderBridge {
        private static final String CLASS =
                "org.apache.hadoop.ipc.CausynthRpcWire";
        private static volatile Binding binding;

        private static boolean stage(String leafPath, long handle,
                                     String producerTaskId,
                                     String producerOccurrenceId) {
            Binding current = bind();
            if (!current.usable()) return false;
            try {
                Object result = current.stage.invoke(null, leafPath,
                        Long.valueOf(handle), producerTaskId,
                        producerOccurrenceId);
                return result instanceof Boolean
                        && ((Boolean) result).booleanValue();
            } catch (Throwable ignored) {
                return false;
            }
        }

        private static HeaderHandle take(String leafPath) {
            Binding current = bind();
            if (!current.usable()) return HeaderHandle.MISSING;
            try {
                Object result = current.take.invoke(null, leafPath);
                if (result == null || !((Boolean) current.present.invoke(
                        result)).booleanValue()) {
                    return HeaderHandle.MISSING;
                }
                return new HeaderHandle(true, ((Long) current.handle.invoke(
                        result)).longValue(),
                        (String) current.producerTaskId.invoke(result),
                        (String) current.producerOccurrenceId.invoke(result));
            } catch (Throwable ignored) {
                return HeaderHandle.MISSING;
            }
        }

        private static Binding bind() {
            Binding current = binding;
            if (current != null) return current;
            synchronized (RpcHeaderBridge.class) {
                current = binding;
                if (current != null) return current;
                try {
                    Class<?> bridge = Class.forName(CLASS);
                    Method stage = bridge.getMethod("stageExpression",
                            String.class, long.class, String.class,
                            String.class);
                    Method take = bridge.getMethod("takeCurrentExpression",
                            String.class);
                    Class<?> result = take.getReturnType();
                    current = new Binding(stage, take,
                            result.getMethod("present"),
                            result.getMethod("handle"),
                            result.getMethod("producerTaskId"),
                            result.getMethod("producerOccurrenceId"));
                } catch (ReflectiveOperationException | RuntimeException
                         | LinkageError unavailable) {
                    current = new Binding();
                }
                binding = current;
                return current;
            }
        }

        private static final class Binding {
            private final Method stage;
            private final Method take;
            private final Method present;
            private final Method handle;
            private final Method producerTaskId;
            private final Method producerOccurrenceId;

            private Binding() {
                this(null, null, null, null, null, null);
            }

            private Binding(Method stage, Method take, Method present,
                            Method handle, Method producerTaskId,
                            Method producerOccurrenceId) {
                this.stage = stage;
                this.take = take;
                this.present = present;
                this.handle = handle;
                this.producerTaskId = producerTaskId;
                this.producerOccurrenceId = producerOccurrenceId;
            }

            private boolean usable() {
                return stage != null && take != null;
            }
        }
    }

    /** Stages one VM handle with the exact active producer execution. */
    private static boolean stageRpcHeaderExpression(String leafPath,
                                                    long handle) {
        ActiveRegion active = activeRegion();
        return active != null && RpcHeaderBridge.stage(leafPath, handle,
                active.activation.taskId, active.activation.occurrenceId);
    }

    /**
     * One exact planner-selected producer-state transfer for a shared Map.
     *
     * <p>The task/port/edge triple is scheduling authority only.  The native
     * version id published later is the value authority; no Java object,
     * concrete Map contents, or "latest writer" guess crosses occurrences.
     * A nonempty failure is deliberately retained so an upstream-bound Map
     * can fail closed without falling back to a fresh local INITIAL.</p>
     */
    private static final class PlannedMapAdmission {
        private final String inputPort;
        private final String selectedEdgeId;
        private final String producerTaskId;
        private final String producerOutputPort;
        private final String failure;

        private PlannedMapAdmission(String inputPort, String selectedEdgeId,
                                    String producerTaskId,
                                    String producerOutputPort,
                                    String failure) {
            this.inputPort = safe(inputPort);
            this.selectedEdgeId = safe(selectedEdgeId);
            this.producerTaskId = safe(producerTaskId);
            this.producerOutputPort = safe(producerOutputPort);
            this.failure = safe(failure);
        }

        private boolean required() {
            return !inputPort.isEmpty();
        }

        private boolean valid() {
            return required() && failure.isEmpty()
                    && !selectedEdgeId.isEmpty()
                    && !producerTaskId.isEmpty()
                    && !producerOutputPort.isEmpty();
        }

        private String registryKey() {
            return producerTaskId + "\n" + producerOutputPort;
        }
    }

    /** Exact scheduled producer version for one concrete scalar/reference field. */
    private static final class PlannedFieldAdmission {
        private final String inputPort;
        private final String selectedEdgeId;
        private final String producerTaskId;
        private final String producerOutputPort;
        /** Exact configured primitive leaves carried by this reference. */
        private final List<PlannedSourceAlias> sourceAliases;
        private final String failure;

        private PlannedFieldAdmission(String inputPort,
                                      String selectedEdgeId,
                                      String producerTaskId,
                                      String producerOutputPort,
                                      List<PlannedSourceAlias> sourceAliases,
                                      String failure) {
            this.inputPort = safe(inputPort);
            this.selectedEdgeId = safe(selectedEdgeId);
            this.producerTaskId = safe(producerTaskId);
            this.producerOutputPort = safe(producerOutputPort);
            this.sourceAliases = sourceAliases == null
                    ? Collections.emptyList()
                    : Collections.unmodifiableList(new ArrayList<>(
                    sourceAliases));
            this.failure = safe(failure);
        }

        private boolean valid() {
            return !inputPort.isEmpty() && failure.isEmpty()
                    && !selectedEdgeId.isEmpty()
                    && !producerTaskId.isEmpty()
                    && !producerOutputPort.isEmpty();
        }

        private String registryKey() {
            return producerTaskId + "\n" + producerOutputPort;
        }
    }

    /** Source identity and exact nested field carried by one output value. */
    private static final class PlannedSourceAlias {
        private final String sourceTaskId;
        private final String sourceId;
        private final String sourceOccurrenceId;
        private final String fieldSignature;

        private PlannedSourceAlias(String sourceTaskId, String sourceId,
                                   String sourceOccurrenceId,
                                   String fieldSignature) {
            this.sourceTaskId = safe(sourceTaskId);
            this.sourceId = safe(sourceId);
            this.sourceOccurrenceId = safe(sourceOccurrenceId);
            this.fieldSignature = safe(fieldSignature);
        }

        private String symbol() {
            return configuredSourceSymbol(sourceOccurrenceId, sourceId);
        }

        private String identity() {
            return sourceOccurrenceId + "\n" + sourceId;
        }
    }

    /** Exact primitive leaf reached from one configured response root. */
    private static final class ResponseFieldPathLeaf {
        private final Object owner;
        private final DeclaredField field;
        private final String descriptor;

        private ResponseFieldPathLeaf(Object owner, DeclaredField field) {
            this.owner = owner;
            this.field = field;
            this.descriptor = javaTypeDescriptor(field.type());
        }
    }

    /**
     * Names one response port whose cut is about to issue its request.
     *
     * <p>This is scheduling metadata only.  It carries no handle or value and
     * is consumed by the immediately following request-send boundary.  A
     * call can name several component ports of the same response; the
     * configuration gate below requires all of them to resolve to the same
     * already-planned producer task.</p>
     */
    public static void prepareResponseHandoff(String portId) {
        ActiveRegion caller = activeRegion();
        if (caller == null || safe(portId).isEmpty()) return;
        CommunicationHandoffSpec site =
                caller.activation.communicationHandoff(portId, false);
        if (site == null || !"RESPONSE".equalsIgnoreCase(site.direction())) {
            return;
        }
        PENDING_RESPONSE_ATTACH_PORTS.get().add(site.portId());
    }

    /** Moves only the caller-selected response-producer scheduling arm. */
    static void observeExchangeLeg(String direction, String transport,
                                   String correlationId, String half) {
        String normalizedDirection = safe(direction);
        String normalizedHalf = safe(half);
        String key = exchangeKey(transport, correlationId, normalizedHalf);
        if ("SEND".equalsIgnoreCase(normalizedDirection)) {
            if ("REQUEST".equalsIgnoreCase(normalizedHalf)) {
                Set<String> ports = new LinkedHashSet<>(
                        PENDING_RESPONSE_ATTACH_PORTS.get());
                PENDING_RESPONSE_ATTACH_PORTS.remove();
                armResponseProducer(key, ports);
            } else if ("RESPONSE".equalsIgnoreCase(normalizedHalf)) {
                INBOUND_RESPONSE_PRODUCER_ARM.remove();
            }
            return;
        }
        if (!"RECEIVE".equalsIgnoreCase(normalizedDirection)) return;
        if ("REQUEST".equalsIgnoreCase(normalizedHalf)) {
            ResponseProducerArm arm;
            synchronized (RESPONSE_ARM_LOCK) {
                arm = IN_FLIGHT_RESPONSE_PRODUCER_ARMS.remove(key);
            }
            if (arm == null) {
                INBOUND_RESPONSE_PRODUCER_ARM.remove();
            } else {
                INBOUND_RESPONSE_PRODUCER_ARM.set(arm);
            }
        }
    }

    private static String exchangeKey(String transport, String correlationId,
                                      String half) {
        return safe(transport) + "\n" + safe(correlationId) + "\n"
                + safe(half);
    }

    /** Arms only the unique producer already selected by this caller's task. */
    private static void armResponseProducer(String exchangeKey,
                                            Set<String> responsePorts) {
        ActiveRegion caller = activeRegion();
        if (caller == null
                || responsePorts == null || responsePorts.isEmpty()) {
            return;
        }
        ResponseProducerArm arm = configuration().responseProducerArm(
                caller.activation, responsePorts);
        if (!arm.valid()) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MISSING_METADATA, 0L,
                    "required response producer admission is not unique: "
                            + arm.failure));
            return;
        }
        boolean collision;
        synchronized (RESPONSE_ARM_LOCK) {
            collision = IN_FLIGHT_RESPONSE_PRODUCER_ARMS.containsKey(
                    exchangeKey);
            if (collision) {
                IN_FLIGHT_RESPONSE_PRODUCER_ARMS.remove(exchangeKey);
            } else {
                IN_FLIGHT_RESPONSE_PRODUCER_ARMS.put(exchangeKey, arm);
            }
        }
        if (collision) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, 0L,
                    "two selected callers armed the same live response "
                            + "exchange"));
        }
    }

    // ------------------------------------------------------------------
    // Declared communication ports
    // ------------------------------------------------------------------

    /**
     * Exports one configured primitive component of the returned response.
     * The response and intermediate references are used only to locate the
     * exact live field; no reference identity or expression crosses the cut.
     */
    public static void exportCommunicationFieldPath(String portId,
                                                    Object responseRoot) {
        CommunicationHandoffSpec site;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, true);
        } finally {
            endBookkeeping();
        }
        if (site == null || !site.responsePathCarrier()) return;
        ResponseFieldPathLeaf leaf = responseFieldPathLeaf(responseRoot,
                site.handoffPath());
        if (leaf == null) {
            recordFieldPathHandoffFailure(RpcExpressionHandoff.STAGE_EXPORT,
                    "configured response field path did not resolve: "
                            + site.portId());
            return;
        }
        // The native broker deliberately performs a pure lookup for a
        // container state: it must never turn an arbitrary response object
        // into a symbolic root.  Establish the same bounded, fixed-shape
        // snapshot used by output capture before asking the broker to mint
        // the live handle.  Doing this after export produced a
        // ContainerRelation in the result but no VALUE_HANDOFF at the cut.
        try {
            Object value = readExactField(leaf.owner,
                    leaf.field.signature());
            if (value == MissingValue.INSTANCE) {
                throw new IllegalStateException(
                        "configured response leaf is unavailable");
            }
            if (containerValue(value)
                    && !snapshotOutputContainer(value, engine())) {
                throw new IllegalStateException(
                        "configured response container has no bounded "
                                + "snapshot model");
            }
        } catch (Throwable failure) {
            recordFieldPathHandoffFailure(RpcExpressionHandoff.STAGE_EXPORT,
                    "configured response field path could not prepare its "
                            + "container state: " + rootCause(failure));
            return;
        }
        HandoffResult result = exportSymbolicLeaf(leaf.owner,
                leaf.field.owner(), leaf.field.name(), leaf.descriptor,
                site.portId());
        // The custom VM exports exact concrete primitives as typed ConstExpr
        // handles.  An old VM returning NOT_SYMBOLIC cannot establish a
        // VALUE_HANDOFF and is deliberately not represented by a zero token.
        if (!result.ok()) return;
        if (!stageRpcHeaderExpression(site.leafPath(), result.handle())) {
            recordFieldPathHandoffFailure(RpcExpressionHandoff.STAGE_EXPORT,
                    "response field path could not enter the RPC header: "
                            + site.leafPath());
        }
    }

    /** Attaches one carried handle to the reconstructed response's leaf. */
    public static void attachCommunicationFieldPath(String portId,
                                                    Object responseRoot) {
        CommunicationHandoffSpec site;
        HeaderHandle carried;
        long handle;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, false);
            carried = site == null ? HeaderHandle.MISSING
                    : RpcHeaderBridge.take(site.leafPath());
            handle = carried.handle;
        } finally {
            endBookkeeping();
        }
        if (site == null || !site.responsePathCarrier()) return;
        if (handle <= 0L) {
            ActiveRegion active = activeRegion();
            if (active != null
                    && active.responseHandoffSatisfied(site.portId())) {
                // This bounded case already attached the selected response
                // component.  A long-lived caller may execute the same
                // static RPC hook again before its outer service loop reaches
                // K_L; those later concrete exchanges are outside this
                // task's selected interaction and are not missing inputs.
                return;
            }
            deferRequiredResponseHandoffHandleGap(site);
            return;
        }
        ResponseFieldPathLeaf leaf = responseFieldPathLeaf(responseRoot,
                site.handoffPath());
        if (leaf == null) {
            recordFieldPathHandoffFailure(RpcExpressionHandoff.STAGE_ATTACH,
                    "configured response field path did not resolve: "
                            + site.portId());
            return;
        }
        attachDeclaredCommunicationExpression(leaf.owner,
                leaf.field.owner(), leaf.field.name(), leaf.descriptor,
                carried, site);
    }

    private static ResponseFieldPathLeaf responseFieldPathLeaf(
            Object root,
            List<CommunicationHandoffSpec.PathStep> path) {
        if (root == null || path == null || path.isEmpty()) {
            return null;
        }
        Object owner = root;
        for (int index = 0; index < path.size(); index++) {
            CommunicationHandoffSpec.PathStep step = path.get(index);
            if (step.field()) {
                if (index + 1 == path.size()) {
                    DeclaredField leaf = FieldPathSpec.declaredField(
                            step.declaration());
                    if (leaf == null || declaredInstanceField(owner,
                            leaf.signature()) == null) return null;
                    return new ResponseFieldPathLeaf(owner, leaf);
                }
                owner = readExactField(owner, step.declaration());
            } else if (step.uniqueArrayElement()) {
                owner = uniqueArrayElement(owner, step.elementType());
            } else {
                return null;
            }
            if (owner == null || owner == MissingValue.INSTANCE) return null;
        }
        return null;
    }

    /** Returns the sole exact-class element of one fixed runtime array. */
    private static Object uniqueArrayElement(Object value,
                                             String binaryClassName) {
        if (value == null || !value.getClass().isArray()
                || safe(binaryClassName).isEmpty()) return null;
        Object selected = null;
        int length = Array.getLength(value);
        for (int index = 0; index < length; index++) {
            Object element = Array.get(value, index);
            if (element == null || !binaryClassName.equals(
                    element.getClass().getName())) continue;
            if (selected != null) return null;
            selected = element;
        }
        return selected;
    }

    private static void recordFieldPathHandoffFailure(String stage,
                                                      String detail) {
        beginBookkeeping();
        try {
            record(failed(stage, RpcExpressionHandoff.MISSING_METADATA,
                    0L, detail));
        } finally {
            endBookkeeping();
        }
    }

    /** A selected attach site executed, but its message carried no VM handle. */
    private static void recordRequiredHandoffHandleGap(
            CommunicationHandoffSpec site, boolean concreteMarker) {
        int status = concreteMarker ? RpcExpressionHandoff.NOT_SYMBOLIC
                : RpcExpressionHandoff.UNKNOWN_HANDLE;
        recordHandoffGap(RpcExpressionHandoff.gap(
                RpcExpressionHandoff.STAGE_ATTACH, status, 0L,
                "required communication port carried no live VM handle: "
                        + site.portId()));
    }

    /**
     * Defers a missing selected response leaf until this bounded caller ends.
     *
     * <p>A long-lived caller may try several live response exchanges before
     * the selected producer occurrence reaches its demanded output.  Those
     * earlier exchanges are search candidates, not independent missing
     * inputs.  Keep at most one provisional fact per port; a later successful
     * VM attach retracts it, while terminal read-out publishes it if no
     * candidate ever supplied a handle.</p>
     */
    private static void deferRequiredResponseHandoffHandleGap(
            CommunicationHandoffSpec site) {
        JsonObject gap = RpcExpressionHandoff.gap(
                RpcExpressionHandoff.STAGE_ATTACH,
                RpcExpressionHandoff.UNKNOWN_HANDLE, 0L,
                "required communication port carried no live VM handle: "
                        + site.portId());
        ActiveRegion active = activeRegion();
        if (active == null) {
            recordHandoffGap(gap);
            return;
        }
        active.deferResponseHandoffGap(site.portId(), gap);
        diag(RpcExpressionHandoff.GAP_KIND, String.valueOf(gap));
    }

    /**
     * Exports the live expression of one declared communication port.
     *
     * <p>Called where the port's own declaration says the value leaves this
     * occurrence: at the cut argument, or at the server entry's return.  The
     * value arrives on a {@link HandoffLeafCarrier} the <em>instrumented
     * frame</em> allocated and stored into, because a broker leaf is an exact
     * instance field while a cut argument is a local - and because only the
     * application's own frame propagates a value's expression into a field.
     * The handle this mints travels with the message; every receiver that
     * attaches it records its own {@code VALUE_HANDOFF} edge.</p>
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
                field, descriptor, site.portId());
        // A concrete leaf is still a leaf the message carried.  Preserve a
        // zero marker so the receiver can distinguish it from a declared leaf
        // that never reached the transport.  Zero is never passed to the VM
        // attach API and therefore creates no symbolic propagation claim.
        if (!result.ok()
                && result.status != RpcExpressionHandoff.NOT_SYMBOLIC) {
            return;
        }
        if (!stageRpcHeaderExpression(site.leafPath(),
                result.ok() ? result.handle() : 0L)) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_EXPORT,
                    RpcExpressionHandoff.MISSING_METADATA,
                    result.ok() ? result.handle() : 0L,
                    "communication leaf could not enter the RPC header: "
                            + site.portId()));
        }
    }

    /**
     * Attaches the exported expression of one declared communication port.
     *
     * <p>After a successful attach the carrier leaf <em>denotes the sender's
     * expression</em>; the instrumented frame reads it straight back into its
     * own local, so the receiver's later arithmetic, branches and exports
     * build on that term directly.  The reference is recorded against the
     * declared port the attach landed on together with the VM export event
     * the ledger relates it to; nothing is paired here.  A delivery that
     * carried no live handle, or an attach the broker refused, leaves the
     * carrier holding the concrete value it arrived with, and is named as a
     * gap.</p>
     */
    public static void attachCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        CommunicationHandoffSpec site;
        HeaderHandle carried;
        long handle;
        boolean leafCarried;
        beginBookkeeping();
        try {
            site = communicationHandoffSite(portId, false);
            carried = site == null ? HeaderHandle.MISSING
                    : RpcHeaderBridge.take(site.leafPath());
            leafCarried = carried.present;
            handle = carried.handle;
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
        if (handle <= 0L) {
            recordRequiredHandoffHandleGap(site, leafCarried);
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

    /** The manual adapter port declared for one exact carrier storage. */
    private static CommunicationHandoffSpec manualCommunicationHandoffSite(
            String declaringClass, String fieldName, String descriptor,
            boolean exporting) {
        ActiveRegion active = activeRegion();
        if (active == null) return null;
        return active.activation.manualCommunicationHandoff(declaringClass,
                fieldName, descriptor, exporting);
    }

    /**
     * Files one case-local reference into the VM's own handoff ledger and the
     * exact expression now held by the attached destination.
     *
     * <p>{@code site} is the declared port this attach landed on, or
     * {@code null} when no port of this occurrence's plan names the
     * destination.  An undeclared destination is still recorded - the edge is
     * the VM's and it exists either way - under the exact field the attach
     * bound, beside a named gap saying the catalog declares no port for it.
     * The Composer then takes its {@code COMMUNICATION_LEAF} authority from
     * the edge and refuses to bind an SMT term to an undeclared port, which
     * is a blocker with a subject rather than an absence.  The value is read
     * after attach from the exact destination storage: a container from its
     * actual referent, every other leaf from its exact field shadow.</p>
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
        long exportEvent = result.exportEventId();
        if (exportEvent <= 0L) {
            recordHandoffGap(RpcExpressionHandoff.gap(
                    RpcExpressionHandoff.STAGE_ATTACH,
                    RpcExpressionHandoff.MALFORMED_RESULT, result.handle(),
                    "attached leaf named no VM export event"));
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
                    "custom VM returned no attached destination expression"));
            return;
        }
        acceptVmHandoffExpression(active, site, exportEvent, expression,
                producerTaskId, producerOccurrenceId);
    }

    /** Commits one fully validated receiver-side handoff to the active case. */
    private static void acceptVmHandoffExpression(
            ActiveRegion active, CommunicationHandoffSpec site,
            long exportEvent, JsonElement expression,
            String producerTaskId, String producerOccurrenceId) {
        active.vmHandoffEvents.add(VmHandoffEvidence.event(site.portId(),
                exportEvent, expression, producerTaskId,
                producerOccurrenceId));
        // A VM-attached expression is an exact selected symbolic input just
        // as much as one created by a local symbolize hook.  Some receiver
        // regions intentionally declare every RPC input CONCRETE because the
        // VALUE_HANDOFF is their sole value authority; without opening this
        // gate, their later branch hooks execute but are never recorded.
        // Keep the gate after destination read-out so a missing, rejected or
        // malformed handle cannot widen symbolic observation.
        ensurePathRecordingStarted(active);
        if (site.responsePathCarrier()) {
            active.markResponseHandoffSatisfied(site.portId());
        }
        // The receiving local now denotes the sender's expression, so any
        // fresh root the entry materialization minted for this same port is
        // dead code that only a second authority could still read.  README
        // SMT-1 allows one authority per selected input, and after a
        // successful attach that authority is this edge.  A port the attach
        // did not bind keeps its root, which is why this is retraction on
        // success rather than removal of the materialization.
        active.symbolized.remove(site.portId());
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
        if (!api.expressionHandoffAvailable()) {
            return unavailable(RpcExpressionHandoff.STAGE_ATTACH, handle,
                    "this JDK exposes no symbolic expression handoff API");
        }
        long exportEventId;
        try {
            exportEventId = api.attachExpression(owner, declaringClass,
                    fieldName, descriptor, handle);
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
        JsonObject success = new JsonObject();
        success.addProperty("exportEventId", exportEventId);
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

    /**
     * Maps a non-positive {@code exportExpression} answer onto a status.  Zero
     * is neither a handle nor a declared failure, so it is a malformed answer
     * rather than a quietly ignored export.
     */
    private static int exportStatus(long handle) {
        if (handle == 0L || handle < Integer.MIN_VALUE) {
            return RpcExpressionHandoff.MALFORMED_RESULT;
        }
        return (int) handle;
    }

    private static HandoffResult unavailable(String stage, long handle,
                                             String detail) {
        return failed(stage, RpcExpressionHandoff.API_UNAVAILABLE, handle,
                detail);
    }

    private static HandoffResult failed(String stage, int status, long handle,
                                        String detail) {
        return new HandoffResult(stage, status, handle,
                RpcExpressionHandoff.gap(stage, status, handle, detail));
    }

    /**
     * Files failed calls with the active region and reports every outcome to
     * the diagnostic trace. Successful propagation is serialized only by the
     * VM ledger and its case-local handoff reference.
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
     * run can state.  It is registered on demand rather than at load, so a
     * run with nothing to state adds no hook.
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
     *
     * <p>The shutdown hook publishes them, and so does the settled campaign
     * immediately before it halts - a halt runs no hook.</p>
     */
    static void publishRunTotals() {
        configuration().publishUnansweredAddresses();
    }

    /**
     * Outcome of one recorded shared-state evidence call.
     *
     * <p>Like a handoff result, it is either an admitted record or exactly one
     * named gap, never both and never neither.  A selection carries no record
     * of its own: selecting a carrier states that a question may be asked
     * later, not that any value has an answer yet.</p>
     */
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

        /**
         * The INITIAL version published by a fresh selection.  Zero means the
         * location was already selected, which is a success: its INITIAL
         * version was published by the first selection and still stands.
         */
        public long initialFieldVersionId() {
            return initialFieldVersionId;
        }

        /** The raw VM envelope; empty when none was returned. */
        public JsonObject envelope() {
            return copyJsonTree(envelope);
        }

        /** Admitted evidence row; empty after a failure or a selection. */
        public JsonObject record() {
            return ok() ? copyJsonTree(record) : new JsonObject();
        }

        /** Named coverage gap for a failure; empty after a success. */
        public JsonObject gap() {
            return ok() ? new JsonObject() : copyJsonTree(record);
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
     *
     * <p>Selection is what makes the version store affordable, so it is
     * explicit and bounded: nothing is versioned until a caller names it.  The
     * location is remembered by the active region, which reads its versions
     * back at region exit.</p>
     */
    public static SharedStateResult selectSharedFieldCarrier(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        beginBookkeeping();
        try {
            return selectFieldCarrier(owner, declaringClass, fieldName,
                    descriptor);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult selectFieldCarrier(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        String missing = missingCarrierMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (!missing.isEmpty()) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "", missing),
                    null, activeRegion());
        }
        EngineApi api = engine();
        if (!api.sharedStateEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_SELECT, ""), null,
                    activeRegion());
        }
        long initial;
        try {
            initial = api.selectSharedFieldCarrier(owner, declaringClass,
                    fieldName, descriptor);
        } catch (Throwable throwable) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, activeRegion());
        }
        if (initial < 0L) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    selectStatus(initial), "",
                    "selectSharedFieldCarrier returned " + initial), null,
                    activeRegion());
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", initial, new JsonObject(),
                        new JsonObject()),
                SharedCarrier.field(owner, declaringClass, fieldName,
                        descriptor), activeRegion());
    }

    /**
     * Selects one element of a fixed-shape array as a symbolic carrier.  A
     * resizable collection has no stable slot and is not selectable; it keeps
     * the container algebra instead.
     */
    public static SharedStateResult selectSharedElementCarrier(Object array,
                                                               int index) {
        beginBookkeeping();
        try {
            return selectElementCarrier(array, index);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult selectElementCarrier(Object array,
                                                          int index) {
        if (array == null || index < 0) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "an element carrier needs an array and a "
                            + "non-negative index"), null, activeRegion());
        }
        EngineApi api = engine();
        if (!api.sharedStateEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_SELECT, ""), null,
                    activeRegion());
        }
        long initial;
        try {
            initial = api.selectSharedElementCarrier(array, index);
        } catch (Throwable throwable) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, activeRegion());
        }
        if (initial < 0L) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    selectStatus(initial), "",
                    "selectSharedElementCarrier returned " + initial), null,
                    activeRegion());
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", initial, new JsonObject(),
                        new JsonObject()),
                SharedCarrier.element(array, index), activeRegion());
    }

    /**
     * Selects one map as a symbolic carrier of its own whole state.
     *
     * <p>A map has no fixed slot, so it is not selectable as a field or as an
     * element; what is selected is the map's <em>state</em>, and every later
     * selected mutation publishes one immutable whole-map version of it while
     * every later query binds to the state it may have observed. That is the
     * same contract a scalar carrier has, over a different expression
     * shape.</p>
     *
     * <p>{@code declaringClass}, {@code fieldName} and {@code descriptor} are
     * the field the map is <em>held in</em>, not the location being selected.
     * The VM addresses the location by the map's own session identity, which
     * no second run can name; the declared field is the join a later run can,
     * so it is recorded here when the caller knows it and left empty when it
     * does not. Empty costs cross-run pairing and nothing else - the slice
     * addresses locations by the VM's identity either way.</p>
     */
    public static SharedStateResult selectSharedMapCarrier(
            Object map, String declaringClass, String fieldName,
            String descriptor) {
        beginBookkeeping();
        try {
            return selectMapCarrier(map, declaringClass, fieldName,
                    descriptor);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult selectMapCarrier(
            Object map, String declaringClass, String fieldName,
            String descriptor) {
        if (map == null) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "a map carrier needs the map it selects"), null,
                    activeRegion());
        }
        EngineApi api = engine();
        if (!api.sharedMapEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_SELECT, ""), null,
                    activeRegion());
        }
        long initial;
        try {
            initial = api.selectSharedMapCarrier(map);
        } catch (Throwable throwable) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, activeRegion());
        }
        if (initial < 0L) {
            return recordShared(failedShared(SharedStateEvidence.STAGE_SELECT,
                    selectStatus(initial), "",
                    "selectSharedMapCarrier returned " + initial), null,
                    activeRegion());
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", initial, new JsonObject(),
                        new JsonObject()),
                SharedCarrier.map(map, declaringClass, fieldName, descriptor),
                activeRegion());
    }

    /**
     * Admits one destination Map to the exact producer version selected by
     * the frozen workflow edge.
     *
     * <p>This path never falls back to {@link #selectMapCarrier}: failure
     * before native admission must leave the destination unselected, because
     * a fresh local INITIAL would be a different value lineage that merely
     * happens to occupy the same declared field.</p>
     */
    private static SharedStateResult admitPlannedSharedMapState(
            ActiveRegion active, SharedCarrierRequest request, Object map,
            PlannedMapAdmission admission) {
        if (active == null || request == null || admission == null
                || !admission.required()) {
            return failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "planned Map admission is missing its exact task edge");
        }
        if (map == null || map == MissingValue.INSTANCE) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "planned Map input " + admission.inputPort
                            + " has no concrete destination Map"), null,
                    active);
        }
        if (!admission.valid()) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.NOT_SELECTED, "",
                    "planned Map input " + admission.inputPort + ": "
                            + admission.failure), null, active);
        }
        Long version = configuration().publishedMapVersion(admission);
        if (version == null || version.longValue() <= 0L) {
            String detail = "planned Map producer "
                    + admission.producerTaskId + " has not published "
                    + admission.producerOutputPort;
            active.deferPlannedProducerPrerequisite(
                    admission.inputPort, detail);
            // This is a candidate-order miss, not evidence that the frozen
            // edge is invalid.  A later compatible root may run after the
            // exact producer commits.  Keep the
            // destination unselected and the candidate open; if no access
            // ever succeeds, the terminal candidate gate names one bounded
            // unanswered occurrence instead of importing a local INITIAL.
            diag("PLANNED_SHARED_STATE_PREREQUISITE_PENDING", detail);
            return failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.NOT_SELECTED, "", detail);
        }
        active.resolvePlannedProducerPrerequisite(admission.inputPort);
        EngineApi api = engine();
        if (!api.sharedMapProducerAdmissionAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_SELECT, ""), null, active);
        }
        final long readEventId;
        try {
            readEventId = api.admitSharedMapVersion(map,
                    version.longValue(), admission.selectedEdgeId);
        } catch (Throwable throwable) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, active);
        }
        if (readEventId <= 0L) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    readEventId < 0L ? selectStatus(readEventId)
                            : SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "admitSharedMapVersion returned " + readEventId
                            + " for " + admission.selectedEdgeId), null,
                    active);
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", 0L, new JsonObject(),
                        new JsonObject()),
                SharedCarrier.map(map, request.declaringClass,
                        request.fieldName, request.descriptor), active);
    }

    /** {@link #selectSharedMapCarrier} with no declared holding field. */
    public static SharedStateResult selectSharedMapCarrier(Object map) {
        return selectSharedMapCarrier(map, "", "", "");
    }

    /**
     * Reads back the whole-map states published for one selected map,
     * together with how every query of it was resolved.
     *
     * <p>The envelope is the version store's own, unchanged: the same kind,
     * the same schema version and the same members a field read-out returns,
     * with {@code MAP_STATE} as the location kind and the reserved
     * whole-state slot. It is therefore decoded by exactly the code path a
     * field envelope is, which is the point - fields, elements and maps
     * differ in the shape of one expression, not in how their evidence is
     * admitted.</p>
     */
    public static SharedStateResult captureSharedMapVersions(Object map) {
        return captureSharedMapVersions(map, "", "", "", activeRegion());
    }

    private static SharedStateResult captureSharedMapVersions(
            Object map, String declaringClass, String fieldName,
            String descriptor, ActiveRegion active) {
        beginBookkeeping();
        try {
            return captureMapVersions(map, declaringClass, fieldName,
                    descriptor, active);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult captureMapVersions(
            Object map, String declaringClass, String fieldName,
            String descriptor, ActiveRegion active) {
        if (map == null) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "a map carrier needs the map it selects"), null, active);
        }
        EngineApi api = engine();
        if (!api.sharedMapEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_VERSIONS, ""), null, active);
        }
        SharedCarrier carrier = SharedCarrier.map(map, declaringClass,
                fieldName, descriptor);
        String serialized = memoizedReadOut(carrier.key());
        if (serialized == null) {
            try {
                serialized = memoizeReadOut(carrier.key(),
                        api.sharedMapVersions(map));
            } catch (Throwable throwable) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        rootCause(throwable)), null, active);
            }
        }
        return recordShared(decodeVersionsEnvelope(serialized, carrier,
                evidenceIdentity(active)), null, active);
    }

    /**
     * Reads back the versions published for one selected field, together with
     * how every read of it was resolved.
     */
    public static SharedStateResult captureSharedFieldVersions(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        return captureSharedFieldVersions(owner, declaringClass, fieldName,
                descriptor, activeRegion());
    }

    private static SharedStateResult captureSharedFieldVersions(
            Object owner, String declaringClass, String fieldName,
            String descriptor, ActiveRegion active) {
        beginBookkeeping();
        try {
            return captureFieldVersions(owner, declaringClass, fieldName,
                    descriptor, active);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult captureFieldVersions(
            Object owner, String declaringClass, String fieldName,
            String descriptor, ActiveRegion active) {
        String missing = missingCarrierMetadata(owner, declaringClass,
                fieldName, descriptor);
        if (!missing.isEmpty()) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MISSING_METADATA, "", missing), null,
                    active);
        }
        EngineApi api = engine();
        if (!api.sharedStateEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_VERSIONS, ""), null, active);
        }
        SharedCarrier carrier = SharedCarrier.field(owner, declaringClass,
                fieldName, descriptor);
        String serialized = memoizedReadOut(carrier.key());
        if (serialized == null) {
            try {
                serialized = memoizeReadOut(carrier.key(),
                        api.sharedFieldVersions(owner, declaringClass,
                                fieldName, descriptor));
            } catch (Throwable throwable) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        rootCause(throwable)), null, active);
            }
        }
        return recordShared(decodeVersionsEnvelope(serialized, carrier,
                evidenceIdentity(active)), null, active);
    }

    /** {@link #captureSharedFieldVersions} for one selected array element. */
    public static SharedStateResult captureSharedElementVersions(
            Object array, int index) {
        return captureSharedElementVersions(array, index, activeRegion());
    }

    private static SharedStateResult captureSharedElementVersions(
            Object array, int index, ActiveRegion active) {
        beginBookkeeping();
        try {
            return captureElementVersions(array, index, active);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult captureElementVersions(
            Object array, int index, ActiveRegion active) {
        if (array == null || index < 0) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_VERSIONS,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "an element carrier needs an array and a "
                            + "non-negative index"), null, active);
        }
        EngineApi api = engine();
        if (!api.sharedStateEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_VERSIONS, ""), null, active);
        }
        SharedCarrier carrier = SharedCarrier.element(array, index);
        String serialized = memoizedReadOut(carrier.key());
        if (serialized == null) {
            try {
                serialized = memoizeReadOut(carrier.key(),
                        api.sharedElementVersions(array, index));
            } catch (Throwable throwable) {
                return recordShared(failedShared(
                        SharedStateEvidence.STAGE_VERSIONS,
                        SharedStateEvidence.INVOCATION_FAILED, "",
                        rootCause(throwable)), null, active);
            }
        }
        return recordShared(decodeVersionsEnvelope(serialized, carrier,
                evidenceIdentity(active)), null, active);
    }

    /**
     * Reads back the session's one event-order ledger.
     *
     * <p>The ledger spans the whole session, not this region, and it is the
     * single order domain every channel contributes to.  It is captured
     * before the region's symbolic context is torn down, because a closed
     * session has none.</p>
     */
    public static SharedStateResult captureSessionEventLedger() {
        return captureSessionEventLedger(activeRegion());
    }

    private static SharedStateResult captureSessionEventLedger(
            ActiveRegion active) {
        beginBookkeeping();
        try {
            return captureEventLedger(active);
        } finally {
            endBookkeeping();
        }
    }

    private static SharedStateResult captureEventLedger(ActiveRegion active) {
        EngineApi api = engine();
        if (!api.sharedStateEvidenceAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_LEDGER, ""), null, active);
        }
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
    }

    /**
     * Raw VM read-outs already taken while closing the selected occurrence on
     * this thread, keyed by the location they answer for.
     *
     * <p>Several evidence builders may ask for the same selected carrier.
     * These are not cheap payloads -
     * a version's {@code pathGuard} is the whole-thread conjunction at the
     * moment it was published, so a versions envelope is already
     * O(versions x path condition) - and each copy is serialized in the VM and
     * then decoded from UTF-8 by the interpreter on the way back.</p>
     *
     * <p>This memoizes the <em>bytes</em>, never the record.  The scope is one
     * {@link #closeOccurrence} pass on one
     * thread, opened and closed explicitly: the VM's version list grows while
     * a region runs, and an answer that outlived the close would be a stale
     * one served for a live location.  It is a memo of one query, not a match
     * by call order or payload equality - the key is the location.</p>
     */
    private static final ThreadLocal<Map<String, String>> READ_OUT_MEMO =
            new ThreadLocal<Map<String, String>>();

    /** Cache key for the session ledger, which names no single location. */
    private static final String LEDGER_READ_OUT_KEY = "SESSION_EVENT_LEDGER";

    // Package-private rather than private: the scope discipline below - open,
    // memoize, close, and never answer outside a scope - is what keeps a stale
    // read-out from being served for a live location, and the test in this
    // package drives it directly.

    /** Opens the memo for one activation close. */
    static void beginReadOutMemo() {
        READ_OUT_MEMO.set(new HashMap<String, String>());
    }

    /** Closes it.  Nothing survives the close that took the read-outs. */
    static void endReadOutMemo() {
        READ_OUT_MEMO.remove();
    }

    /** The bytes already read for {@code key} in this close, or null. */
    static String memoizedReadOut(String key) {
        Map<String, String> memo = READ_OUT_MEMO.get();
        return memo == null ? null : memo.get(key);
    }

    /** Files {@code serialized} under {@code key} and returns it unchanged. */
    static String memoizeReadOut(String key, String serialized) {
        Map<String, String> memo = READ_OUT_MEMO.get();
        if (memo != null && serialized != null) memo.put(key, serialized);
        return serialized;
    }

    /**
     * Reads one VM version envelope.  An envelope for a location that was
     * never selected is its own named finding: "nobody wrote it" and "nobody
     * was watching" are opposite answers and only one of them is evidence.
     */
    static SharedStateResult decodeVersionsEnvelope(
            String serialized, SharedCarrier carrier,
            RecordedEvidenceIdentity identity) {
        return decodeVersionsEnvelope(serialized, carrier, identity,
                activeRegion());
    }

    /** Decodes one read-out for the exact activation that captured it. */
    private static SharedStateResult decodeVersionsEnvelope(
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
        // The VM writes an unguarded write's guard as JSON null, which no
        // tree copy preserves. Make it explicit only after admission: a
        // serializer-truncated tree is refused without rewriting evidence
        // that cannot be used.
        SharedStateEvidence.normalizeGuards(envelope);
        String locationKey = SharedStateEvidence.locationKey(envelope);
        JsonObject record = SharedStateEvidence.versionsRecord(locationKey,
                envelope, identity);
        if (carrier != null) {
            // The VM addresses a location by its own session identity; the
            // slice and the composer address one by its declared Java field.
            // Only this call site holds both, so the join is recorded here
            // rather than reconstructed by matching values later.
            record.add("carrier", carrier.toJson());
        }
        // Publication can run after the owner thread has left ACTIVE.  Its
        // explicit activation is the only authority for repeated instances;
        // never fall back to the publication thread's empty ThreadLocal.
        addActivationIdentity(object(record, "envelope"), active);
        return new SharedStateResult(SharedStateEvidence.STAGE_VERSIONS,
                SharedStateEvidence.OK, locationKey, 0L, envelope, record);
    }

    /**
     * Gives every write and read in one envelope the activation address the
     * rest of the pipeline joins on.
     *
     * <p>The VM stamps a write with the {@code taskId} of the context that
     * published it and a read with its {@code regionId}. Neither is a
     * cross-run address: a task id means nothing without the plan that minted
     * it, and a static region is shared by every concurrent activation of it.
     * This process holds that plan, so it resolves both here - a write
     * exactly, through its own task, and a read through the activation that
     * is running when the read is read out.</p>
     *
     * <p>The reader address used to be "the campaign's one activation of that
     * region", an implicit root-call fallback which silently dropped reader
     * attribution whenever several occurrences shared a template. The replacement is
     * the identity the running region already carries - the same fields
     * {@link #evidenceIdentity} stamps - and a read that no active region owns
     * is marked by name rather than left unaddressed, because "nobody was
     * running" and "the row was never considered" are different findings.</p>
     */
    private static void addActivationIdentity(JsonObject envelope) {
        addActivationIdentity(envelope, activeRegion());
    }

    private static void addActivationIdentity(JsonObject envelope,
                                              ActiveRegion active) {
        Configuration config = configuration();
        for (JsonElement element : array(envelope, "versions")) {
            if (!element.isJsonObject()) continue;
            JsonObject version = element.getAsJsonObject();
            RuntimeTask writer = config.taskById(
                    string(version, "taskId"));
            if (writer == null) continue;
            version.addProperty(SharedStateEvidence.WRITER_SOURCE_KEY,
                    writer.sourceKey);
            version.addProperty(SharedStateEvidence.WRITER_OCCURRENCE_ID,
                    writer.occurrenceId);
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
            // The VM addresses a read by its static region.  Only an active
            // region can say which activation of that region performed it,
            // and a read whose region is not the running one is a read this
            // activation did not perform: it is marked, never attributed.
            if (!reader.regionId.equals(string(read, "regionId"))) {
                read.addProperty(READER_AUTHORITY_FIELD,
                        READER_FOREIGN_REGION);
                continue;
            }
            read.addProperty(SharedStateEvidence.READER_SOURCE_KEY,
                    reader.sourceKey);
            read.addProperty(SharedStateEvidence.READER_OCCURRENCE_ID,
                    reader.occurrenceId);
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

    /**
     * The identity every record of one read-out batch is stamped with.
     *
     * <p>An activation outside any campaign task has none of these
     * identities, so it produces an unstamped record, which the admission
     * layer then refuses by name. That is deliberate: evidence whose observer
     * cannot be named is exactly what the stamp exists to keep out.</p>
     */
    private static RecordedEvidenceIdentity evidenceIdentity(
            ActiveRegion active) {
        if (active == null) return null;
        return RecordedEvidenceIdentity.of(
                RecordedEvidenceIdentity.declaredRunId(),
                sessionIdentity(active), active.activation.taskId,
                active.activation.occurrenceId,
                active.activation.sourceKey, active.evidenceSnapshot());
    }

    /**
     * The symbolic session lifetime one activation's evidence belongs to.
     *
     * <p>A region that runs without a workload session still belongs to a
     * session - the VM opens a region-scoped lifetime for it - but this
     * process never learned that lifetime's id, so the activation's own token
     * names it. The two forms are kept distinguishable on purpose: records of
     * one workload session share the first, and records of two region
     * lifetimes never share the second.</p>
     */
    private static String sessionIdentity(ActiveRegion active) {
        long session = workloadSessionId;
        return session != 0L ? "workload#" + session
                : "region#" + active.token;
    }

    /**
     * Offers one compiled read-cut gate to the running activation.
     *
     * <p>The gate is admitted, recorded and left to observe. It is
     * deliberately <em>not</em> a wait: distributed replay only observes the
     * selected read and reports that the model's proposed order was not
     * enforced.</p>
     *
     * <p>What is enforced here are the invariants. A row that is not a gate
     * this authority compiled, that claims to write a program field, to
     * replace an RPC return value, or whose placement contradicts the selected
     * access is refused with its own named reason and becomes a gate gap in
     * the region result. Nothing is dropped silently.</p>
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
        JsonObject installation = copyJsonTree(gate);
        installation.addProperty("installedAs",
                SelectedReadCut.OBSERVE_AND_CONFIRM);
        installation.addProperty("parked", false);
        installation.addProperty("wroteProgramField", false);
        installation.addProperty("replacedRpcReturnValue", false);
        return recordReadCut(new ReadCutGateResult(installation, true),
                active);
    }

    /**
     * Installs one concrete field read from the exact scheduled producer
     * version.  Unlike ordinary carrier selection this path never creates a
     * destination INITIAL: failure leaves the field unselected and records a
     * named provenance gap.
     */
    private static SharedStateResult admitPlannedSharedFieldState(
            ActiveRegion active, SharedCarrierRequest request, Object owner,
            PlannedFieldAdmission admission) {
        if (active == null || request == null || admission == null) {
            return failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "planned field admission is missing its exact task edge");
        }
        if (owner == null || owner == MissingValue.INSTANCE) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.MISSING_METADATA, "",
                    "planned field input " + admission.inputPort
                            + " has no concrete destination owner"), null,
                    active);
        }
        if (!admission.valid()) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.NOT_SELECTED, "",
                    "planned field input " + admission.inputPort + ": "
                            + admission.failure), null, active);
        }
        Long version = configuration().publishedFieldVersion(admission);
        if (version == null || version.longValue() <= 0L) {
            String detail = "planned field producer "
                    + admission.producerTaskId + " has not published "
                    + admission.producerOutputPort;
            active.deferPlannedProducerPrerequisite(
                    admission.inputPort, detail);
            // As for Map state above, absence from the campaign registry is
            // provisional while other selected occurrences are live.  It is
            // neither permission to use the concrete destination nor a
            // durable shared-state gap for this candidate.
            diag("PLANNED_SHARED_STATE_PREREQUISITE_PENDING", detail);
            return failedShared(SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.NOT_SELECTED, "", detail);
        }
        active.resolvePlannedProducerPrerequisite(admission.inputPort);
        EngineApi api = engine();
        if (!api.sharedFieldProducerAdmissionAvailable()) {
            return recordShared(unavailableShared(
                    SharedStateEvidence.STAGE_SELECT, ""), null, active);
        }
        final long readEventId;
        try {
            readEventId = api.admitSharedFieldVersion(owner,
                    request.declaringClass, request.fieldName,
                    request.descriptor, version.longValue(),
                    admission.selectedEdgeId);
        } catch (Throwable throwable) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    rootCause(throwable)), null, active);
        }
        if (readEventId <= 0L) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    readEventId < 0L ? selectStatus(readEventId)
                            : SharedStateEvidence.MALFORMED_ENVELOPE, "",
                    "admitSharedFieldVersion returned " + readEventId
                            + " for " + admission.selectedEdgeId), null,
                    active);
        }
        String sourceFailure = installPlannedNestedSourceAliases(active,
                request, owner, admission, api);
        if (!sourceFailure.isEmpty()) {
            return recordShared(failedShared(
                    SharedStateEvidence.STAGE_SELECT,
                    SharedStateEvidence.INVOCATION_FAILED, "",
                    sourceFailure), null, active);
        }
        return recordShared(new SharedStateResult(
                        SharedStateEvidence.STAGE_SELECT,
                        SharedStateEvidence.OK, "", 0L, new JsonObject(),
                        new JsonObject()),
                SharedCarrier.field(owner, request.declaringClass,
                        request.fieldName, request.descriptor), active);
    }

    /**
     * Restores exact configured primitive source leaves on a transferred
     * reference value.
     *
     * <p>The reference admission above is the authority that this concrete
     * destination denotes the selected producer value.  Only after that
     * succeeds may a source declaration attached to that producer output be
     * materialized on the referenced object.  The VM name is the producer's
     * original occurrence/source identity, so this creates no second input
     * and performs no concrete-value or object-identity join.</p>
     */
    private static String installPlannedNestedSourceAliases(
            ActiveRegion active, SharedCarrierRequest request, Object owner,
            PlannedFieldAdmission admission, EngineApi api) {
        if (admission.sourceAliases.isEmpty()) return "";
        Field carried = declaredInstanceField(owner, request.declaringClass,
                request.fieldName, request.descriptor);
        if (carried == null) {
            return "planned source alias has no exact carried field for "
                    + admission.inputPort;
        }

        final Object referent;
        try {
            referent = carried.get(owner);
        } catch (Throwable failure) {
            return "planned source alias cannot read carried field: "
                    + rootCause(failure);
        }
        if (referent == null || referent == MissingValue.INSTANCE
                || carried.getType().isPrimitive()) {
            return "planned source alias requires a non-null reference for "
                    + admission.inputPort;
        }

        List<Field> sourceFields = new ArrayList<>();
        for (PlannedSourceAlias alias : admission.sourceAliases) {
            Field sourceField = declaredInstanceField(referent,
                    alias.fieldSignature);
            if (sourceField == null || !sourceField.getType().isPrimitive()) {
                return "planned source alias " + alias.sourceId
                        + " is not an exact primitive field on the carried "
                        + "reference";
            }
            sourceFields.add(sourceField);
        }

        for (int index = 0; index < admission.sourceAliases.size(); index++) {
            PlannedSourceAlias alias = admission.sourceAliases.get(index);
            Field sourceField = sourceFields.get(index);
            try {
                String published = configuration().publishedSourceSymbol(
                        admission, alias);
                if (published.isEmpty()) {
                    return "planned source alias " + alias.sourceId
                            + " has no accepted producer VM symbol";
                }
                String prefix = alias.symbol();
                api.symbolizeExactField(referent,
                        exactFieldSignature(sourceField), prefix);
                ensurePathRecordingStarted(active);
                Object value = sourceField.get(referent);
                JsonElement expression = engineExpression(
                        api.fieldExpression(referent,
                                sourceField.getDeclaringClass().getName(),
                                sourceField.getName(), javaTypeDescriptor(
                                        sourceField.getType().getTypeName()),
                                value));
                JsonObject verified = SymbolicSourceEvidence.event(
                        alias.sourceId, alias.sourceOccurrenceId,
                        alias.fieldSignature, expression);
                if (!published.equals(string(verified, "rawSymbol"))) {
                    return "planned source alias " + alias.sourceId
                            + " produced a different VM symbol";
                }
            } catch (Throwable failure) {
                return "planned source alias " + alias.sourceId
                        + " failed: " + rootCause(failure);
            }
        }
        return "";
    }

    /** A read-cut gate was offered where no activation could carry it. */
    public static final String READ_CUT_NO_ACTIVE_REGION =
            "GATE_NO_ACTIVE_REGION";
    /** The selected order is observed and confirmed, never scheduled. */
    public static final String READ_CUT_ORDER_NOT_ENFORCED =
            "GATE_ORDER_NOT_ENFORCED";

    /**
     * Files one gate outcome with the active region.
     *
     * <p>An installed gate carries its own coverage fact: the run observes and
     * confirms the selected read, and does not enforce its order. Recording
     * that beside the installation is what keeps a confirmed read from being
     * read as an enforced one.</p>
     */
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
            return installed ? copyJsonTree(record) : new JsonObject();
        }

        /** Named coverage gap for a refusal; empty after an admission. */
        public JsonObject gap() {
            return installed ? new JsonObject() : copyJsonTree(record);
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
            return failedShared(SharedStateEvidence.STAGE_LEDGER,
                    SharedStateEvidence.MALFORMED_ENVELOPE, "", fault);
        }
        return new SharedStateResult(SharedStateEvidence.STAGE_LEDGER,
                SharedStateEvidence.OK, "", 0L, envelope,
                SharedStateEvidence.ledgerRecord(envelope, identity));
    }

    /**
     * One shared location a task asked this activation to select.
     *
     * <p>The declaration is deliberately thin: a field named by its declaring
     * class, name and descriptor, or an array element named by its index,
     * both reached by the same {@code fieldPath} from the region receiver
     * that a symbolize action already uses - an empty path meaning the
     * receiver itself. Nothing here searches for a plausible owner: a
     * declaration that does not resolve becomes a named gap, because
     * selecting the wrong location would record provenance for a field the
     * target never reads.</p>
     */
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
         *
         * <p>A field carrier selects on the object that <em>declares</em> the
         * field, which is the owner of the path's last segment; an element
         * carrier selects on the array, and a map carrier on the map, both of
         * which are that segment's value.</p>
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

        SharedStateResult selectAtAccess(ActiveRegion active, Object owner,
                                         String fieldSignature) {
            if (mapState) {
                Object map = readExactField(owner, fieldSignature);
                PlannedMapAdmission admission = active == null ? null
                        : active.activation.mapAdmission(fieldSignature);
                if (admission != null) {
                    return admitPlannedSharedMapState(active, this, map,
                            admission);
                }
                return selectSharedMapCarrier(map, declaringClass,
                        fieldName, descriptor);
            }
            PlannedFieldAdmission admission = active == null ? null
                    : active.activation.fieldAdmission(fieldSignature);
            if (admission != null) {
                return admitPlannedSharedFieldState(active, this, owner,
                        admission);
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

    /**
     * Selects every carrier this activation's task declared.
     *
     * <p>This runs at region entry, before the region's own work, for the
     * same reason a read-cut gate is offered there: a location becomes
     * versioned only from the moment it is selected, so a selection made after
     * the first write would record a store that is missing exactly the write
     * the reader took. A task that declares none selects none - the absent
     * list is not an invitation to pick a carrier for it.</p>
     */
    private static void selectDeclaredSharedCarriers(ActiveRegion active) {
        for (SharedCarrierRequest request
                : active.activation.sharedCarriers) {
            // This binding is resolved by the exact instrumented field
            // access, where the actual declaring object is available.  The
            // activation receiver may be an outer service-loop object and is
            // never substituted for it.
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
            ActiveRegion active, Object owner, String fieldSignature,
            boolean allowPlannedAdmission, String method, int unitIndex,
            int occurrence) {
        for (SharedCarrierRequest request
                : active.activation.sharedCarriers) {
            if (!request.matchesAccess(fieldSignature)) continue;
            if (!allowPlannedAdmission
                    && (request.mapState
                    && active.activation.mapAdmission(fieldSignature) != null
                    || !request.mapState && !request.element
                    && active.activation.fieldAdmission(fieldSignature)
                    != null)) {
                // An upstream-bound location is admitted only at its
                // selected read. Selecting it at an earlier putfield would
                // mint/consume a local INITIAL before exact producer-state
                // admission can install the scheduled version.
                continue;
            }
            String key = request.declaringClass + "#" + request.fieldName
                    + "@" + System.identityHashCode(owner);
            if (!active.accessOwnerCarrierSelections.add(key)) continue;
            PlannedMapAdmission mapAdmission = request.mapState
                    ? active.activation.mapAdmission(fieldSignature) : null;
            PlannedFieldAdmission fieldAdmission = !request.mapState
                    && !request.element
                    ? active.activation.fieldAdmission(fieldSignature) : null;
            String plannedInputPort = mapAdmission != null
                    ? mapAdmission.inputPort : fieldAdmission == null
                    ? "" : fieldAdmission.inputPort;
            if (allowPlannedAdmission && !plannedInputPort.isEmpty()
                    && !active.activation.matchesPlannedInputAccess(
                    plannedInputPort, method, unitIndex, owner,
                    fieldSignature, occurrence)) {
                // Producer-state admission is for the exact selected read,
                // not merely another read of the same field in the same
                // long-lived root.  A later compatible root starts a fresh
                // occurrence counter and may retry; a later access here may
                // not silently replace the recorded one.
                active.accessOwnerCarrierSelections.remove(key);
                continue;
            }
            try {
                request.selectAtAccess(active, owner, fieldSignature);
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

        /**
         * One map selected as the carrier of its own whole state. The
         * declared field is the one holding the map, and is optional: it is
         * the cross-run join, not the location.
         */
        static SharedCarrier map(Object map, String declaringClass,
                                 String fieldName, String descriptor) {
            return new SharedCarrier(map, safe(declaringClass),
                    safe(fieldName), safe(descriptor), -1, SHAPE_MAP);
        }

        boolean mapState() {
            return SHAPE_MAP.equals(shape);
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
            // The receiver's trace identity, so a version row names its own
            // location across sessions instead of borrowing a name from an
            // edge in the same summary. The VM addresses a location by a
            // per-session rid, and a summary carrying no edge has nothing to
            // borrow from; this is the identity that outlives the session.
            // 0 when the trace never recorded this object, which leaves the
            // row honestly unnameable rather than merging it with another.
            carrier.addProperty("receiverObjectId",
                    CausynthTraceRecorder.recordedObjectId(owner));
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

    /**
     * Maps a negative carrier-selection answer onto a status.  A value outside
     * the int range is a malformed answer rather than an undeclared refusal.
     */
    private static int selectStatus(long answer) {
        return answer < Integer.MIN_VALUE
                ? SharedStateEvidence.MALFORMED_ENVELOPE : (int) answer;
    }

    private static SharedStateResult unavailableShared(String stage,
                                                       String locationKey) {
        return failedShared(stage, SharedStateEvidence.API_UNAVAILABLE,
                locationKey,
                "this JDK exposes no recorded shared-state evidence API");
    }

    private static SharedStateResult failedShared(String stage, int status,
                                                  String locationKey,
                                                  String detail) {
        return new SharedStateResult(stage, status, safe(locationKey), 0L,
                new JsonObject(), SharedStateEvidence.gap(stage, status,
                locationKey, detail));
    }

    /**
     * Files one shared-state outcome with the active region.  A refusal is
     * kept as a named gap; an admitted record replaces the previous answer for
     * the same location, because the later read-out of one location is the
     * more complete one, not a second finding.
     */
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
     * owns the VM context.  It deliberately does not parse JSON: the returned
     * strings are the VM's exact bytes and can outlive the region safely.
     *
     * <p>Carriers and the ledger remain gated apart.  An RPC-only activation
     * has no carrier, but still needs the workload event ledger that orders
     * its handoff.  Failures are retained beside raw read-outs and become the
     * same named gaps during asynchronous assembly.</p>
     */
    private static RawSharedStateReadOut captureRecordedSharedStateRaw(
            ActiveRegion active, EngineApi api,
            RecordedEvidenceIdentity identity) {
        List<RawSharedCarrierReadOut> carriers = new ArrayList<>();
        for (SharedCarrier carrier
                : new ArrayList<>(active.sharedCarriers.values())) {
            try {
                if (carrier.mapState()
                        ? !api.sharedMapEvidenceAvailable()
                        : !api.sharedStateEvidenceAvailable()) {
                    carriers.add(RawSharedCarrierReadOut.failure(carrier,
                            unavailableShared(
                                    SharedStateEvidence.STAGE_VERSIONS, "")));
                    continue;
                }
                String serialized = memoizedReadOut(carrier.key());
                if (serialized == null) {
                    serialized = memoizeReadOut(carrier.key(),
                            carrier.rawVersions(api));
                }
                carriers.add(RawSharedCarrierReadOut.success(carrier,
                        serialized));
            } catch (Throwable throwable) {
                carriers.add(RawSharedCarrierReadOut.failure(carrier,
                        failedShared(SharedStateEvidence.STAGE_VERSIONS,
                                SharedStateEvidence.INVOCATION_FAILED, "",
                                rootCause(throwable))));
            }
        }

        String ledger = null;
        SharedStateResult ledgerFailure = null;
        if (!api.sharedStateEvidenceAvailable()) {
            ledgerFailure = unavailableShared(
                    SharedStateEvidence.STAGE_LEDGER, "");
        } else {
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

        private static RawSharedCarrierReadOut success(
                SharedCarrier carrier, String serialized) {
            return new RawSharedCarrierReadOut(carrier, serialized, null);
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
                if ("CUT".equals(exceptionalExitKind(throwable))) {
                    finishRootInvocation(frame.token, "CUT", "", throwable);
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
        String branchSite = siteId(method, unitIndex);
        if (skipsRelationSeedBranch(active.activation, branchSite)) {
            // A producer seed exports the relation observed at its semantic
            // output boundary.  Reading the whole accumulated path condition
            // at every incidental branch is redundant (and quadratic on
            // system traces). An explicitly selected EXPLORE branch is part
            // of that relation's requested closure and must retain its exact
            // VM-owned condition so the importer can schedule its flip.
            active.takePreparedBranch(preparedHandle);
            return observedOutcome;
        }
        if (!active.pathRecordingStarted) {
            // The symbolic gate is still closed, so no VM event exists and no
            // path condition may be read. The branch did execute, though, and
            // a recorded site is attested by execution, not by solvability.
            try {
                if (active.activation.declaresBranch(branchSite)) {
                    // A site the frozen plan declares is addressable evidence
                    // whether or not it was solvable here: its occurrence is
                    // what {@code (loopSiteId, i)} and a flip obligation are
                    // stated over.  The thin witness below carries no
                    // occurrence by design and is deduplicated by
                    // (site, outcome), so a declared site recorded only that
                    // way is unaddressable forever - and no later stage can
                    // recover the ordinal without inventing one.
                    active.recordDeclaredConcreteBranch(method, unitIndex,
                            observedOutcome);
                } else {
                    active.recordConcreteBranchWitness(method, unitIndex,
                            observedOutcome);
                }
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
                    && active.activation.targetBranch(
                    siteId(method, unitIndex), prepared.occurrence)) {
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

    /**
     * Whether a relation-only seed may pass this branch without recording it.
     *
     * <p>The economy is real - reading the whole accumulated path condition at
     * every incidental branch is quadratic on system traces - but the test has
     * to be "did the plan ask for this site", not "did the plan ask to explore
     * it".  A declared {@code PATH_ASSUMPTION} site is part of the relation's
     * requested closure exactly as much as a declared {@code EXPLORE} one: it
     * is what says which guarded case the relation published.  Skipping it
     * dropped the site before anything could record it, so the occurrence's
     * own declared branches arrived empty and the delta could only report
     * {@code PLANNED_BRANCH_EVENT_NOT_OBSERVED} for a site that did execute.
     * Declared sites are the frozen plan's own small set, so admitting all of
     * them keeps the bound the skip was introduced for.</p>
     */
    private static boolean skipsRelationSeedBranch(
            RuntimeTask task, String siteId) {
        return task != null && task.relationOnlySeed()
                && !task.declaresBranch(siteId);
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
        // One read of the event stream, used by both questions asked of it.
        // Reading it twice cost a second full serialization and decode of every
        // event this thread has ever recorded, and left a window - closed only
        // by the paused recorder - in which the two answers could disagree.
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
            // Avoid serializing and parsing the full accumulated PC merely to
            // record a concrete observation.
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
            // conditions belong to this branch.  If it cannot name one
            // contiguous window, leave a mapping gap instead of serializing
            // the whole accumulated PC.  The latter is both expensive and
            // cannot repair a malformed ownership attestation.
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

    /**
     * Reads only the absolute indices named by an exact VM branch event.
     * Failure is a local mapping gap; it never falls back to exporting the
     * thread's accumulated path condition.
     */
    private static PathConditionRead readPathConditionRange(
            EngineApi api, int start, int end) throws Exception {
        if (!api.pathConditionRangeAvailable() || start < 0
                || end <= start) {
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

    /** Marks one selected occurrence unusable before its VM close. */
    private static void abandonOccurrence(
            ActiveRegion active, String skipKind, String reason) {
        active.abandoned = true;
        endLiveSelectedRegion();
        writeSkipped(active.activation, skipKind, reason);
    }

    /** Releases an incomplete candidate so a later invocation can answer. */
    private static void abandonIncompleteRelation(
            ActiveRegion active, String reason) {
        // A candidate that did not reach all output leaves is search state,
        // not a second model result. Publishing every attempt made the
        // importer retain durable coverage gaps even when a later invocation
        // of the same task produced the complete relation. The run-end hook
        // emits one task-level unanswered-address gap if none ever succeeds.
        active.activation.noteUnaddressedCandidate(reason);
        active.abandoned = true;
        endLiveSelectedRegion();
    }

    private static JsonArray missingOutputCaptureBindingIds(
            ActiveRegion active) {
        JsonArray missing = new JsonArray();
        for (OutputCaptureSpec request : active.activation.outputCaptures) {
            // A filed row proves that the requested hook ran even when its
            // expression read-out failed.  Such a row still cannot complete
            // the relation boundary, but the binding itself is not missing.
            if (!active.hasOutputCapture(request.captureBindingId())) {
                missing.add(request.captureBindingId());
            }
        }
        return missing;
    }

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
        if ("NORMAL".equals(exitKind)
                && active.deferResponseTerminal(exitKind,
                exceptionType, output)) {
            return;
        }
        finishOccurrence(active, exitKind, exceptionType, output);
    }

    /**
     * Completes a server occurrence after its transport adapter exported the
     * returned response object while the occurrence's VM context was live.
     *
     * <p>The handler's Java return precedes serialization, so closing at the
     * injected return hook destroys the expressions the transport is about to
     * export.  A task that declares an entry-return RESPONSE handoff therefore
     * parks only its terminal; the adapter calls this method after walking the
     * real response leaves.  No identity is paired here and no value moves in
     * Java: the VM export/attach broker remains the sole propagation
     * authority.</p>
     *
     * @return {@code true} when this thread completed a parked response
     *         terminal, otherwise {@code false}
     */
    public static boolean completeResponseHandoff() {
        ActiveRegion active = activeRegion();
        if (active == null) return false;
        DeferredTerminal terminal = active.takeResponseTerminal();
        if (terminal == null) return false;
        finishOccurrence(active, terminal.exitKind,
                terminal.exceptionType, terminal.output);
        return true;
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
                // first.  Region cleanup is the final fail-closed boundary
                // for malformed or externally interrupted control flow.
                clearAccessorCallContexts(active.token);
                diag("REGION_FINISH", "token=" + active.token
                        + " task=" + safe(active.activation.taskId)
                        + " source=" + active.attributedSourceKeys()
                        + " exit=" + safe(exitKind) + " captures="
                        + active.outputCaptures.size());
                active.exitKind = safe(exitKind);
                active.exceptionType = safe(exceptionType);
                active.exitOutput = output;
                judgeFinishedOccurrence(active);
                if (!active.abandoned) {
                    String publicationFailure = configuration()
                            .commitSelectedVersions(active);
                    if (!publicationFailure.isEmpty()) {
                        // A producer version is visible to a consumer only
                        // after this occurrence has passed every anchor,
                        // replay-prefix and output-completeness gate.  A
                        // conflict is retained in this result as an explicit
                        // unresolved relation.  Map and scalar/reference
                        // versions are validated together before either kind
                        // is installed in the campaign registry.
                        active.addUnresolvedOnce(publicationFailure);
                    }
                }
            } finally {
                publicationDeferred = closeOccurrence(active);
            }
        } finally {
            endBookkeeping();
            if (!publicationDeferred) endSelectedResultPublication();
        }
    }

    /**
     * Applies the admission gates a finished occurrence must pass before its
     * relation may be built.  An occurrence that fails one is abandoned with its
     * own named skip and contributes no result row.
     */
    private static void judgeFinishedOccurrence(ActiveRegion active) {
        // First, because it is the only gate that asks whether this
        // activation is the addressed occurrence at all.  A candidate that is
        // not cannot contradict a prefix or a seed outcome it was never meant
        // to satisfy, and naming it as a contradiction would report a wrong
        // path where the run merely held another activation of the same root.
        String unaddressed =
                active.activation.rootContextSelector.unconfirmed(
                        active.attributedSourceKeys());
        if (!unaddressed.isEmpty()) {
            // A candidate that is not the addressed occurrence is the
            // candidate loop working, not a finding, so it is released
            // without a durable row.  Mid-run neither half of the reason is
            // decidable either: an anchored source that is unregistered now
            // may be registered later in the same run - a node restart is
            // exactly that - and a run that published "never registered in
            // this run" before its own restart contradicted itself once per
            // rejected candidate.  The address is stated once, after the
            // run, and only if nothing ever answered it.
            active.activation.noteUnaddressedCandidate(unaddressed);
            active.abandoned = true;
            endLiveSelectedRegion();
            return;
        }
        if (active.hasPendingPlannedProducerPrerequisites()) {
            // A concrete read before its exact selected writer commits is a
            // candidate-order miss.  It cannot authorize a local concrete
            // fallback, and it is not yet proof that the frozen edge is
            // absent.  Release this candidate; a later compatible activation
            // may observe the same declared access after publication.  If no
            // activation does, the run-end unanswered-address row is the one
            // durable bounded gap.
            abandonIncompleteRelation(active,
                    active.pendingPlannedProducerPrerequisiteReason());
            return;
        }
        // A target address that several activations of one region on one
        // source answer is separated by the only thing that distinguishes
        // them: whether this activation reached the declared target event.
        // One that did not has not answered the address, so it releases it
        // by name and the next candidate is tried - which is what README
        // OCC-1 means by treating each target occurrence as a candidate.
        // Publishing it instead would let the first activation claim an
        // address it did not answer and make every later one ambiguous.
        if (active.activation.declaresTargetBranch()
                && active.targetReach == null) {
            abandonOccurrence(active, SKIP_TARGET_EVENT_NOT_REACHED,
                    "activation did not reach the declared target event "
                            + active.activation.targetBranchLabel());
            return;
        }
        if (active.replayPrefixContradicted()) {
            abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                    "activation contradicts the recorded replay prefix: "
                            + active.replayProgress.failure());
            return;
        }
        if (incompleteRelationOnlyBoundary(active.activation,
                active.outputCaptures, active.exitKind)) {
            abandonIncompleteRelation(active,
                    "compatible root ended before every demanded semantic "
                            + "output boundary was observed");
            return;
        }
        // Replay progress is frozen at this terminal.  An unfinished prefix is
        // a recoverable candidate miss, so release it before output building or
        // raw shared-state serialization can hold the owner while later
        // compatible instances pass.  A contradiction remains the stronger
        // finding above and keeps its existing priority.
        if (active.activation.replayContract != null) {
            if (!active.replayProgress.complete()) {
                abandonOccurrence(active, SKIP_REPLAY_PREFIX_UNMATCHED,
                        "no compatible activation matched replay prefix: "
                                + active.replayProgress.failure());
            }
            return;
        }
        // A producer path replay can make the canonical target task take its
        // planned failure branch. That is a direct target witness, not a bad
        // seed replay. Keep the ordinary seed-outcome gate for every other
        // deviation; only the exact selected site, occurrence and required
        // outcome can return here.
        if (active.activation.reachedRequiredTargetOutcome(
                active.targetReach)) {
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
     * Reads one occurrence and closes its VM region on the owner thread, then
     * transfers JSON decoding and durable publication to the daemon pool.
     *
     * @return true only when the publication executor owns the in-flight
     *         publication counter
     */
    private static boolean closeOccurrence(ActiveRegion active) {
        if (!active.beginClose()) return false;
        EngineApi api = engine();
        boolean engineFinished = false;
        String rawEngineSummary = null;
        RawSharedStateReadOut rawSharedState = null;
        JsonObject result = null;
        try {
            // Everything below is observational bookkeeping.  Pause PC
            // recording before any null checks, Gson work, or string building
            // can reuse a symbolic value and manufacture a false condition.
            api.pausePathCondition();
            beginReadOutMemo();
            try {
                // A response port is judged over the whole bounded caller,
                // not over each producer candidate it tried.  Finalize the
                // provisional miss even for an abandoned close so no state
                // can survive this ActiveRegion; abandoned candidates still
                // publish no relation row by the existing rule below.
                active.flushPendingResponseHandoffGaps();
                if (!active.abandoned) {
                    result = new JsonObject();
                    // One ordinal names every row assembled for this close.
                    // Freeze it before output building, but read shared state
                    // only afterwards: output capture can publish the final
                    // field/container version that the raw envelope must see.
                    active.beginEvidenceSnapshot();
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
                endReadOutMemo();
            }
            String summary = api.finish();
            engineFinished = true;
            if (jsonObjectEnvelope(summary)) {
                // The VM already serialized this large object.  Keep it raw
                // and splice it into the JSONL record below; parsing and then
                // re-serializing it under the interpreter is needlessly
                // quadratic for real system paths.
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
            PENDING_RESPONSE_ATTACH_PORTS.remove();
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
            // fallback.  The candidate remains explicitly unanswered and the
            // campaign receives the same failing contribution as a durable
            // append failure.
            diagAfterVmClose("RESULT_PUBLICATION_REJECTED",
                    rootCause(rejected));
            configuration().releaseCandidate(active.activation);
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
                configuration().claimOccurrence(active.activation);
            } else {
                configuration().releaseCandidate(active.activation);
            }
            haltWhenCampaignSettled(active.activation.taskId,
                    written ? 0 : 2);
        } catch (Throwable failure) {
            // An asynchronous failure must not leave the task permanently
            // candidateLive.  No partial result is claimed.
            diagAfterVmClose("RESULT_PUBLICATION_FAILED",
                    rootCause(failure));
            configuration().releaseCandidate(active.activation);
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
        if (active.missingSelectedInputIsUnresolved()) {
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
            } catch (Throwable throwable) {
                result.addProperty("outputExpressionError",
                        rootCause(throwable));
            }
        }
    }

    /**
     * Ends the workload once every campaign task has reached a terminal
     * outcome, when the caller asked for that.
     *
     * <p>A concolic replay is an isolated worker, so a long-running system
     * test need not run on after its selected results exist.  Under a
     * campaign the trigger is deliberately the <em>last</em> task and not the
     * first: halting after the first publication would kill the sibling tasks
     * that are still live on other threads, which is precisely the evidence a
     * campaign exists to collect.  The status is the worst contribution any
     * task made, so a one-task campaign keeps the previous truth table
     * exactly.</p>
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
            if (active.boundedOutputVersionSlot(request, occurrence)) {
                recordRegionExitFieldOutput(active, request, owner, value,
                        occurrence);
            }
        }
    }

    /**
     * Copies {@code rows} with the identity stamp applied to each.
     *
     * <p>A record already stamped at capture keeps that stamp: it names the
     * batch the read-out really happened in, which is the point of the
     * ordinal, and overwriting it here would replace an observation with the
     * moment it was serialized.</p>
     */
    private static JsonArray stamped(List<JsonObject> rows,
                                     RecordedEvidenceIdentity identity) {
        JsonArray stamped = new JsonArray();
        for (JsonObject row : rows) {
            JsonObject copy = copyJsonTree(row);
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
        if (!active.loopCardinalities.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITIES,
                    GSON.toJsonTree(active.loopCardinalities));
        }
        if (!active.loopCardinalityGaps.isEmpty()) {
            result.add(LoopBoundPolicy.LOOP_CARDINALITY_GAPS,
                    GSON.toJsonTree(active.loopCardinalityGaps));
        }
        active.validateRegionExitFieldCaptures(exitKind);
        active.validateConfiguredSymbolicSources();
        active.nameUnreachedTargetBranch();
        if (active.targetReach != null) {
            result.add("targetReach", active.targetReach);
        }
        result.add("unresolvedInputs", GSON.toJsonTree(active.unresolved));
        result.add("symbolizedInputs", GSON.toJsonTree(active.symbolized));
        SymbolicSourceEvidence.writeTo(result,
                new ArrayList<>(active.symbolicSources.values()));
        result.add("branchMappings", GSON.toJsonTree(active.branchMappings));
        if (!active.concreteBranchWitnesses.isEmpty()) {
            result.add("concreteBranchWitnesses",
                    GSON.toJsonTree(active.concreteBranchWitnesses));
        }
        result.add("outputCaptures", GSON.toJsonTree(active.outputCaptures));
        // Every evidence row this activation publishes names the run, the
        // session, the activation, and the read-out batch it came from.  A
        // consumer that had to infer any of those - and the only material it
        // could infer them from is row counts and arrival order - would be
        // guessing about exactly the identities the composition binds on.
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
        JsonArray mapCarriers = selectedMapCarriers(active);
        if (mapCarriers.size() > 0) {
            // Which maps this activation selected, beside the evidence they
            // produced.  A carrier that selected and published nothing is
            // still a fact about the run - it says the location was watched -
            // and it is the one fact the versions member cannot state.
            result.add("sharedMapCarriers", mapCarriers);
        }
        if (active.sessionEventLedger != null) {
            result.add("sessionEventLedger",
                    copyJsonTree(active.sessionEventLedger));
        }
        if (!active.sharedStateGaps.isEmpty()) {
            result.add("sharedStateGaps",
                    stamped(active.sharedStateGaps, identity));
        }
    }

    /** The maps this activation selected as whole-state carriers. */
    private static JsonArray selectedMapCarriers(ActiveRegion active) {
        JsonArray carriers = new JsonArray();
        for (SharedCarrier carrier : active.sharedCarriers.values()) {
            if (carrier.mapState()) carriers.add(carrier.toJson());
        }
        return carriers;
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

    /**
     * The value at the end of {@code path}, starting from {@code root}.
     *
     * <p>{@link #resolveFieldPathLeafOwner} stops one segment short, because
     * its callers symbolize the leaf field and need the object that declares
     * it. A carrier declaration that names an array needs the array itself,
     * which is the value of that same last segment.</p>
     */
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
     * that scopes separately symbolized leaves.  If the VM has a native
     * container model we retain it; otherwise the exact observed container is
     * a concrete slot, not an unresolved scalar input.
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

    /** Exact live field named by a VM handoff export. */
    private static Field declaredInstanceField(
            Object owner, String declaringClass, String fieldName,
            String descriptor) {
        if (owner == null || safe(declaringClass).isEmpty()
                || safe(fieldName).isEmpty() || safe(descriptor).isEmpty()) {
            return null;
        }
        Class<?> type = owner.getClass();
        while (type != null && !declaringClass.equals(type.getName())) {
            type = type.getSuperclass();
        }
        if (type == null) return null;
        try {
            Field field = type.getDeclaredField(fieldName);
            if (Modifier.isStatic(field.getModifiers())
                    || !descriptor.equals(javaTypeDescriptor(
                    field.getType().getTypeName()))) {
                return null;
            }
            if (!field.isAccessible()) field.setAccessible(true);
            return field;
        } catch (Throwable unavailable) {
            return null;
        }
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
     * is the machine-readable half: a skip that was never admitted is a plan
     * outcome, while a skip that ran and contradicted its recording is a
     * finding about the path, and a reader that cannot tell them apart
     * reports one as the other.
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
        if (haltStatus >= 0) {
            // A durable terminal skip is not a successful replay result.  It
            // settles this task nonzero; the workload still ends only once
            // every campaign task has settled.
            haltWhenCampaignSettled(activation.taskId, haltStatus);
        }
    }

    /**
     * The halt-status contribution of a skip that ends its task, or -1 when
     * the task may still publish.
     */
    static int terminalSelectedSkipHaltStatus(
            String skipKind, String reason, boolean written) {
        // A replay-prefix mismatch is not terminal: a later compatible
        // activation of the same task may still match the recorded prefix.
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

    /** Diagnostic for daemon publication, where no VM context may be called. */
    private static void diagAfterVmClose(String event, String detail) {
        if (!diagnosticsEnabled()) return;
        try {
            System.err.println("CAUSYNTH-DIAG|"
                    + System.currentTimeMillis() + "|t"
                    + Thread.currentThread().getId() + "|heapMB"
                    + (Runtime.getRuntime().totalMemory()
                    - Runtime.getRuntime().freeMemory()) / 1048576L + "|"
                    + safe(event) + "|" + safe(detail));
        } catch (Throwable ignored) {
            // Diagnostics never fail publication.
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
     *
     * <p>Elements are addressed by their <em>absolute</em> index in the
     * thread's one append-only path condition, which is the index an exact VM
     * branch event names.  A whole-document read starts that numbering at 0; a
     * window read of {@code [base, windowEnd)} starts it at {@code base} and
     * refuses every index outside its own window rather than shifting one.
     * {@link #size()} always answers the same question either way - how many
     * conditions the thread has accumulated - so a caller that only needs the
     * suffix does not have to know which reader answered.</p>
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
        }

        /**
         * Reads a serialized path condition.  A document that is not an array
         * of values carries no conditions, which is what the tree parser
         * reported for it before.
         */
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
         *
         * <p>{@code null} means "this envelope cannot be read as that window
         * with certainty" - a malformed document, a window that does not start
         * where the caller asked, or an element count that disagrees with the
         * indices the VM stamped.  A caller that gets {@code null} must read
         * the whole path condition instead; it must never treat a window it
         * could not verify as the accumulated condition list, because the
         * absolute index an exact branch event names would then address the
         * wrong element.</p>
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
            // The window's own indices are the authority on what it holds.  A
            // count that disagrees with them means an element the VM did not
            // serialize, and an absolute index would then be off by however
            // many of those there were.
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
            return parseJson(raw.substring(
                    bounds[2 * offset], bounds[2 * offset + 1]));
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
         * <p>The keys are matched where a key may appear and nowhere else.
         * Searching the text for a quoted name would find one inside a
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
        private int versionOrdinal;
        private PendingMutationCapture pending;
        private boolean ambiguousContainer;
        private Object atomicPreparedReceiver;

        /** How this invocation absorbed one selected mutation. */
        enum Selection { ANCHORED, FOLDED, AMBIGUOUS, IGNORED }

        /**
         * A mutation relation denotes the container state at the definition
         * invocation's normal exit.  Repeating the selected mutator on the
         * same receiver is therefore the ordinary fold (one invocation adds
         * every element) and keeps the first mutation as the anchor.
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

        /** The first selected Atomic call owns this invocation's pre-state. */
        boolean claimAtomicPreparation(Object receiver) {
            if (atomicPreparedReceiver != null) return false;
            atomicPreparedReceiver = receiver;
            return true;
        }

    }

    private static final class ActiveRegion {
        private final long token;
        private final RuntimeTask activation;
        private final Object receiver;
        private final Thread thread;
        private final AtomicBoolean finished = new AtomicBoolean();
        private boolean prepared;
        /**
         * The declared target branch event this occurrence decided, or
         * {@code null} while it has not decided one.
         *
         * <p>Reaching the target is evidence the case carries to its own
         * terminal, not a terminal of its own: a handler observes the target
         * inside itself and still owes the response its caller attaches, and
         * a case that ended at the observation lost every effect after it.
         * </p>
         */
        private JsonObject targetReach;
        /** Terminal outcome, frozen when the occurrence stops running. */
        private boolean abandoned;
        private boolean closed;
        /** Normal handler return parked until response serialization ends. */
        private DeferredTerminal responseTerminal;
        /**
         * Loop bodies this activation has charged.  Written only by its own
         * root thread and read by the process-exit barrier as the one cheap
         * proof that a still-live occurrence is executing rather than stuck.
         */
        private volatile long chargedLoopBodies;
        /**
         * The stable causal context this candidate observed while it was
         * live: the logical sources it ran on and the external request scopes
         * it ran inside.
         *
         * <p>Both are established by the application <em>inside</em> its own
         * entry method - a thread-entry root is entered before its source is
         * registered, and a handler receives the sender's scope later still -
         * so neither can be read at the entry hook.  Recording them as they
         * happen is what lets the finish gate say whether this activation is
         * the occurrence its plan row addressed.</p>
         */
        private final Set<String> observedSourceKeys = new LinkedHashSet<>();
        /**
         * Every stable source this occurrence can be attributed to by the
         * application's own registration.
         *
         * <p>Two kinds of evidence, both produced by the replay itself.  The
         * first is what the thread's trace context published while this
         * occurrence was live - a workload that opens a request scope or
         * records an RPC leg names its source that way.  The second is the
         * source registered <em>for this occurrence's own receiver</em>, and
         * it is the one that matters for a long-lived service: a node binds
         * its receiver to its source once at start-up
         * ({@code registerSource}/{@code registerSourceAlias}) and never
         * opens a request scope on the threads that later run the selected
         * region.  That binding is ordinary application code, so it happens
         * in every replay; nothing about it depends on the discovery session
         * recurring.</p>
         *
         * <p>Reading it here rather than at entry is deliberate: a receiver
         * built during start-up is older than the source declaration that
         * names it, so the alias may be flushed after this region began.</p>
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

        private synchronized boolean deferResponseTerminal(
                String exitKind, String exceptionType, Object output) {
            if (!activation.exportsResponseHandoff) return false;
            if (responseTerminal != null) {
                throw new IllegalStateException(
                        "response terminal already deferred");
            }
            responseTerminal = new DeferredTerminal(exitKind,
                    exceptionType, output);
            return true;
        }

        private synchronized DeferredTerminal takeResponseTerminal() {
            DeferredTerminal terminal = responseTerminal;
            responseTerminal = null;
            return terminal;
        }
        private String exitKind = "";
        private String exceptionType = "";
        private Object exitOutput;
        private final List<String> symbolized = new ArrayList<>();
        /** Exact configured source roots materialized by this activation. */
        private final Map<String, JsonObject> symbolicSources =
                new LinkedHashMap<>();
        /** Object identity prevents one source id from naming two fields. */
        private final Map<String, Object> symbolicSourceOwners =
                new LinkedHashMap<>();
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
        /**
         * Map versions produced by this candidate but not yet visible to a
         * consumer.  They are committed only after the occurrence passes its
         * terminal admission gates; an abandoned candidate therefore cannot
         * leak a native state handle into a later accepted consumer.
         */
        private final Map<String, Long> stagedMapVersions =
                new LinkedHashMap<>();
        /** Scalar/reference versions staged until this producer is accepted. */
        private final Map<String, Long> stagedFieldVersions =
                new LinkedHashMap<>();
        /**
         * Case-local references into the VM's own handoff ledger: the
         * declared port an attach landed on and the export event the
         * {@code VALUE_HANDOFF} edge relates it to.
         */
        private final List<JsonObject> vmHandoffEvents = new ArrayList<>();
        /** Response component ports already attached in this bounded case. */
        private final Set<String> satisfiedResponseHandoffPorts =
                new LinkedHashSet<>();
        /**
         * Provisional handle misses while searching repeated response
         * candidates.  Bounded by declared response port, never by the
         * number of concrete exchanges a long-lived caller executes.
         */
        private final Map<String, JsonObject> pendingResponseHandoffGaps =
                new LinkedHashMap<>();
        private final List<JsonObject> rpcHandoffGaps = new ArrayList<>();

        private synchronized void deferResponseHandoffGap(
                String portId, JsonObject gap) {
            String port = safe(portId);
            if (port.isEmpty() || satisfiedResponseHandoffPorts.contains(
                    port)) return;
            if (!pendingResponseHandoffGaps.containsKey(port)) {
                pendingResponseHandoffGaps.put(port, gap);
            }
        }

        private synchronized void markResponseHandoffSatisfied(
                String portId) {
            String port = safe(portId);
            if (port.isEmpty()) return;
            satisfiedResponseHandoffPorts.add(port);
            pendingResponseHandoffGaps.remove(port);
        }

        private synchronized boolean responseHandoffSatisfied(
                String portId) {
            return !safe(portId).isEmpty()
                    && satisfiedResponseHandoffPorts.contains(portId);
        }

        private synchronized void flushPendingResponseHandoffGaps() {
            for (Map.Entry<String, JsonObject> entry
                    : pendingResponseHandoffGaps.entrySet()) {
                if (!satisfiedResponseHandoffPorts.contains(entry.getKey())) {
                    rpcHandoffGaps.add(entry.getValue());
                }
            }
            pendingResponseHandoffGaps.clear();
        }
        /**
         * Shared locations this activation selected as symbolic carriers, and
         * the evidence read back from them.  A record is keyed by the VM's own
         * location identity so a second read-out of one location replaces the
         * first rather than doubling it; a gap is appended, because two
         * refusals are two facts about the run.
         */
        private final Map<String, SharedCarrier> sharedCarriers =
                new LinkedHashMap<>();
        /** Exact access-owner carrier declarations already selected here. */
        private final Set<String> accessOwnerCarrierSelections =
                new LinkedHashSet<>();
        /**
         * Exact upstream inputs observed before their selected producer had
         * committed a version.
         *
         * <p>This is candidate-local search state, not a shared-state gap.
         * One entry per declared input bounds repeated polling in a
         * long-lived root.  A successful later admission removes it; a
         * terminal with entries releases the candidate so another compatible
         * activation can answer the same causal address.</p>
         */
        private final Map<String, String> pendingPlannedProducerPrerequisites =
                new LinkedHashMap<>();
        private final Map<String, JsonObject> sharedStateRecords =
                new LinkedHashMap<>();
        private final List<JsonObject> sharedStateGaps = new ArrayList<>();

        private synchronized void deferPlannedProducerPrerequisite(
                String inputPort, String detail) {
            String port = safe(inputPort);
            if (port.isEmpty()) return;
            pendingPlannedProducerPrerequisites.putIfAbsent(port,
                    safe(detail));
        }

        private synchronized void resolvePlannedProducerPrerequisite(
                String inputPort) {
            pendingPlannedProducerPrerequisites.remove(safe(inputPort));
        }

        private synchronized boolean plannedProducerPrerequisitePending(
                String inputPort) {
            return pendingPlannedProducerPrerequisites.containsKey(
                    safe(inputPort));
        }

        private synchronized boolean hasPendingPlannedProducerPrerequisites() {
            return !pendingPlannedProducerPrerequisites.isEmpty();
        }

        private synchronized String pendingPlannedProducerPrerequisiteReason() {
            return "exact planned input producer was not yet committed: "
                    + new LinkedHashMap<>(
                    pendingPlannedProducerPrerequisites);
        }
        /**
         * Read-cut gates this activation admitted as observations, and the
         * named gaps of the ones it refused.  They are kept apart for the same
         * reason successful evidence is kept apart from a gap: one may become
         * a confirmed read-from, the other never may.
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
        /**
         * Records a declared branch site that executed before the symbolic
         * gate opened.
         *
         * <p>Emitted as an ordinary {@code branchMappings} row so the site
         * keeps its activation-local occurrence, and carrying a
         * {@code concreteObservation} rather than a {@code witness} so it can
         * never be mistaken for a symbolic decision: there was no VM event and
         * no path condition, and the row says exactly that.  This is the same
         * shape the symbolic path publishes when the VM attests that a
         * declared branch contributed no condition.</p>
         */
        private void recordDeclaredConcreteBranch(
                String method, int unitIndex, boolean outcome) {
            String site = siteId(method, unitIndex);
            int occurrence = nextBranchOccurrence(site);
            JsonObject mapping = branchMapping(method, unitIndex, occurrence);
            mapping.addProperty("rawPathConditionSize", 0);
            mapping.addProperty("rawPathConditionBaseline", 0);
            mapping.add("concreteObservation",
                    ExactConcreteBranchObservation.attested(site,
                            safe(method), unitIndex, occurrence, outcome)
                            .toJson());
            branchMappings.add(mapping);
            witnessOutcome(site, outcome);
        }

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
            // One completed definition invocation publishes one state
            // version. All container operations inside that invocation (for
            // example a fixed array/for walk performing several puts) fold
            // into that version and must not spend extra bounded slots. A
            // later invocation reached by replay receives the next version.
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
                // once now that the count is final.  The refusal itself was
                // published per-occurrence and cannot carry this: it is asked
                // while the site is still executing, so every number it could
                // quote is a lower bound.  Both halves in one row let a
                // reader size the real bound instead of rediscovering it.
                int observed = outputCaptureOccurrences.observed(
                        request.captureBindingId(), request.outputSiteId());
                int capacity = activation.loopBound.maxBackedgeTraversals();
                if (observed > capacity) {
                    addUnresolvedOnce(request.captureBindingId()
                            + ": bounded output version capacity " + capacity
                            + " held " + matches + " of " + observed
                            + " observed " + observedUnit + " at "
                            + request.outputSiteId());
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

        /**
         * Whether this execution of a declared output site may produce a
         * relation version.
         *
         * <p>The only rule is the capture's own declared prerequisite: its
         * input ports must already exist, because a hook that runs before
         * them has nothing to state the relation over.  A successful earlier
         * occurrence is deliberately <em>not</em> a reason to refuse: a later
         * execution of the same site is another bounded version of the same
         * relation, which {@link #nextOutputCaptureOccurrence} ordinals and
         * the importer exports as one version set.  Refusing it made the
         * later heartbeat, rotation or reissue of a long-lived occurrence
         * look exactly like a site that never ran again.</p>
         */
        private boolean captureEligible(OutputCaptureSpec request) {
            if (request == null) return false;
            return activation.capturePrerequisitesSatisfied(
                    request.captureBindingId(), symbolized,
                    observedInputSlots);
        }

        /**
         * Whether the counted occurrence still has a bounded version slot.
         *
         * <p>Every execution is counted before this is asked, so the observed
         * count stays true whatever the answer is.  The capacity is the
         * activation's own declared executor limit - the largest {@code K_L}
         * the campaign declared - because that is how many bounded slots its
         * model holds; the occurrence ordinal itself counts nested calls and
         * every loop nest, so it is not a loop body index.  README's resource
         * rule applies to the versions past it: they are named once per port
         * and never silently absent.</p>
         */
        private boolean boundedOutputVersionSlot(
                OutputCaptureSpec request, int occurrence) {
            int capacity = activation.loopBound.maxBackedgeTraversals();
            if (occurrence >= 1 && occurrence <= capacity) return true;
            // Deliberately without the observed count.  This fires on every
            // occurrence past the capacity, and addUnresolvedOnce dedupes on
            // the exact string, so a running count here would publish one row
            // per excess occurrence - each carrying a number that is only a
            // lower bound at the moment it was taken.  The total is stated
            // once, at the terminal, by validateRegionExitFieldCaptures.
            addUnresolvedOnce(request.captureBindingId()
                    + ": bounded output version capacity " + capacity
                    + " reached at " + request.outputSiteId()
                    + "; later occurrences are counted, not captured");
            return false;
        }

        /**
         * Whether every demanded output relation of this occurrence produced
         * at least one admitted version by now.
         *
         * <p>A flip is asked what its decision does to the relation, so the
         * versions captured before that decision cannot answer it.</p>
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
         * A relation-only seed that reached every demanded semantic output
         * is still a valid witnessed constant relation when none of its
         * optional solver dimensions materialized on this replay.  Other
         * tasks retain the strict missing-input diagnostic.
         */
        private boolean missingSelectedInputIsUnresolved() {
            return !activation.symbolize.isEmpty()
                    && !pathRecordingStarted
                    && !(activation.relationOnlySeed()
                    && demandedOutputRelationComplete());
        }

        /**
         * Names a declared target branch event this occurrence never decided.
         *
         * <p>The occurrence ran to its own terminal, so the demand cannot be
         * met later; an unmet demand is a gap with a subject rather than a
         * summary that simply carries no target.</p>
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
         *
         * <p>Only the first decision of the declared event is the target the
         * plan selected; a later occurrence of the same site is another
         * event, and overwriting would rename the reach after it.</p>
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

        /** 1=new claim, 0=idempotent same owner, -1=conflict. */
        private synchronized int claimSymbolicSource(
                String sourceId, Object owner) {
            Object prior = symbolicSourceOwners.get(sourceId);
            if (prior == owner) return 0;
            if (prior != null) {
                addUnresolvedOnce(sourceId
                        + ": one configured source reached two owners");
                return -1;
            }
            symbolicSourceOwners.put(sourceId, owner);
            return 1;
        }

        private synchronized void recordSymbolicSource(
                String sourceId, JsonObject evidence) {
            JsonObject prior = symbolicSources.putIfAbsent(sourceId,
                    evidence.deepCopy());
            if (prior != null && !prior.equals(evidence)) {
                addUnresolvedOnce(sourceId
                        + ": configured source produced conflicting "
                        + "expressions");
            }
        }

        /** Exact raw VM names staged by this candidate's source hooks. */
        private synchronized Map<String, String> stagedSourceSymbols() {
            Map<String, String> result = new LinkedHashMap<>();
            for (Map.Entry<String, JsonObject> entry
                    : symbolicSources.entrySet()) {
                String raw = string(entry.getValue(), "rawSymbol");
                if (!raw.isEmpty()) result.put(entry.getKey(), raw);
            }
            return result;
        }

        private synchronized void releaseSymbolicSourceClaim(
                String sourceId, Object owner) {
            if (!symbolicSources.containsKey(sourceId)
                    && symbolicSourceOwners.get(sourceId) == owner) {
                symbolicSourceOwners.remove(sourceId);
            }
        }

        private synchronized void validateConfiguredSymbolicSources() {
            for (String sourceId : activation.sourceFields.keySet()) {
                if (!symbolicSources.containsKey(sourceId)) {
                    addUnresolvedOnce(sourceId
                            + ": CONFIGURED_SYMBOLIC_SOURCE_NOT_MATERIALIZED");
                }
            }
        }

        private synchronized String stageMapVersion(
                String outputPort, long versionId) {
            String port = safe(outputPort);
            if (port.isEmpty() || versionId <= 0L) {
                return "selected Map producer returned no exact current "
                        + "version for " + port;
            }
            Long prior = stagedMapVersions.putIfAbsent(port, versionId);
            if (prior != null && prior.longValue() != versionId) {
                return "selected Map producer captured conflicting versions "
                        + prior + " and " + versionId + " for " + port;
            }
            return "";
        }

        private synchronized Map<String, Long> stagedMapVersions() {
            return new LinkedHashMap<>(stagedMapVersions);
        }

        private synchronized String stageFieldVersion(
                String outputPort, long versionId) {
            String port = safe(outputPort);
            if (port.isEmpty() || versionId <= 0L) {
                return "selected field producer returned no exact current "
                        + "version for " + port;
            }
            Long prior = stagedFieldVersions.putIfAbsent(port, versionId);
            if (prior != null && prior.longValue() != versionId) {
                return "selected field producer captured conflicting "
                        + "versions " + prior + " and " + versionId
                        + " for " + port;
            }
            return "";
        }

        private synchronized Map<String, Long> stagedFieldVersions() {
            return new LinkedHashMap<>(stagedFieldVersions);
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

        /** Opens a fresh batch for the read-out that is about to happen. */
        private void beginEvidenceSnapshot() {
            evidenceSnapshot = EVIDENCE_SNAPSHOTS.incrementAndGet();
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

        private void recordSymbolizedInputPort(String symbol, Object value) {
            if (value == null) return;
            String previous = symbolizedInputPorts.get(value);
            symbolizedInputPorts.put(value, previous == null
                    || previous.equals(symbol) ? symbol : "");
        }

        private String symbolizedInputPort(Object value) {
            return value == null ? "" : safe(symbolizedInputPorts.get(value));
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

        /** One solver value for one exact configured source hook. */
        private ModelAssignment configuredSourceAssignment(
                String sourceId, String fieldSignature) {
            ModelAssignment selected = null;
            for (ModelAssignment candidate : activation.modelAssignments) {
                if (!candidate.matchesConfiguredSource(sourceId,
                        fieldSignature)
                        || appliedModelAssignments.contains(candidate.key)) {
                    continue;
                }
                if (selected != null) {
                    addUnresolvedOnce(sourceId
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
         * <p>Separate from {@link #traversals}: that ledger belongs only to
         * declared condition-controlled loops and enforces their exact K_L.
         * This resource ledger is also spent by fixed-count array loops and
         * replay-path service loops, so work outside the symbolic loop space
         * remains finite without changing its semantics.</p>
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
        private final String intraRegionSourceOutputPort;
        private final String intraRegionReadFromAuthority;
        private final String symbolicDemand;
        private final String rootKind;
        private final List<String> fieldPath;
        private final String javaType;
        private final String observedPrimitiveValue;
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
            String explicitLeafSignature = string(json,
                    "leafFieldSignature");
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
            this.observedPrimitiveValue = string(json, "primitiveValue");
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

        private boolean observedFieldReceiverRoot() {
            return "OBSERVED_FIELD_RECEIVER".equals(rootKind);
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
            // leaf name alone aliases unrelated fields that happen to share a
            // name across two declaring types, which is common where one type
            // carries a transferable copy of another's state.  Only an
            // explicit owner or an exact declared-field signature is
            // authoritative enough to symbolize a concrete field access.
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
            this.engineSymbol = string(json, "engineSymbol");
            this.inputSymbol = string(json, "inputSymbol");
            this.valueType = string(json, "valueType");
            this.value = string(json, "value");
            this.referenceSourceInputSymbol = string(json,
                    "referenceSourceInputSymbol");
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

        private boolean configuredSourceAssignment() {
            return !configuredSourceId.isEmpty()
                    || !configuredSourceFieldSignature.isEmpty();
        }

        private boolean matchesConfiguredSource(String sourceId,
                                                 String fieldSignature) {
            return configuredSourceId.equals(safe(sourceId))
                    && configuredSourceFieldSignature.equals(
                    safe(fieldSignature))
                    && inputSymbol.equals("SOURCE:" + safe(sourceId));
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
     * each becomes knowable.  The <em>root predicate</em> - region root
     * method, receiver runtime class and thread context - is decidable at the
     * entry hook and admits a <em>candidate</em>.  The <em>causal anchor</em>
     * is the stable logical source established by the application. A fresh
     * replay may mint a different lifecycle epoch, so the epoch is not
     * identity. A configured API name is an optional entry predicate only
     * for a local root that begins inside that scope; remote handlers and
     * long-lived service continuations omit it from their selector.</p>
     *
     * <p>There is no invocation ordinal in either half.  An ordinal addresses
     * a position in a sequence of activations, so a replay whose flipped
     * branch adds or removes an earlier activation of the same root silently
     * re-points the selector at a different occurrence.  Every component here
     * is a name both the recording and the replay state for themselves.</p>
     */
    private static final class RootContextSelector {
        private final boolean receiverScoped;
        private final String receiverRuntimeClass;
        private final String threadName;
        private final String sourceKey;
        private final String requestApi;

        private RootContextSelector(boolean receiverScoped,
                                    String receiverRuntimeClass,
                                    String threadName, String sourceKey,
                                    String requestApi) {
            this.receiverScoped = receiverScoped;
            this.receiverRuntimeClass = safe(receiverRuntimeClass);
            this.threadName = stableReplayThreadContext(threadName);
            this.sourceKey = safe(sourceKey);
            this.requestApi = safe(requestApi);
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
            if (!global && (receiverClass.isEmpty()
                    || !receiverClass.equals(receiverClass.trim())
                    || !"RECEIVER_CONTEXT".equals(kind)
                    || selector.has("thread") && (thread.isEmpty()
                    || !thread.equals(thread.trim())))
                    || sourceKey.isEmpty()) {
                throw new IllegalArgumentException(
                        "rootSelector requires an exact receiver context and "
                                + "a causal anchor naming its source");
            }
            return new RootContextSelector(!global, receiverClass, thread,
                    sourceKey, requestApi);
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

        /** Whether the root entered the explicitly selected local scope. */
        private boolean matchesRequestApi(String actualRequestApi) {
            return requestApi.isEmpty()
                    || requestApi.equals(safe(actualRequestApi));
        }

        /**
         * Why the candidate that just ran is not the addressed occurrence, or
         * {@code ""} when it is.
         *
         * <p>The logical source must be the declared one: an unregistered
         * workload declares the unregistered source and observes none, which
         * is the same answer stated from both ends rather than a default
         * standing in for a missing one.</p>
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
        private final String instrumentationSelector;
        private final String regionId;
        /**
         * The activation this task is.  The VM knows a write's task and a
         * read's region and nothing else about who performed them; these two
         * are what turn either into the address the pipeline joins on.
         */
        private final String sourceKey;
        private final String occurrenceId;
        /**
         * The recorded root call this occurrence ran in.
         *
         * <p>It is <b>not</b> {@link #occurrenceId}.  An {@code activationId}
         * is {@code ACT.<uuid>}, minted per recorded root call; an
         * {@code occurrenceId} is
         * {@code <sourceKey>/region/<regionId>#<n>}, minted per observed
         * activation of one region on one source.  They never compare
         * equal.</p>
         */
        private final String activationId;
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
        private final boolean hasExplicitFaultInput;
        private final Map<String, Set<String>> capturePrerequisites;
        private final Map<String, JsonObject> recordedPrimitiveOutputs;
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
         * port id.  An export site sends the port's live expression across
         * the cut; an attach site takes it.
         */
        private final Map<String, CommunicationHandoffSpec>
                communicationHandoffs = new LinkedHashMap<>();
        /** Explicit source fields this output relation is required to mint. */
        private final Map<String, SourceField> sourceFields =
                new LinkedHashMap<>();
        /** Response leaves this caller must attach after its selected cut. */
        private final Set<String> responseAttachPortIds =
                new LinkedHashSet<>();
        /** Response leaves this server occurrence exports at normal return. */
        private final Set<String> responseExportPortIds =
                new LinkedHashSet<>();
        /**
         * Planner-selected producer occurrence of each response attach port.
         * This is admission provenance, never a runtime value join.
         */
        private final Map<String, String> responseProducerOccurrenceByPort =
                new LinkedHashMap<>();
        /** Manual adapter sites indexed only by their exact VM storage. */
        private final Map<String, CommunicationHandoffSpec>
                manualCommunicationHandoffs = new LinkedHashMap<>();
        /** Whether serialization must run before this server root closes. */
        private final boolean exportsResponseHandoff;
        /** Read-cut gates the solver selected for this replay, if any. */
        private final List<JsonObject> readCutGates = new ArrayList<>();
        /** Shared locations this task selects as carriers at region entry. */
        private final List<SharedCarrierRequest> sharedCarriers =
                new ArrayList<>();
        /** Frozen runtime bindings used to resolve exact Map producers. */
        private final JsonArray edgeBindings;
        /** Exact producer member edges, indexed by published output port. */
        private final Map<String, Set<String>> outputCausalEdgesByPort =
                new LinkedHashMap<>();
        /** Exact output cell owned by each published output port. */
        private final Map<String, String> outputCellByPort =
                new LinkedHashMap<>();
        /** Failure-slice inputs of each output member. */
        private final Map<String, Set<String>> outputInputsByPort =
                new LinkedHashMap<>();
        /** Configured source identities propagated through selected edges. */
        private final Map<String, LinkedHashMap<String, PlannedSourceAlias>>
                sourceAliasesByOutputPort = new LinkedHashMap<>();
        /** Source identities arriving at exact selected input ports. */
        private final Map<String, LinkedHashMap<String, PlannedSourceAlias>>
                sourceAliasesByInputPort = new LinkedHashMap<>();
        /** One upstream Map admission per exact access-field declaration. */
        private final Map<String, PlannedMapAdmission> mapAdmissions =
                new LinkedHashMap<>();
        /** Exact concrete field producer admission by access signature. */
        private final Map<String, PlannedFieldAdmission> fieldAdmissions =
                new LinkedHashMap<>();
        /**
         * Activations that ran as candidates for this address and were not
         * the addressed occurrence, and every distinct reason they were not.
         *
         * <p>Held rather than published: whether the address went unanswered
         * is a property of the whole run, and each rejection on its own says
         * only that the loop moved on to the next candidate.</p>
         *
         * <p>Every reason, not the last one.  Keeping only the last made the
         * run state that four candidates ran and describe one of them, which
         * is precisely the question a reader asks next - the four differ by
         * owner, or by epoch, or by request scope, and one sample cannot
         * say which.  Distinct reasons are bounded by the ways an address
         * can miss, not by the number of activations.</p>
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
            this.activationId = firstNonBlank(
                    string(task.json(), "activationId"),
                    string(object(task.json(), "traceEvidence"),
                            "activationId"));
            this.rootMethod = task.rootMethod();
            this.rootContextSelector = RootContextSelector.from(rootSelector);
            this.rootArgumentSelector = RootArgumentSelector.from(
                    rootSelector);
            this.declaredSymbolize = new ArrayList<>();
            this.symbolize = new ArrayList<>();
            boolean explicitFaultInput = false;
            boolean responseHandoff = false;
            this.branchPolicies = new LinkedHashMap<>();
            this.seedOutcomes = new LinkedHashMap<>();
            this.loopBound = task.loopBound();
            this.modelAssignments = new ArrayList<>();
            this.outputCaptures = new ArrayList<>();
            this.capturesOutputRelation =
                    task.goalKind().capturesOutputRelation();
            this.capturePrerequisites = new LinkedHashMap<>();
            this.recordedPrimitiveOutputs = new LinkedHashMap<>();
            this.executionScopeMethods = new LinkedHashSet<>();
            this.edgeBindings = task.edgeBindings().deepCopy();
            Set<String> selectedOutputCells = new LinkedHashSet<>();
            if (task.outputClosure() != null) {
                this.executionScopeMethods.addAll(
                        task.outputClosure().executionScope().methods());
                for (OutputClosureContract.Member member
                        : task.outputClosure().members()) {
                    selectedOutputCells.add(member.cell());
                    Set<String> memberEdges = new LinkedHashSet<>();
                    for (JsonElement edge : array(member.slice(),
                            "causalEdgeIds")) {
                        if (edge.isJsonPrimitive()) {
                            memberEdges.add(safe(edge.getAsString()));
                        }
                    }
                    outputCausalEdgesByPort.put(member.portId(),
                            memberEdges);
                    outputCellByPort.put(member.portId(), member.cell());
                    Set<String> memberInputs = new LinkedHashSet<>();
                    for (JsonElement input : array(member.slice(),
                            "inputPorts")) {
                        if (input.isJsonPrimitive()) {
                            memberInputs.add(safe(input.getAsString()));
                        }
                    }
                    outputInputsByPort.put(member.portId(), memberInputs);
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
            indexCapturePrerequisites(task.outputClosure());
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
                responseHandoff |= site.exportsEntryReturn()
                        && "RESPONSE".equals(site.direction());
                if (site.attachesCutReturn()
                        && "RESPONSE".equals(site.direction())) {
                    responseAttachPortIds.add(site.portId());
                }
                if (site.exportsEntryReturn()
                        && "RESPONSE".equals(site.direction())) {
                    responseExportPortIds.add(site.portId());
                }
                // A region that holds both sides of a cut declares the same
                // port twice, once per role, and each role has its own site.
                // Two sites of one role would be two answers to one
                // question, and are refused rather than resolved by order.
                if (communicationHandoffs.put(handoffKey(site.portId(),
                        site.exports()), site) != null) {
                    throw new IllegalArgumentException(
                            "communication port declares two handoff sites "
                            + "in " + taskId + ": " + site.portId());
                }
                if (site.manualCarrier()
                        && manualCommunicationHandoffs.put(
                        handoffCarrierKey(site.carrierClass(),
                                site.carrierField(),
                                site.carrierDescriptor(), site.exports()),
                        site) != null) {
                    throw new IllegalArgumentException(
                            "communication handoff declares two ports for "
                                    + "one manual carrier in " + taskId
                                    + ": " + site.siteId());
                }
            }
            for (JsonElement element : array(task.json(),
                    SymbolicSourceEvidence.TASK_FIELD)) {
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            SymbolicSourceEvidence.TASK_FIELD
                                    + " entries must be objects");
                }
                SourceField source = SourceField.from(
                        element.getAsJsonObject());
                if (!selectedOutputCells.containsAll(
                        source.requiredOutputFieldSignatures)) {
                    throw new IllegalArgumentException(
                            "configured symbolic source requires output "
                                    + "outside this task closure: "
                                    + source.sourceId);
                }
                if (sourceFields.put(source.sourceId, source) != null) {
                    throw new IllegalArgumentException(
                            "task declares one symbolic source twice: "
                                    + source.sourceId);
                }
            }
            for (ModelAssignment assignment : modelAssignments) {
                if (!assignment.configuredSourceAssignment()) continue;
                SourceField source = sourceFields.get(
                        assignment.configuredSourceId);
                if (source == null
                        || !assignment.configuredSourceFieldSignature.equals(
                        source.fieldSignature)
                        || !assignment.matchesConfiguredSource(
                        source.sourceId, source.fieldSignature)
                        || assignment.hasContainerTarget()
                        || assignment.referenceAlias()) {
                    throw new IllegalArgumentException(
                            "model assignment names an undeclared or "
                                    + "unsupported configured source in "
                                    + taskId + ": " + assignment.key);
                }
            }
            indexResponseProducerOccurrences(edgeBindings);
            this.exportsResponseHandoff = responseHandoff;
            // Gates travel with the task because the arm they enforce was
            // chosen by the solver for this replay and no other.  They are
            // carried unparsed: the concolic layer owns their admission, and
            // this side must not decide a gate is safe by rebuilding it.
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
        }

        private static final class SourceField {
            private final String sourceId;
            private final String fieldSignature;
            private final Set<String> requiredOutputFieldSignatures;

            private SourceField(String sourceId, String fieldSignature,
                                Set<String> requiredOutputFieldSignatures) {
                this.sourceId = sourceId;
                this.fieldSignature = fieldSignature;
                this.requiredOutputFieldSignatures =
                        Collections.unmodifiableSet(new LinkedHashSet<>(
                                requiredOutputFieldSignatures));
            }

            private static SourceField from(JsonObject row) {
                String sourceId = string(row, "sourceId");
                String field = string(row, "fieldSignature");
                Set<String> outputs = new LinkedHashSet<>();
                String output = string(row,
                        "requiredOutputFieldSignature");
                if (!output.isEmpty()) outputs.add(output);
                for (JsonElement element : array(row,
                        "requiredOutputFieldSignatures")) {
                    if (!element.isJsonPrimitive()
                            || safe(element.getAsString()).isEmpty()
                            || !outputs.add(element.getAsString())) {
                        throw new IllegalArgumentException(
                                "malformed configured symbolic source outputs");
                    }
                }
                if (!SymbolicSourceEvidence.DECLARATION_AUTHORITY.equals(
                        string(row, "authority"))
                        || sourceId.isEmpty() || field.isEmpty()
                        || outputs.isEmpty()
                        || (!output.isEmpty()
                        && row.has("requiredOutputFieldSignatures"))) {
                    throw new IllegalArgumentException(
                            "malformed configured symbolic source field");
                }
                return new SourceField(sourceId, field, outputs);
            }
        }

        private boolean publishesSelectedEdge(String outputPort,
                                              String edgeId) {
            Set<String> edges = outputCausalEdgesByPort.get(
                    safe(outputPort));
            return edges != null && edges.contains(safe(edgeId));
        }

        /** Seeds this task's source aliases at their declared output ports. */
        private void initializeConfiguredSourceAliases() {
            for (Map.Entry<String, String> output
                    : outputCellByPort.entrySet()) {
                for (SourceField source : sourceFields.values()) {
                    if (source.requiredOutputFieldSignatures.contains(
                            output.getValue())) {
                        addSourceAliasToOutput(output.getKey(),
                                new PlannedSourceAlias(taskId,
                                        source.sourceId, occurrenceId,
                                        source.fieldSignature));
                    }
                }
            }
        }

        /** Adds one identity to an output, refusing conflicting declarations. */
        private boolean addSourceAliasToOutput(
                String outputPort, PlannedSourceAlias alias) {
            if (alias == null || safe(outputPort).isEmpty()) return false;
            LinkedHashMap<String, PlannedSourceAlias> aliases =
                    sourceAliasesByOutputPort.computeIfAbsent(
                            safe(outputPort), ignored -> new LinkedHashMap<>());
            PlannedSourceAlias prior = aliases.putIfAbsent(alias.identity(),
                    alias);
            if (prior != null
                    && (!prior.sourceTaskId.equals(alias.sourceTaskId)
                    || !prior.fieldSignature.equals(alias.fieldSignature))) {
                throw new IllegalArgumentException(
                        "configured source identity has conflicting origins: "
                                + alias.identity());
            }
            return prior == null;
        }

        private boolean addSourceAliasToInput(
                String inputPort, PlannedSourceAlias alias) {
            if (alias == null || safe(inputPort).isEmpty()) return false;
            LinkedHashMap<String, PlannedSourceAlias> aliases =
                    sourceAliasesByInputPort.computeIfAbsent(
                            safe(inputPort), ignored -> new LinkedHashMap<>());
            PlannedSourceAlias prior = aliases.putIfAbsent(alias.identity(),
                    alias);
            if (prior != null
                    && (!prior.sourceTaskId.equals(alias.sourceTaskId)
                    || !prior.fieldSignature.equals(alias.fieldSignature))) {
                throw new IllegalArgumentException(
                        "configured source identity has conflicting inputs: "
                                + alias.identity());
            }
            return prior == null;
        }

        /** Configured source leaves whose value is carried by this output. */
        private List<PlannedSourceAlias> sourceAliasesForOutputPort(
                String outputPort) {
            Map<String, PlannedSourceAlias> aliases =
                    sourceAliasesByOutputPort.get(safe(outputPort));
            if (aliases == null || aliases.isEmpty()) {
                return Collections.emptyList();
            }
            return new ArrayList<>(aliases.values());
        }

        private PlannedMapAdmission mapAdmission(
                String accessFieldSignature) {
            return mapAdmissions.get(safe(accessFieldSignature));
        }

        private PlannedFieldAdmission fieldAdmission(
                String accessFieldSignature) {
            return fieldAdmissions.get(safe(accessFieldSignature));
        }

        /** Whether this hook is the exact declared access of one admission. */
        private boolean matchesPlannedInputAccess(
                String inputPort, String method, int unitIndex, Object owner,
                String fieldSignature, int occurrence) {
            if (safe(inputPort).isEmpty() || occurrence < 1) return false;
            DeclaredField field = FieldPathSpec.declaredField(fieldSignature);
            if (field == null) return false;
            for (SymbolizeAction action : declaredSymbolize) {
                if (inputPort.equals(action.symbol)
                        && action.matchesField(method, unitIndex, owner,
                        fieldSignature, field.name())
                        && action.acceptsDirectFieldOccurrence(occurrence)) {
                    return true;
                }
            }
            return false;
        }

        /** The declared handoff site of one communication port role. */
        private CommunicationHandoffSpec communicationHandoff(
                String portId, boolean exporting) {
            return communicationHandoffs.get(handoffKey(portId, exporting));
        }

        private CommunicationHandoffSpec manualCommunicationHandoff(
                String declaringClass, String fieldName, String descriptor,
                boolean exporting) {
            return manualCommunicationHandoffs.get(handoffCarrierKey(
                    declaringClass, fieldName, descriptor, exporting));
        }

        /**
         * Resolves each selected response input to its planner-authored
         * producer occurrence.  Several evidence rows may repeat that answer,
         * but two different occurrences are an ambiguous admission and are
         * rejected while loading the task.
         */
        private void indexResponseProducerOccurrences(JsonArray bindings) {
            for (String portId : responseAttachPortIds) {
                String producerOccurrence = "";
                for (JsonElement element : bindings) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!portId.equals(string(binding, "toInputPort"))) {
                        continue;
                    }
                    String candidate = string(binding, "fromOccurrenceId");
                    if (candidate.isEmpty()) continue;
                    if (!producerOccurrence.isEmpty()
                            && !producerOccurrence.equals(candidate)) {
                        throw new IllegalArgumentException(
                                "response handoff port has two producer "
                                        + "occurrences in " + taskId + ": "
                                        + portId);
                    }
                    producerOccurrence = candidate;
                }
                if (!producerOccurrence.isEmpty()) {
                    responseProducerOccurrenceByPort.put(portId,
                            producerOccurrence);
                }
            }
        }

        private static String handoffKey(String portId, boolean exporting) {
            return (exporting ? "EXPORT\n" : "ATTACH\n") + safe(portId);
        }

        private static String handoffCarrierKey(String declaringClass,
                                                String fieldName,
                                                String descriptor,
                                                boolean exporting) {
            return (exporting ? "EXPORT\n" : "ATTACH\n")
                    + safe(declaringClass) + "\n" + safe(fieldName) + "\n"
                    + safe(descriptor);
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
            // A named explicit fault is different: its alternate outcome is
            // the experiment input we must replay and merge, not incidental
            // producer control flow that may be projected away.
            return capturesOutputRelation && replayContract == null
                    && !hasExplicitFaultInput;
        }

        private void indexCapturePrerequisites(
                OutputClosureContract closure) {
            if (closure == null) return;
            boolean singletonRelation = closure.members().size() == 1;
            Set<String> symbolicPorts = new LinkedHashSet<>();
            Set<String> declaredPorts = new LinkedHashSet<>();
            for (SymbolizeAction action : symbolize) {
                // A bounded container action materializes a concrete
                // receiver/container snapshot.  It does not necessarily
                // publish a VM scalar symbol, and therefore cannot be a
                // prerequisite for capturing a scalar relation derived from
                // values subsequently read from that container.  The scalar
                // leaf actions below it remain ordinary prerequisites.
                if (!"BOUNDED_CONTAINER_STATE".equals(
                        action.symbolicDemand)) {
                    symbolicPorts.add(action.symbol);
                }
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
                boolean semanticExitSnapshot = singletonRelation
                        && member.captures().size() > 0;
                for (JsonElement element : member.captures()) {
                    if (!OutputCaptureSpec.MUTATION_STATE.equals(string(
                            element.getAsJsonObject(), "captureKind"))) {
                        semanticExitSnapshot = false;
                    }
                }
                if (semanticExitSnapshot) {
                    // A singleton mutation summary denotes the state at the
                    // mutator's normal-exit boundary.  It may legitimately
                    // observe only a subset of the planner's potential leaf
                    // inputs on this replay; the VM expression records the
                    // inputs that actually reached the boundary.
                    required.clear();
                } else if (!anchor.isEmpty()) {
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
                    JsonObject encodedCapture = element.getAsJsonObject();
                    String binding = string(encodedCapture,
                            "captureBindingId");
                    if (binding.isEmpty()
                            || capturePrerequisites.put(binding,
                            Collections.unmodifiableSet(
                                    new LinkedHashSet<>(required))) != null) {
                        throw new IllegalArgumentException(
                                "duplicate or missing output capture binding");
                    }
                    JsonObject recorded = recordedPrimitiveExpression(
                            encodedCapture);
                    if (required.isEmpty() && recorded != null) {
                        recordedPrimitiveOutputs.put(binding, recorded);
                    }
                }
            }
        }

        private static JsonObject recordedPrimitiveExpression(
                JsonObject capture) {
            if (!OutputCaptureSpec.FIELD_WRITE_STATE.equals(
                    string(capture, "captureKind"))) return null;
            String value = string(capture, "recordedPrimitiveValue");
            String descriptor = javaTypeDescriptor(string(capture,
                    "javaType"));
            if (!("I".equals(descriptor) || "J".equals(descriptor))
                    || !value.matches("-?(?:0|[1-9][0-9]*)")) {
                return null;
            }
            JsonObject expression = new JsonObject();
            expression.addProperty("_type", "ConstExpr");
            expression.addProperty("_java_type", descriptor);
            expression.addProperty("_exp", "Y_" + descriptor + "_"
                    + value);
            return expression;
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

        private JsonObject recordedPrimitiveOutput(
                OutputCaptureSpec request) {
            if (request == null || !request.capturesFieldWriteState()) {
                return null;
            }
            Set<String> required = capturePrerequisites.get(
                    request.captureBindingId());
            JsonObject expression = recordedPrimitiveOutputs.get(
                    request.captureBindingId());
            return required != null && required.isEmpty()
                    && expression != null ? expression.deepCopy() : null;
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

        /** Whether the frozen plan declares a policy for this branch site. */
        private boolean declaresBranch(String siteId) {
            return branchPolicies.containsKey(safe(siteId));
        }

        /** Whether this branch event is the target this task selected. */
        private boolean targetBranch(String siteId, int occurrence) {
            return !targetBranchSite.isEmpty()
                    && targetBranchSite.equals(safe(siteId))
                    && targetBranchOccurrence == occurrence;
        }

        /** Whether this task selected a target branch event at all. */
        private boolean declaresTargetBranch() {
            return !targetBranchSite.isEmpty();
        }

        /**
         * Whether this occurrence directly witnessed the selected failure
         * outcome, rather than merely deviating from its recorded seed path.
         *
         * <p>An upstream producer replay can legitimately change the target
         * task's seed outcome. Rejecting that activation as a seed mismatch
         * discards the strongest possible certificate: the exact receiver
         * occurrence consumed the replayed value and reached the planned
         * failure branch. Only the exact target site/occurrence and its
         * planner-authored required outcome receive this exemption.</p>
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

    }

    private static final class DeferredTerminal {
        private final String exitKind;
        private final String exceptionType;
        private final Object output;

        private DeferredTerminal(String exitKind, String exceptionType,
                                 Object output) {
            this.exitKind = exitKind;
            this.exceptionType = exceptionType;
            this.output = output;
        }
    }

    /**
     * The bounded campaign this JVM executes.
     *
     * <p>A campaign of one is the ordinary single-task run; nothing about it
     * is special-cased.  Every task keeps its own compatible-root counter, so
     * several tasks selected by different source/occurrence predicates can be
     * active on different threads at the same time.</p>
     */
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
         * <p>Positionally aligned with {@link #tasks}.  Together they turn
         * admission into what README {@code OCC-1} asks for: every compatible
         * root invocation is a candidate for the address, one at a time, until
         * one of them is the addressed occurrence.  A candidate that is not
         * ends by name and leaves the address open for the next; a further
         * candidate for an address already answered is ambiguity, and is also
         * published by name rather than quietly claiming the address twice.
         * </p>
         */
        private final boolean[] candidateLive;
        private final boolean[] occurrenceClaimed;
        /** Halt-status contribution of each task that has settled. */
        private final Map<String, Integer> settled = new LinkedHashMap<>();
        /** Exact Map versions published by selected producer output slots. */
        private final Map<String, Long> publishedMapVersions =
                new ConcurrentHashMap<>();
        /** Accepted scalar/reference producer versions by task/output port. */
        private final Map<String, Long> publishedFieldVersions =
                new ConcurrentHashMap<>();
        /** Accepted configured source roots by producer task/source id. */
        private final Map<String, String> publishedSourceSymbols =
                new ConcurrentHashMap<>();
        private boolean unansweredAddressesPublished;

        private Configuration(Path resultFile, List<RuntimeTask> tasks) {
            this.resultFile = resultFile;
            this.tasks = Collections.unmodifiableList(tasks);
            this.candidateLive = new boolean[tasks.size()];
            this.occurrenceClaimed = new boolean[tasks.size()];
            indexConfiguredSourceAliases();
            indexPlannedMapAdmissions();
            indexPlannedFieldAdmissions();
        }

        /**
         * Propagates configured source identities through the frozen selected
         * task graph.  This is metadata flow only: runtime values still move
         * exclusively through VM field-version admission or VM handoff.
         */
        private void indexConfiguredSourceAliases() {
            for (RuntimeTask task : tasks) {
                task.initializeConfiguredSourceAliases();
            }
            boolean changed;
            do {
                changed = false;
                for (RuntimeTask consumer : tasks) {
                    for (JsonElement element : consumer.edgeBindings) {
                        if (!element.isJsonObject()) continue;
                        JsonObject binding = element.getAsJsonObject();
                        String edgeId = string(binding, "edgeId");
                        String producerOccurrence = string(binding,
                                "fromOccurrenceId");
                        String outputPort = string(binding,
                                "fromOutputPort");
                        String inputPort = string(binding, "toInputPort");
                        if (edgeId.isEmpty() || producerOccurrence.isEmpty()
                                || outputPort.isEmpty()
                                || inputPort.isEmpty()) {
                            continue;
                        }
                        for (RuntimeTask producer : tasks) {
                            if (!producerOccurrence.equals(
                                    producer.occurrenceId)
                                    || !producer.publishesSelectedEdge(
                                    outputPort, edgeId)) {
                                continue;
                            }
                            for (PlannedSourceAlias alias
                                    : producer.sourceAliasesForOutputPort(
                                    outputPort)) {
                                changed |= consumer.addSourceAliasToInput(
                                        inputPort, alias);
                            }
                        }
                    }
                }
                for (RuntimeTask task : tasks) {
                    for (Map.Entry<String, Set<String>> output
                            : task.outputInputsByPort.entrySet()) {
                        for (String inputPort : output.getValue()) {
                            Map<String, PlannedSourceAlias> aliases =
                                    task.sourceAliasesByInputPort.get(
                                            inputPort);
                            if (aliases == null) continue;
                            for (PlannedSourceAlias alias
                                    : aliases.values()) {
                                changed |= task.addSourceAliasToOutput(
                                        output.getKey(), alias);
                            }
                        }
                    }
                }
            } while (changed);
        }

        /**
         * Resolves an upstream-bound Map input only through a producer member
         * selected by the same frozen edge id.  Occurrence and output port
         * alone are insufficient because one occurrence may be projected
         * into several phase tasks; the member's causal edge chooses the
         * phase without consulting runtime values.
         */
        private void indexPlannedMapAdmissions() {
            for (RuntimeTask consumer : tasks) {
                for (SharedCarrierRequest request
                        : consumer.sharedCarriers) {
                    if (!request.mapState || !request.accessOwnerBound()) {
                        continue;
                    }
                    Set<String> inputPorts = new LinkedHashSet<>();
                    Set<String> symbolicInputPorts = new LinkedHashSet<>();
                    for (SymbolizeAction action
                            : consumer.declaredSymbolize) {
                        if (request.matchesAccess(
                                action.accessFieldSignature)
                                && !action.symbol.isEmpty()) {
                            inputPorts.add(action.symbol);
                            if (action.symbolic) {
                                symbolicInputPorts.add(action.symbol);
                            }
                        }
                    }
                    if (inputPorts.isEmpty()) continue;

                    List<PlannedMapAdmission> selected = new ArrayList<>();
                    boolean hasUpstreamCandidate = false;
                    for (JsonElement element : consumer.edgeBindings) {
                        if (!element.isJsonObject()) continue;
                        JsonObject binding = element.getAsJsonObject();
                        String inputPort = string(binding, "toInputPort");
                        if (!inputPorts.contains(inputPort)
                                || !request.fieldKey().equals(
                                string(binding,
                                        RecordedReadFrom.EDGE_FIELD))) {
                            continue;
                        }
                        hasUpstreamCandidate = true;
                        String edgeId = string(binding, "edgeId");
                        String producerOccurrence = string(binding,
                                "fromOccurrenceId");
                        String outputPort = string(binding,
                                "fromOutputPort");
                        if (edgeId.isEmpty() || producerOccurrence.isEmpty()
                                || outputPort.isEmpty()) {
                            continue;
                        }
                        for (RuntimeTask producer : tasks) {
                            if (!producerOccurrence.equals(
                                    producer.occurrenceId)
                                    || !producer.publishesSelectedEdge(
                                    outputPort, edgeId)) {
                                continue;
                            }
                            selected.add(new PlannedMapAdmission(inputPort,
                                    edgeId, producer.taskId, outputPort, ""));
                        }
                    }
                    if (!hasUpstreamCandidate) continue;

                    // A concrete observation may carry broad candidate RF
                    // rows that are useful to the planner but are not part
                    // of this task's selected output relation.  Requiring a
                    // producer for such a row creates a local carrier/gap for
                    // an input the solver never requested.  A concrete Map
                    // is admitted only when an exact scheduled producer
                    // member owns its causal edge; an explicitly SYMBOLIC
                    // Map still fails closed when its producer is missing.
                    if (selected.isEmpty()
                            && symbolicInputPorts.isEmpty()) {
                        continue;
                    }

                    PlannedMapAdmission admission;
                    if (selected.size() == 1) {
                        admission = selected.get(0);
                    } else {
                        admission = new PlannedMapAdmission(
                                inputPorts.size() == 1
                                        ? inputPorts.iterator().next()
                                        : String.join(",", inputPorts),
                                "", "", "",
                                selected.isEmpty()
                                        ? "no campaign producer member owns "
                                        + "the selected Map input edge"
                                        : "multiple campaign producer members "
                                        + "own the selected Map input edge");
                    }
                    Set<String> accessFields = new LinkedHashSet<>();
                    for (SymbolizeAction action
                            : consumer.declaredSymbolize) {
                        if (inputPorts.contains(action.symbol)
                                && request.matchesAccess(
                                action.accessFieldSignature)
                                && !action.accessFieldSignature.isEmpty()) {
                            accessFields.add(action.accessFieldSignature);
                        }
                    }
                    if (accessFields.isEmpty()) {
                        throw new IllegalArgumentException(
                                "upstream Map input has no exact declared "
                                        + "access field in "
                                        + consumer.taskId);
                    }
                    for (String access : accessFields) {
                        PlannedMapAdmission prior =
                                consumer.mapAdmissions.put(access, admission);
                        if (prior != null) {
                            throw new IllegalArgumentException(
                                    "two Map carrier declarations resolve "
                                            + "the same access field in "
                                            + consumer.taskId + ": "
                                            + access);
                        }
                    }
                }
            }
        }

        /**
         * Resolves concrete scalar/reference inputs only when one scheduled
         * producer member owns the exact incoming edge.  Explicit symbolic
         * roots remain discovery variables and are never overwritten by a
         * recorded producer constant; broad concrete candidate edges with no
         * selected producer create no carrier and no gap.
         */
        private void indexPlannedFieldAdmissions() {
            for (RuntimeTask consumer : tasks) {
                for (SharedCarrierRequest request
                        : consumer.sharedCarriers) {
                    if (request.mapState || request.element
                            || !request.accessOwnerBound()) {
                        continue;
                    }
                    Set<String> inputPorts = new LinkedHashSet<>();
                    Map<String, String> accessByPort = new LinkedHashMap<>();
                    for (SymbolizeAction action
                            : consumer.declaredSymbolize) {
                        if (!action.symbolic
                                && request.matchesAccess(
                                action.accessFieldSignature)
                                && !action.symbol.isEmpty()
                                && !action.accessFieldSignature.isEmpty()) {
                            inputPorts.add(action.symbol);
                            accessByPort.put(action.symbol,
                                    action.accessFieldSignature);
                        }
                    }
                    if (inputPorts.isEmpty()) continue;

                    Map<String, PlannedFieldAdmission> selectedByKey =
                            new LinkedHashMap<>();
                    for (JsonElement element : consumer.edgeBindings) {
                        if (!element.isJsonObject()) continue;
                        JsonObject binding = element.getAsJsonObject();
                        String inputPort = string(binding, "toInputPort");
                        if (!inputPorts.contains(inputPort)
                                || !request.fieldKey().equals(string(binding,
                                RecordedReadFrom.EDGE_FIELD))) {
                            continue;
                        }
                        String edgeId = string(binding, "edgeId");
                        String producerOccurrence = string(binding,
                                "fromOccurrenceId");
                        String outputPort = string(binding,
                                "fromOutputPort");
                        if (edgeId.isEmpty() || producerOccurrence.isEmpty()
                                || outputPort.isEmpty()) {
                            continue;
                        }
                        for (RuntimeTask producer : tasks) {
                            if (!producerOccurrence.equals(
                                    producer.occurrenceId)
                                    || !producer.publishesSelectedEdge(
                                    outputPort, edgeId)) {
                                continue;
                            }
                            PlannedFieldAdmission admission =
                                    new PlannedFieldAdmission(inputPort,
                                            edgeId, producer.taskId,
                                            outputPort,
                                            producer.sourceAliasesForOutputPort(
                                                    outputPort), "");
                            selectedByKey.put(admission.registryKey() + "\n"
                                    + edgeId + "\n" + inputPort, admission);
                        }
                    }
                    if (selectedByKey.isEmpty()) continue;

                    PlannedFieldAdmission admission;
                    if (selectedByKey.size() == 1) {
                        admission = selectedByKey.values().iterator().next();
                    } else {
                        admission = new PlannedFieldAdmission(
                                String.join(",", inputPorts), "", "", "",
                                Collections.emptyList(),
                                "multiple campaign producer members own the "
                                        + "selected field input edge");
                    }
                    for (String inputPort : inputPorts) {
                        String access = accessByPort.get(inputPort);
                        if (access == null || access.isEmpty()) continue;
                        PlannedFieldAdmission prior =
                                consumer.fieldAdmissions.put(access,
                                        admission);
                        if (prior != null) {
                            throw new IllegalArgumentException(
                                    "two field carrier declarations resolve "
                                            + "the same access field in "
                                            + consumer.taskId + ": "
                                            + access);
                        }
                    }
                }
            }
        }

        private boolean selectedMapProducer(RuntimeTask producer,
                                            String outputPort) {
            if (producer == null || safe(outputPort).isEmpty()) return false;
            String key = producer.taskId + "\n" + safe(outputPort);
            for (RuntimeTask consumer : tasks) {
                for (PlannedMapAdmission admission
                        : consumer.mapAdmissions.values()) {
                    if (admission.valid()
                            && key.equals(admission.registryKey())) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean selectedFieldProducer(RuntimeTask producer,
                                              String outputPort) {
            if (producer == null || safe(outputPort).isEmpty()) return false;
            String key = producer.taskId + "\n" + safe(outputPort);
            for (RuntimeTask consumer : tasks) {
                for (PlannedFieldAdmission admission
                        : consumer.fieldAdmissions.values()) {
                    if (admission.valid()
                            && key.equals(admission.registryKey())) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean selectedSourceProducer(RuntimeTask producer,
                                               String sourceId) {
            if (producer == null || safe(sourceId).isEmpty()) return false;
            for (RuntimeTask consumer : tasks) {
                for (PlannedFieldAdmission admission
                        : consumer.fieldAdmissions.values()) {
                    if (!admission.valid()
                            || !producer.taskId.equals(
                            admission.producerTaskId)) {
                        continue;
                    }
                    for (PlannedSourceAlias alias
                            : admission.sourceAliases) {
                        if (producer.taskId.equals(alias.sourceTaskId)
                                && sourceId.equals(alias.sourceId)) {
                            return true;
                        }
                    }
                }
            }
            return false;
        }

        private synchronized String commitMapVersions(ActiveRegion active) {
            if (active == null || active.abandoned) return "";
            Map<String, Long> staged = active.stagedMapVersions();
            String failure = validateMapVersions(active, staged);
            if (!failure.isEmpty()) return failure;
            publishMapVersions(active, staged);
            return "";
        }

        private String validateMapVersions(ActiveRegion active,
                                           Map<String, Long> staged) {
            // Validate the whole candidate before making any port visible;
            // a multi-output producer must commit atomically.
            for (Map.Entry<String, Long> entry : staged.entrySet()) {
                if (!selectedMapProducer(active.activation,
                        entry.getKey())) continue;
                if (entry.getValue() == null || entry.getValue() <= 0L) {
                    return "selected Map producer returned no exact current "
                            + "version for " + safe(entry.getKey());
                }
                String key = active.activation.taskId + "\n"
                        + safe(entry.getKey());
                Long prior = publishedMapVersions.get(key);
                if (prior != null
                        && prior.longValue() != entry.getValue()) {
                    return "selected Map producer published conflicting "
                            + "versions " + prior + " and "
                            + entry.getValue() + " for "
                            + safe(entry.getKey());
                }
            }
            return "";
        }

        private void publishMapVersions(ActiveRegion active,
                                        Map<String, Long> staged) {
            for (Map.Entry<String, Long> entry : staged.entrySet()) {
                if (selectedMapProducer(active.activation,
                        entry.getKey())) {
                    publishedMapVersions.put(active.activation.taskId + "\n"
                            + safe(entry.getKey()), entry.getValue());
                }
            }
        }

        /**
         * Atomically publishes every selected shared-state version staged by
         * one accepted producer occurrence.  A mixed Map/field producer must
         * not expose one half of its state when validation of the other half
         * fails.
         */
        private synchronized String commitSelectedVersions(
                ActiveRegion active) {
            if (active == null || active.abandoned) return "";
            Map<String, Long> maps = active.stagedMapVersions();
            Map<String, Long> fields = active.stagedFieldVersions();
            Map<String, String> sources = active.stagedSourceSymbols();
            String failure = validateMapVersions(active, maps);
            if (!failure.isEmpty()) return failure;
            failure = validateFieldVersions(active, fields);
            if (!failure.isEmpty()) return failure;
            failure = validateSourceSymbols(active, sources);
            if (!failure.isEmpty()) return failure;
            publishMapVersions(active, maps);
            publishFieldVersions(active, fields);
            publishSourceSymbols(active, sources);
            return "";
        }

        private String validateSourceSymbols(
                ActiveRegion active, Map<String, String> staged) {
            for (RuntimeTask.SourceField source
                    : active.activation.sourceFields.values()) {
                if (!selectedSourceProducer(active.activation,
                        source.sourceId)) {
                    continue;
                }
                String raw = staged.get(source.sourceId);
                if (raw == null || raw.isEmpty()) {
                    return "selected configured source producer returned no "
                            + "exact VM symbol for " + source.sourceId;
                }
                String key = active.activation.taskId + "\n"
                        + source.sourceId;
                String prior = publishedSourceSymbols.get(key);
                if (prior != null && !prior.equals(raw)) {
                    return "selected configured source producer published "
                            + "conflicting VM symbols for " + source.sourceId;
                }
            }
            return "";
        }

        private void publishSourceSymbols(
                ActiveRegion active, Map<String, String> staged) {
            for (RuntimeTask.SourceField source
                    : active.activation.sourceFields.values()) {
                if (selectedSourceProducer(active.activation,
                        source.sourceId)) {
                    publishedSourceSymbols.put(active.activation.taskId
                            + "\n" + source.sourceId,
                            staged.get(source.sourceId));
                }
            }
        }

        private String publishedSourceSymbol(
                PlannedFieldAdmission admission, PlannedSourceAlias alias) {
            if (admission == null || !admission.valid() || alias == null) {
                return "";
            }
            return safe(publishedSourceSymbols.get(
                    alias.sourceTaskId + "\n" + alias.sourceId));
        }

        private Long publishedMapVersion(PlannedMapAdmission admission) {
            return admission == null || !admission.valid()
                    ? null : publishedMapVersions.get(
                    admission.registryKey());
        }

        private synchronized String commitFieldVersions(
                ActiveRegion active) {
            if (active == null || active.abandoned) return "";
            Map<String, Long> staged = active.stagedFieldVersions();
            String failure = validateFieldVersions(active, staged);
            if (!failure.isEmpty()) return failure;
            publishFieldVersions(active, staged);
            return "";
        }

        private String validateFieldVersions(ActiveRegion active,
                                             Map<String, Long> staged) {
            for (Map.Entry<String, Long> entry : staged.entrySet()) {
                if (!selectedFieldProducer(active.activation,
                        entry.getKey())) continue;
                if (entry.getValue() == null || entry.getValue() <= 0L) {
                    return "selected field producer returned no exact "
                            + "current version for " + safe(entry.getKey());
                }
                String key = active.activation.taskId + "\n"
                        + safe(entry.getKey());
                Long prior = publishedFieldVersions.get(key);
                if (prior != null && prior.longValue()
                        != entry.getValue().longValue()) {
                    return "selected field producer published conflicting "
                            + "versions " + prior + " and "
                            + entry.getValue() + " for "
                            + safe(entry.getKey());
                }
            }
            return "";
        }

        private void publishFieldVersions(ActiveRegion active,
                                          Map<String, Long> staged) {
            for (Map.Entry<String, Long> entry : staged.entrySet()) {
                if (selectedFieldProducer(active.activation,
                        entry.getKey())) {
                    publishedFieldVersions.put(active.activation.taskId
                            + "\n" + safe(entry.getKey()),
                            entry.getValue());
                }
            }
        }

        private Long publishedFieldVersion(PlannedFieldAdmission admission) {
            return admission == null || !admission.valid()
                    ? null : publishedFieldVersions.get(
                    admission.registryKey());
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
         * States every selected address that no activation answered, once
         * each, now that the run is over and "never registered in this run"
         * is decidable rather than a snapshot the same run can contradict.
         */
        private synchronized void publishUnansweredAddresses() {
            if (unansweredAddressesPublished) return;
            unansweredAddressesPublished = true;
            for (int index = 0; index < tasks.size(); index++) {
                if (occurrenceClaimed[index]) continue;
                RuntimeTask task = tasks.get(index);
                if (task.unaddressedCandidates == 0) continue;
                writeSkipped(task, task.rootContextSelector
                                .anchorSourceNeverExisted()
                                ? SKIP_ANCHOR_SOURCE_NEVER_EXISTED
                                : SKIP_OCCURRENCE_ANCHOR_UNMATCHED,
                        task.unansweredAddress());
            }
        }

        /** Records that a candidate was the occurrence and published it. */
        private synchronized void claimOccurrence(RuntimeTask task) {
            int index = tasks.indexOf(task);
            if (index < 0) return;
            candidateLive[index] = false;
            occurrenceClaimed[index] = true;
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
         * Resolves the caller's selected response ports to one exact producer
         * task in this campaign.  The occurrence comes from the existing
         * planner edge; the port proves that task owns the corresponding
         * response export.  No dynamic exchange or payload value is compared.
         */
        private ResponseProducerArm responseProducerArm(
                RuntimeTask caller, Set<String> requestedPorts) {
            if (caller == null || requestedPorts == null
                    || requestedPorts.isEmpty()) {
                return new ResponseProducerArm("",
                        Collections.<String>emptySet(), "no response attach");
            }
            String producerTaskId = "";
            RuntimeTask selectedProducer = null;
            Set<String> ports = new LinkedHashSet<>();
            for (String portId : requestedPorts) {
                if (!caller.responseAttachPortIds.contains(portId)) {
                    return new ResponseProducerArm("", ports,
                            "port " + portId
                                    + " is not a response attach of caller "
                                    + caller.taskId);
                }
                RuntimeTask matched = selectedResponseProducer(caller,
                        portId);
                if (matched == null) {
                    return new ResponseProducerArm("", ports,
                            "port " + portId
                                    + " has no unique campaign producer "
                                    + "task for caller "
                                    + caller.occurrenceId);
                }
                if (!producerTaskId.isEmpty()
                        && !producerTaskId.equals(matched.taskId)) {
                    return new ResponseProducerArm("", ports,
                            "one request would arm response ports from "
                                    + "multiple producer tasks");
                }
                producerTaskId = matched.taskId;
                selectedProducer = matched;
            }
            if (selectedProducer == null) {
                return new ResponseProducerArm("", ports,
                        "no selected response producer");
            }
            ports.addAll(selectedProducer.responseExportPortIds);
            return new ResponseProducerArm(producerTaskId, ports, "");
        }

        /**
         * Finds the unique frozen producer task for one caller response port.
         *
         * <p>The scheduler may store the same RPC binding on the producer
         * task rather than the consumer task.  Admission therefore searches
         * the whole bounded campaign, but still requires the exact four
         * endpoints authored by the runtime plan.  No correlation id,
         * payload value or call order is reconstructed here.</p>
         */
        private RuntimeTask selectedResponseProducer(RuntimeTask caller,
                                                     String portId) {
            String localOccurrence = safe(
                    caller.responseProducerOccurrenceByPort.get(portId));
            RuntimeTask matched = null;
            for (RuntimeTask candidate : tasks) {
                if (!candidate.responseExportPortIds.contains(portId)) {
                    continue;
                }
                boolean selected = !localOccurrence.isEmpty()
                        && localOccurrence.equals(candidate.occurrenceId);
                for (JsonElement element : candidate.edgeBindings) {
                    if (!element.isJsonObject()) continue;
                    JsonObject binding = element.getAsJsonObject();
                    if (!"RESPONSE".equalsIgnoreCase(
                            string(binding, "direction"))
                            || !candidate.occurrenceId.equals(
                            string(binding, "fromOccurrenceId"))
                            || !portId.equals(string(binding,
                            "fromOutputPort"))
                            || !caller.occurrenceId.equals(string(binding,
                            "toOccurrenceId"))
                            || !portId.equals(string(binding,
                            "toInputPort"))) {
                        continue;
                    }
                    selected = true;
                }
                if (!selected) continue;
                if (matched != null && matched != candidate) return null;
                matched = candidate;
            }
            return matched;
        }

        /**
         * Claims at most one open task for this root invocation.  Completed
         * and currently running tasks are skipped; another compatible task
         * may therefore run concurrently on another application thread, but
         * two task rows are never folded into one VM region.
         */
        private synchronized RuntimeTask select(String instrumentationSelector,
                                                String rootMethod,
                                                Object receiver,
                                                Object[] rootArguments) {
            String threadName = Thread.currentThread().getName();
            // A short-lived Runnable need not be registered as an alias
            // itself: an exact inherited async/request/RPC context can still
            // attribute its entry. An explicit receiver registration remains
            // stronger and may never be overridden by that context.
            SourceRef registeredReceiverSource =
                    RuntimeTraceContext.sourceFor(receiver);
            String requestApi = RuntimeTraceContext.current().requestApi;
            for (int index = 0; index < tasks.size(); index++) {
                RuntimeTask task = tasks.get(index);
                if (!task.instrumentationSelector.equals(
                        safe(instrumentationSelector))) continue;
                if (!compatibleRoot(task.rootMethod, rootMethod,
                        task.rootContextSelector, task.rootArgumentSelector,
                        receiver, rootArguments, threadName)) {
                    continue;
                }
                ResponseProducerArm responseArm = null;
                if (task.exportsResponseHandoff) {
                    responseArm = INBOUND_RESPONSE_PRODUCER_ARM.get();
                    if (responseArm == null
                            || !responseArm.authorizes(task)) {
                        // A response producer is an occurrence selected by its
                        // active caller, not the first compatible invocation
                        // of the same server method.
                        continue;
                    }
                }
                if (!task.rootContextSelector.matchesRequestApi(requestApi)) {
                    task.noteUnaddressedCandidate(
                            "matching root entered request API "
                                    + safe(requestApi) + " instead of "
                                    + task.rootContextSelector.requestApi);
                    continue;
                }
                // A receiver-scoped task already declares that its owner is
                // part of the occurrence address. Require exact source
                // attribution before opening a VM region or materializing an
                // input: either the receiver's own registration, or the exact
                // root context already resolved from its async/request/RPC
                // seed. Starting a source-less or wrong-source candidate and
                // checking only at terminal pollutes the workload-wide
                // symbolic session while contributing no usable result.
                if (task.rootContextSelector.receiverScoped
                        && registeredReceiverSource != null
                        && !RuntimeTraceContext.sameSourceIdentity(
                        task.sourceKey, registeredReceiverSource.key())) {
                    task.noteUnaddressedCandidate(
                            "matching root receiver belonged to "
                            + registeredReceiverSource.key() + " instead of "
                            + task.sourceKey);
                    continue;
                }
                if (occurrenceClaimed[index] || candidateLive[index]) continue;
                candidateLive[index] = true;
                if (responseArm != null) {
                    // One live request authorizes one producer occurrence.
                    // The response value itself is still propagated only by
                    // the VM handle exported later in that occurrence.
                    INBOUND_RESPONSE_PRODUCER_ARM.remove();
                }
                return task;
            }
            return null;
        }

        /**
         * Records one task's terminal outcome and returns the campaign's halt
         * status once every task has settled, or {@code -1} while any task can
         * still produce evidence.  The status is the worst contribution, so a
         * campaign of one reports exactly what that task reported.
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

        /**
         * The selected campaign, in plan order.  One id is the ordinary
         * single-task run; several are comma-separated.
         */
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

    /** Exact source authority available when the region entry hook runs. */
    private static SourceRef entrySource(Object receiver) {
        SourceRef registered = RuntimeTraceContext.sourceFor(receiver);
        return registered != null
                ? registered : RuntimeTraceContext.currentSource();
    }

    /** Test seam for receiver registration versus exact root-context priority. */
    static boolean exactEntrySourceForTests(Object receiver,
                                            String expectedSourceKey) {
        SourceRef source = entrySource(receiver);
        return source != null && safe(expectedSourceKey).equals(source.key());
    }

    /** Whether receiver-owned evidence permits the plan's exact source. */
    static boolean plannedEntrySourceForTests(Object receiver,
                                              String expectedSourceKey) {
        SourceRef registered = RuntimeTraceContext.sourceFor(receiver);
        return registered == null
                || RuntimeTraceContext.sameSourceIdentity(
                expectedSourceKey, registered.key());
    }


    /** Test seam listing the configured campaign, in plan order. */
    static List<String> campaignTaskIdsForTests() {
        List<String> ids = new ArrayList<>();
        for (RuntimeTask task : configuration().tasks) {
            ids.add(task.taskId);
        }
        return ids;
    }

    /** Test seam for the exact Map producer-state task/port/edge resolver. */
    static String plannedMapAdmissionForTests(
            String taskId, String accessFieldSignature) {
        RuntimeTask task = configuration().taskById(taskId);
        PlannedMapAdmission admission = task == null ? null
                : task.mapAdmission(accessFieldSignature);
        if (admission == null) return "NONE";
        if (!admission.valid()) return "REFUSED:" + admission.failure;
        return admission.producerTaskId + "\n"
                + admission.producerOutputPort + "\n"
                + admission.selectedEdgeId + "\n" + admission.inputPort;
    }

    /** Test seam for exact scalar/reference producer-state resolution. */
    static String plannedFieldAdmissionForTests(
            String taskId, String accessFieldSignature) {
        RuntimeTask task = configuration().taskById(taskId);
        PlannedFieldAdmission admission = task == null ? null
                : task.fieldAdmission(accessFieldSignature);
        if (admission == null) return "NONE";
        if (!admission.valid()) return "REFUSED:" + admission.failure;
        return admission.producerTaskId + "\n"
                + admission.producerOutputPort + "\n"
                + admission.selectedEdgeId + "\n" + admission.inputPort;
    }

    /** Test seam for configured nested-source propagation metadata. */
    static List<String> plannedFieldSourceAliasesForTests(
            String taskId, String accessFieldSignature) {
        RuntimeTask task = configuration().taskById(taskId);
        PlannedFieldAdmission admission = task == null ? null
                : task.fieldAdmission(accessFieldSignature);
        if (admission == null || !admission.valid()) {
            return Collections.emptyList();
        }
        List<String> result = new ArrayList<>();
        for (PlannedSourceAlias alias : admission.sourceAliases) {
            result.add(alias.sourceOccurrenceId + "\n" + alias.sourceId
                    + "\n" + alias.fieldSignature + "\n" + alias.symbol());
        }
        return result;
    }

    /** Test seam for the canonical raw name of one configured source. */
    static String configuredSourceSymbolForTests(
            String sourceOccurrenceId, String sourceId) {
        return configuredSourceSymbol(sourceOccurrenceId, sourceId);
    }

    /** Test seam for candidate-local staging versus accepted publication. */
    static String mapVersionLifecycleForTests(
            String producerTaskId, String outputPort, long versionId,
            boolean accepted) {
        Configuration configured = configuration();
        RuntimeTask producer = configured.taskById(producerTaskId);
        if (producer == null) return "NO_TASK";
        ActiveRegion candidate = new ActiveRegion(-1L, producer,
                new Object(), Thread.currentThread());
        String failure = candidate.stageMapVersion(outputPort, versionId);
        if (!failure.isEmpty()) return "REFUSED:" + failure;
        if (accepted) {
            failure = configured.commitMapVersions(candidate);
            if (!failure.isEmpty()) return "REFUSED:" + failure;
        }
        Long published = configured.publishedMapVersions.get(
                producer.taskId + "\n" + safe(outputPort));
        return published == null ? "ABSENT" : Long.toString(published);
    }

    /** Test seam for candidate-local scalar/reference version publication. */
    static String fieldVersionLifecycleForTests(
            String producerTaskId, String outputPort, long versionId,
            boolean accepted) {
        Configuration configured = configuration();
        RuntimeTask producer = configured.taskById(producerTaskId);
        if (producer == null) return "NO_TASK";
        ActiveRegion candidate = new ActiveRegion(-1L, producer,
                new Object(), Thread.currentThread());
        String failure = candidate.stageFieldVersion(outputPort, versionId);
        if (!failure.isEmpty()) return "REFUSED:" + failure;
        if (accepted) {
            failure = configured.commitFieldVersions(candidate);
            if (!failure.isEmpty()) return "REFUSED:" + failure;
        }
        Long published = configured.publishedFieldVersions.get(
                producer.taskId + "\n" + safe(outputPort));
        return published == null ? "ABSENT" : Long.toString(published);
    }

    /**
     * Test seam exercising the real access hook and terminal candidate gate
     * when an exact concrete field is read before its producer commits.
     */
    static String plannedFieldPrerequisiteMissForTests(
            String taskId, String method, int unitIndex, Object fieldOwner,
            String fieldSignature, String fieldName) {
        Configuration configured = configuration();
        RuntimeTask requested = configured.taskById(taskId);
        if (requested == null) return "NO_TASK";
        Object rootReceiver = new Object();
        RuntimeTask admitted = configured.select(
                requested.instrumentationSelector, requested.rootMethod,
                rootReceiver, new Object[0]);
        if (admitted == null) return "NOT_ADMITTED";
        beginLiveSelectedRegion();
        ActiveRegion active = new ActiveRegion(-1L, admitted, rootReceiver,
                Thread.currentThread());
        active.observedSourceKeys.add(admitted.sourceKey);
        ACTIVE.put(active.token, active);
        CURRENT_TOKEN.set(active.token);
        boolean pending;
        int gaps;
        boolean observed;
        boolean selectionRetained;
        boolean pendingAfterLaterAccess;
        boolean abandoned;
        boolean retried;
        try {
            materializeField(method, unitIndex, fieldOwner,
                    fieldSignature, fieldName);
            PlannedFieldAdmission admission = admitted.fieldAdmission(
                    fieldSignature);
            String inputPort = admission == null ? ""
                    : admission.inputPort;
            pending = active.plannedProducerPrerequisitePending(inputPort);
            gaps = active.sharedStateGaps.size();
            observed = active.observedInputSlots.contains(inputPort);
            selectionRetained = !active.accessOwnerCarrierSelections
                    .isEmpty();
            // Even if the producer commits now, occurrence 2 of this field
            // access is not occurrence 1 from the frozen input action.
            if (admission != null) {
                configured.publishedFieldVersions.put(
                        admission.registryKey(), 73L);
            }
            materializeField(method, unitIndex, fieldOwner,
                    fieldSignature, fieldName);
            pendingAfterLaterAccess =
                    active.plannedProducerPrerequisitePending(inputPort);
            judgeFinishedOccurrence(active);
            abandoned = active.abandoned;
        } finally {
            ACTIVE.remove(active.token, active);
            CURRENT_TOKEN.remove();
            if (!active.abandoned) endLiveSelectedRegion();
            configured.releaseCandidate(admitted);
        }
        RuntimeTask retry = configured.select(
                requested.instrumentationSelector, requested.rootMethod,
                new Object(), new Object[0]);
        retried = retry == requested;
        if (retry != null) configured.releaseCandidate(retry);
        return "pending=" + pending + ",gaps=" + gaps
                + ",observed=" + observed + ",selectionRetained="
                + selectionRetained + ",pendingAfterLaterAccess="
                + pendingAfterLaterAccess + ",abandoned=" + abandoned
                + ",retried=" + retried;
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
     * Test seam for the campaign completion gate.  Returns the campaign halt
     * status once every task has settled, otherwise -1.
     */
    static int settleCampaignTaskForTests(String taskId, int status) {
        return configuration().settle(taskId, status);
    }

    /**
     * Test seam for the candidate loop: one candidate ran and was not the
     * addressed occurrence, exactly as a finished activation reports it.
     */
    static void noteUnaddressedCandidateForTests(String taskId, String why) {
        for (RuntimeTask task : configuration().tasks) {
            if (task.taskId.equals(taskId)) {
                task.noteUnaddressedCandidate(why);
            }
        }
    }


    /** Test seam for the root-predicate half of a replay address. */
    static boolean compatibleRootForTests(
            JsonObject rootSelector, String selectedMethod,
            String actualMethod, Object receiver, Object[] rootArguments,
            String threadName) {
        return compatibleRoot(selectedMethod, actualMethod,
                RootContextSelector.from(rootSelector),
                RootArgumentSelector.from(rootSelector), receiver,
                rootArguments, threadName);
    }

    /**
     * Test seam for the causal-anchor half of a replay address: why the
     * candidate that observed this context is not the addressed occurrence,
     * or {@code ""} when it is.
     */
    static String unconfirmedAnchorForTests(JsonObject rootSelector,
                                            Set<String> attributedSourceKeys) {
        return RootContextSelector.from(rootSelector).unconfirmed(
                attributedSourceKeys);
    }

    private static final class EngineApi {
        private final Method openWorkloadSession;
        private final Method closeWorkloadSession;
        private final Method workloadSessionStatus;
        private final Method startRegion;
        private final Method symbolizeWithPrefix;
        private final Method symbolizeField;
        private final Method symbolizeExactField;
        private final Method observeExactPrimitiveField;
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
        private final HandoffApi handoff;
        private final PathConditionApi pathCondition;
        private final SharedStateApi sharedState;

        private EngineApi(Method openWorkloadSession,
                          Method closeWorkloadSession,
                          Method workloadSessionStatus,
                          Method startRegion,
                          Method symbolizeWithPrefix, Method symbolizeField,
                          Method symbolizeExactField,
                          Method observeExactPrimitiveField,
                          Method snapshotContainer,
                          Method trackContainer,
                          Method getExpression,
                          Method getFieldExpression,
                          Method finishRegion, Method getPathCondition,
                          Method pausePathCondition,
                          Method resumePathCondition,
                          Method markBranch, Method getBranchEvents,
                          Method cleanupEnd,
                          HandoffApi handoff,
                          PathConditionApi pathCondition,
                          SharedStateApi sharedState) {
            this.openWorkloadSession = openWorkloadSession;
            this.closeWorkloadSession = closeWorkloadSession;
            this.workloadSessionStatus = workloadSessionStatus;
            this.startRegion = startRegion;
            this.symbolizeWithPrefix = symbolizeWithPrefix;
            this.symbolizeField = symbolizeField;
            this.symbolizeExactField = symbolizeExactField;
            this.observeExactPrimitiveField = observeExactPrimitiveField;
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
            this.handoff = handoff;
            this.pathCondition = pathCondition;
            this.sharedState = sharedState;
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

        /**
         * Whether this JDK owns a workload-wide symbolic session.  Open and
         * close are one capability: a session that can be opened but never
         * closed would outlive the workload it belongs to.
         */
        private boolean workloadSessionAvailable() {
            return openWorkloadSession != null
                    && closeWorkloadSession != null;
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

        private void observeExactPrimitiveField(
                Object owner, String fieldSignature) throws Exception {
            DeclaredField field = FieldPathSpec.declaredField(
                    safe(fieldSignature));
            if (observeExactPrimitiveField == null) {
                throw new UnsupportedOperationException(
                        "custom concolic exact observed-field API is unavailable");
            }
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

        /**
         * Whether this JDK exposes the complete expression-handoff pair.
         * A partial set is treated as absent: a handoff that can export but
         * never attach is not a handoff.
         */
        private boolean expressionHandoffAvailable() {
            return handoff.available();
        }

        private long exportExpression(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            return handoff.export(owner, declaringClass, fieldName,
                    descriptor);
        }

        private long attachExpression(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long handle) throws Exception {
            return handoff.attach(owner, declaringClass, fieldName,
                    descriptor, handle);
        }

        private boolean pathConditionRangeAvailable() {
            return pathCondition.available();
        }

        private String pathConditionRange(int startIndex, int endIndex)
                throws Exception {
            return pathCondition.range(startIndex, endIndex);
        }

        private boolean sharedStateEvidenceAvailable() {
            return sharedState.available();
        }

        private boolean sharedMapEvidenceAvailable() {
            return sharedState.mapAvailable();
        }

        private boolean sharedMapProducerAdmissionAvailable() {
            return sharedState.mapProducerAdmissionAvailable();
        }

        private boolean sharedFieldProducerAdmissionAvailable() {
            return sharedState.fieldProducerAdmissionAvailable();
        }

        private long selectSharedMapCarrier(Object map) throws Exception {
            return sharedState.selectMap(map);
        }

        private String sharedMapVersions(Object map) throws Exception {
            return sharedState.mapVersions(map);
        }

        private long currentSharedMapVersion(Object map) throws Exception {
            return sharedState.currentMapVersion(map);
        }

        private long admitSharedMapVersion(Object map, long fieldVersionId,
                                           String selectedEdgeId)
                throws Exception {
            return sharedState.admitMapVersion(map, fieldVersionId,
                    selectedEdgeId);
        }

        private long currentSharedFieldVersion(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            return sharedState.currentFieldVersion(owner, declaringClass,
                    fieldName, descriptor);
        }

        private long admitSharedFieldVersion(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long fieldVersionId,
                String selectedEdgeId) throws Exception {
            return sharedState.admitFieldVersion(owner, declaringClass,
                    fieldName, descriptor, fieldVersionId, selectedEdgeId);
        }

        private long selectSharedFieldCarrier(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            return sharedState.selectField(owner, declaringClass, fieldName,
                    descriptor);
        }

        private long selectSharedElementCarrier(Object array, int index)
                throws Exception {
            return sharedState.selectElement(array, index);
        }

        private String sharedFieldVersions(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            return sharedState.fieldVersions(owner, declaringClass, fieldName,
                    descriptor);
        }

        private String sharedElementVersions(Object array, int index)
                throws Exception {
            return sharedState.elementVersions(array, index);
        }

        private String eventLedger() throws Exception {
            return sharedState.eventLedger();
        }

        private static EngineApi load() {
            Class<System> system = System.class;
            return new EngineApi(
                    method(system, "openWorkloadSession"),
                    method(system, "closeWorkloadSession"),
                    method(system, "getWorkloadSessionStatus"),
                    method(system, "startConcolicRegion", String.class, String.class),
                    method(system, "symbolize", Object.class, String.class),
                    method(system, "symbolizeField", Object.class,
                            String.class, String.class),
                    method(system, "symbolizeExactField", Object.class,
                            String.class, String.class, String.class,
                            String.class),
                    method(system, "observeExactPrimitiveField", Object.class,
                            String.class, String.class, String.class),
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
                    method(system, "endConcolic"),
                    HandoffApi.load(),
                    PathConditionApi.load(),
                    SharedStateApi.load());
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

    /**
     * Reflective view of the VM's symbolic expression handoff.
     *
     * <p>Only the current typed export/attach pair is bound.  Import,
     * explicit release and exchange-only compatibility APIs belonged to the
     * deleted second protocol.  A live handle plus the destination field is
     * the complete operation; session close owns broker reclamation.</p>
     */
    private static final class HandoffApi {
        private final Method export;
        private final Method attach;

        private HandoffApi(Method export, Method attach) {
            this.export = export;
            this.attach = attach;
        }

        private boolean available() {
            return export != null && attach != null;
        }

        private long export(Object owner, String declaringClass,
                            String fieldName, String descriptor)
                throws Exception {
            if (export == null) {
                throw new UnsupportedOperationException(
                        "custom concolic expression-export API is unavailable");
            }
            Object handle = export.invoke(null, owner, declaringClass,
                    fieldName, descriptor);
            return handle instanceof Number
                    ? ((Number) handle).longValue() : 0L;
        }

        private long attach(Object owner, String declaringClass,
                           String fieldName, String descriptor, long handle)
                throws Exception {
            if (attach == null) {
                throw new UnsupportedOperationException(
                        "custom concolic expression-attach API is unavailable");
            }
            Object answer = attach.invoke(null, owner, declaringClass,
                    fieldName, descriptor, handle);
            return answer instanceof Number
                    ? ((Number) answer).longValue()
                    : RpcExpressionHandoff.MALFORMED_RESULT;
        }

        private static HandoffApi load() {
            Class<System> system = System.class;
            return new HandoffApi(
                    EngineApi.method(system, "exportExpression", Object.class,
                            String.class, String.class, String.class),
                    EngineApi.method(system, "attachExpression", Object.class,
                            String.class, String.class, String.class,
                            long.class));
        }
    }

    /**
     * Reflective view of the VM's path-condition read-back.
     *
     * <p>Bound on its own, and deliberately not as one member of a group:
     * the whole path condition is no longer inlined in the region summary,
     * so this is the only way a selected branch witness reads back the
     * predicate its {@code conditionIndices} name.  Grouping it with natives
     * that no longer exist would report it unavailable and degrade branch
     * witness capture silently.</p>
     */
    private static final class PathConditionApi {
        private final Method range;

        private PathConditionApi(Method range) {
            this.range = range;
        }

        private boolean available() {
            return range != null;
        }

        private String range(int startIndex, int endIndex) throws Exception {
            return String.valueOf(range.invoke(null, startIndex, endIndex));
        }

        private static PathConditionApi load() {
            return new PathConditionApi(EngineApi.method(System.class,
                    "getConcolicPathConditionRange", int.class, int.class));
        }
    }

    /**
     * Reflective view of the VM's recorded shared-state evidence.
     *
     * <p>Selection and read-out are one capability, not five: a carrier that
     * can be selected but whose versions cannot be read back proves nothing,
     * and a ledger without carriers records nothing.  A partial set is
     * therefore treated as absent, exactly as the handoff pair is.</p>
     */
    private static final class SharedStateApi {
        private final Method selectField;
        private final Method selectElement;
        private final Method selectMap;
        private final Method fieldVersions;
        private final Method elementVersions;
        private final Method mapVersions;
        private final Method currentMapVersion;
        private final Method admitMapVersion;
        private final Method currentFieldVersion;
        private final Method admitFieldVersion;
        private final Method eventLedger;

        private SharedStateApi(Method selectField, Method selectElement,
                               Method selectMap, Method fieldVersions,
                               Method elementVersions, Method mapVersions,
                               Method currentMapVersion,
                               Method admitMapVersion,
                               Method currentFieldVersion,
                               Method admitFieldVersion,
                               Method eventLedger) {
            this.selectField = selectField;
            this.selectElement = selectElement;
            this.selectMap = selectMap;
            this.fieldVersions = fieldVersions;
            this.elementVersions = elementVersions;
            this.mapVersions = mapVersions;
            this.currentMapVersion = currentMapVersion;
            this.admitMapVersion = admitMapVersion;
            this.currentFieldVersion = currentFieldVersion;
            this.admitFieldVersion = admitFieldVersion;
            this.eventLedger = eventLedger;
        }

        private boolean available() {
            return selectField != null && selectElement != null
                    && fieldVersions != null && elementVersions != null
                    && eventLedger != null;
        }

        /**
         * Whether this JDK can both select a map carrier and read its
         * whole-state versions back.
         *
         * <p>Asked separately from {@link #available()} rather than folded
         * into it. Selecting a map and reading it back is one capability, so
         * a JDK holding half of the pair has none of it - but a JDK holding
         * neither still has the scalar half, and reporting the whole evidence
         * API absent for it would turn a missing map carrier into a missing
         * field carrier.</p>
         */
        private boolean mapAvailable() {
            return available() && selectMap != null && mapVersions != null;
        }

        private boolean mapProducerAdmissionAvailable() {
            return mapAvailable() && currentMapVersion != null
                    && admitMapVersion != null;
        }

        private boolean fieldProducerAdmissionAvailable() {
            return available() && currentFieldVersion != null
                    && admitFieldVersion != null;
        }

        private long selectField(Object owner, String declaringClass,
                                 String fieldName, String descriptor)
                throws Exception {
            Object version = selectField.invoke(null, owner, declaringClass,
                    fieldName, descriptor);
            return version instanceof Number
                    ? ((Number) version).longValue() : 0L;
        }

        private long selectElement(Object array, int index) throws Exception {
            Object version = selectElement.invoke(null, array, index);
            return version instanceof Number
                    ? ((Number) version).longValue() : 0L;
        }

        private long selectMap(Object map) throws Exception {
            Object version = selectMap.invoke(null, map);
            return version instanceof Number
                    ? ((Number) version).longValue() : 0L;
        }

        private String mapVersions(Object map) throws Exception {
            return String.valueOf(mapVersions.invoke(null, map));
        }

        private long currentMapVersion(Object map) throws Exception {
            Object answer = currentMapVersion.invoke(null, map);
            return answer instanceof Number
                    ? ((Number) answer).longValue() : Long.MIN_VALUE;
        }

        private long admitMapVersion(Object map, long fieldVersionId,
                                     String selectedEdgeId)
                throws Exception {
            Object answer = admitMapVersion.invoke(null, map,
                    fieldVersionId, selectedEdgeId);
            return answer instanceof Number
                    ? ((Number) answer).longValue() : Long.MIN_VALUE;
        }

        private long currentFieldVersion(
                Object owner, String declaringClass, String fieldName,
                String descriptor) throws Exception {
            Object answer = currentFieldVersion.invoke(null, owner,
                    declaringClass, fieldName, descriptor);
            return answer instanceof Number
                    ? ((Number) answer).longValue() : Long.MIN_VALUE;
        }

        private long admitFieldVersion(
                Object owner, String declaringClass, String fieldName,
                String descriptor, long fieldVersionId,
                String selectedEdgeId) throws Exception {
            Object answer = admitFieldVersion.invoke(null, owner,
                    declaringClass, fieldName, descriptor, fieldVersionId,
                    selectedEdgeId);
            return answer instanceof Number
                    ? ((Number) answer).longValue() : Long.MIN_VALUE;
        }

        private String fieldVersions(Object owner, String declaringClass,
                                     String fieldName, String descriptor)
                throws Exception {
            return String.valueOf(fieldVersions.invoke(null, owner,
                    declaringClass, fieldName, descriptor));
        }

        private String elementVersions(Object array, int index)
                throws Exception {
            return String.valueOf(elementVersions.invoke(null, array, index));
        }

        private String eventLedger() throws Exception {
            return String.valueOf(eventLedger.invoke(null));
        }

        private static SharedStateApi load() {
            Class<System> system = System.class;
            return new SharedStateApi(
                    EngineApi.method(system, "selectSharedFieldCarrier",
                            Object.class, String.class, String.class,
                            String.class),
                    EngineApi.method(system, "selectSharedElementCarrier",
                            Object.class, int.class),
                    EngineApi.method(system, "selectSharedMapCarrier",
                            Object.class),
                    EngineApi.method(system, "getSharedFieldVersions",
                            Object.class, String.class, String.class,
                            String.class),
                    EngineApi.method(system, "getSharedElementVersions",
                            Object.class, int.class),
                    EngineApi.method(system, "getSharedMapVersions",
                            Object.class),
                    EngineApi.method(system, "getCurrentSharedMapVersion",
                            Object.class),
                    EngineApi.method(system, "admitSharedMapVersion",
                            Object.class, long.class, String.class),
                    EngineApi.method(system, "getCurrentSharedFieldVersion",
                            Object.class, String.class, String.class,
                            String.class),
                    EngineApi.method(system, "admitSharedFieldVersion",
                            Object.class, String.class, String.class,
                            String.class, long.class, String.class),
                    EngineApi.method(system, "getEventLedger"));
        }
    }

}
