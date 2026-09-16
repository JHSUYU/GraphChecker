package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.plan.ConcolicScheduler;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonNull;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.plan.BranchPredicateAlgebra;
import edu.uva.liftlab.graphchecker.plan.BranchWitness;
import edu.uva.liftlab.graphchecker.smt.CanonicalJson;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.smt.VmExpressionIr;
import edu.uva.liftlab.graphchecker.plan.VmExpressionTable;
import edu.uva.liftlab.graphchecker.plan.SmtModelValueCodec;
import edu.uva.liftlab.graphchecker.plan.CommunicationHandoffSpec;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec;
import edu.uva.liftlab.graphchecker.plan.FieldPathSpec.DeclaredField;
import edu.uva.liftlab.graphchecker.plan.InputActionCatalog;
import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveBoxing;
import edu.uva.liftlab.graphchecker.plan.LoopBoundPolicy;
import edu.uva.liftlab.graphchecker.runtime.RowRuntime;
import edu.uva.liftlab.graphchecker.runtime.Interactions;
import edu.uva.liftlab.graphchecker.runtime.FieldAccess.MissingValue;
import edu.uva.liftlab.graphchecker.runtime.BranchObservation.BranchDecision;
import edu.uva.liftlab.graphchecker.runtime.BranchObservation.PreparedBranch;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.LoopBackedgeBudget;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.LoopBoundCut;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.ReplayLoopResourceCut;

import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.declaredInstanceField;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.exactFieldSignature;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.freshPrimitiveBox;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.instanceOfName;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.readExactField;
import static edu.uva.liftlab.graphchecker.runtime.FieldAccess.resolveFieldPathLeafOwner;
import static edu.uva.liftlab.graphchecker.runtime.ModelValues.isPrimitiveBox;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.RawSharedStateReadOut;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.nio.charset.StandardCharsets;
import java.util.UUID;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics;
import static edu.uva.liftlab.graphchecker.smt.JavaPrimitiveSmtSemantics.javaTypeDescriptor;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.array;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalLongInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.object;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.shallowCopy;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.beginLiveSelectedRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.beginSelectedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.haltWhenCampaignSettled;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.endSelectedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.endLiveSelectedRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.submitCompletedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.taskUnanswered;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.captureRecordedSharedStateRaw;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.contiguousConditionIndices;
import static edu.uva.liftlab.graphchecker.runtime.PathConditionWindow.vmEventConditionIndices;

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
    static final String ROOT_ARGUMENT_PREDICATE_KIND =
            "EXACT_RUNTIME_TYPE";
    static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    /** Shared with {@link LoopAccounting}, which mints a loop-root entry. */
    static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    static final String HALT_AFTER_SELECTED_RESULT_PROPERTY =
            "causynth.concolic.halt.after.selected.result";
    static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
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
    static final ThreadLocal<AccessorCallContext>
            CURRENT_ACCESSOR_CALL_CONTEXT = new ThreadLocal<>();
    /** Session this JVM opened for its workload, or zero when it opened none. */
    static volatile long workloadSessionId;
    /**
     * Content-addressed expression universe of the current VM workload
     * session.  Native expression ids are session-wide, so decoding them in
     * one store per region needlessly rebuilt the same propagated DAG at every
     * hop and every concurrent occurrence.
     */
    private static volatile VmExpressionTable.Store workloadExpressionStore =
            new VmExpressionTable.Store();
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
    static void beginBookkeeping() {
        pauseObservation();
    }

    /** Ends the muted subtree {@link #beginBookkeeping()} opened. */
    static void endBookkeeping() {
        resumeObservation();
    }

    /**
     * The innermost activation, or null while observation is muted: a hook
     * reached from GraphChecker's own bookkeeping accounts for nothing.
     */
    static ActiveRegion observingActiveRegion() {
        return OBSERVATION_PAUSE_DEPTH.get() > 0 ? null : activeRegion();
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
        // No index frame.  An accessor call context is woven by the
        // campaign and by nothing else, so a frame pushed here is a frame
        // the recording never stands on: the replay's execution index was
        // five frames deeper than the recorded one for the same occurrence
        // (planned 8 frames, ran 13), and every address below it drifted.
        // What the frame was for -- telling two reads of one accessor site
        // inside one occurrence apart -- is Identity.eventSiteIndex's job,
        // which counts per occurrence and per site in both passes alike.
        //
        // The context itself is NOT redundant with the recorder's
        // CausynthTraceRecorder.currentCallParentSiteMatches, and deleting
        // it would leave every accessor-constrained action unmatchable in
        // this pass.  That answer needs two recorder frames, and the
        // concolic weave pushes neither: an ActiveCall (pushed by
        // Hook.ENTER_METHOD -> CausynthTraceRecorder.enterMethod) and,
        // under it, the ActiveCallSite its parentSiteId names (pushed by
        // Hook.BEGIN_CALL -> beginCall).  Both hooks live in
        // HookCatalog.trace() only -- HookCatalog.concolic() binds neither
        // -- so in a replay ACTIVE_CALLS is empty and
        // currentCallParentSiteMatches returns false at its first test.
        // It could not answer even if the frames were woven: the hook this
        // context brackets is MATERIALIZE_FIELD, emitted BEFORE the
        // selected invoke in the CALLER's frame with the implementation
        // method's name (CausynthPipeline.instrumentConcolicAccessor-
        // CallContexts), so the accessor has not been entered yet, and on
        // hdfs-17960 six of the accessor-constrained actions name
        // <java.util.concurrent.atomic.AtomicInteger: int get()>, a JDK
        // body Soot's application scope cannot instrument at all.
        try {
            ActiveRegion active = activeRegion();
            String caller = safe(callerMethod);
            String site = safe(callSiteId);
            String callee = safe(declaredCallee);
            if (active == null || caller.isEmpty() || callUnitIndex < 0
                    || callee.isEmpty()
                    || !site.equals(SiteId.render(caller, callUnitIndex))) {
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
     * Opens the workload-wide symbolic session that outlives every individual
     * region in this JVM.
     *
     * @return an empty string on success, otherwise a named diagnostic
     */
    public static String openWorkloadSession() {
        // The session is open before the first region is admitted: an
        // export can cross a declared port before anything is selected, and
        // a row that is not published because nothing was live yet reads
        // afterwards as a site that never ran.
        RowRuntime.configure(configuration().resultFile);
        if (configuration().tasks.isEmpty()) {
            workloadExpressionStore = new VmExpressionTable.Store();
            return "";
        }
        ConcolicVmBroker api = engine();
        api.requireCurrentCapabilities();
        // The static slice's control-dependence answer, before any region can
        // store anything: a concrete store starts a location's log only in a
        // method the map names and only under one of that method's guard
        // decisions.  The artifact is this epoch's PLAN output and has been
        // required since closure v2, so a session that cannot read it is
        // refused by name rather than replaying as the pre-VM22 baseline in
        // which no concrete store is evidence at all.
        String guardedStores = GuardedStoreSites.install(api);
        if (!guardedStores.isEmpty()) {
            return guardedStores;
        }
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
            return "";
        }
        ConcolicVmBroker api = engine();
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
        workloadSessionId = 0L;
        workloadExpressionStore = new VmExpressionTable.Store();
        return "";
    }

    /**
     * Waits until every selected activation has durably closed its result
     * record or reported a write failure.
     *
     * <p>Called from outside this class: a launcher that owns no workload
     * session drives the durability barrier directly, the way the workload
     * checkouts call {@link #symbolizeConfiguredSourceField}.  The work
     * itself belongs to {@code ConcolicResultPublisher}; this is the driver
     * entry point that names it.</p>
     */
    public static void awaitSelectedResultPublications() {
        ConcolicResultPublisher.awaitSelectedResultPublications();
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
     * Admits the one planned occurrence this root invocation will execute.
     *
     * @return the started occurrence, or {@code null} when nothing was
     *         admitted or it could not be started
     */
    private static ActiveRegion admitRegion(
            ConcolicTaskPlan config, String rootHookGroupKey,
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
        return startSymbolicRegion(admitted, receiver);
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
    private static RuntimeTask selectTask(ConcolicTaskPlan config,
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
        // The "k past the bound" gap went with the ordinal: identity v3
        // addresses a loop body by the execution index it ran at, and
        // whether that index is reachable inside K_L is not a comparison of
        // two numbers.  The bound itself still cuts, below.
        if (admitted.claimLoopBoundCutMarker()) {
            taskUnanswered(admitted, "LOOP_OCCURRENCES_BOUNDED: the"
                    + " occurrence set of loop-body region "
                    + admitted.regionId + " is bounded at K_L="
                    + admitted.loopOccurrenceBudget + "; further iterations"
                    + " of " + admitted.occurrenceId + " run concretely"
                    + " without capture");
        }
        return true;
    }

    /** Starts one planned region occurrence. */
    private static ActiveRegion startSymbolicRegion(
            RuntimeTask admitted, Object receiver) {
        beginLiveSelectedRegion();
        ConcolicVmBroker api = engine();
        installEventClock(api);
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
                    admitted, receiver, Thread.currentThread());
            // A nested region starts with the symbolic state already carried
            // by its caller.  Its local branches must therefore open
            // immediately even when it mints no new task-local root.
            if (enclosing != null && enclosing.pathRecordingStarted) {
                active.pathRecordingStarted = true;
            }
            active.claimActivation();
            // Identity v2, minted from the lineage this activation entered
            // under.  The session it publishes into is this replay's own.
            edu.uva.liftlab.graphchecker.runtime.RowRuntime.configure(
                    configuration().resultFile);
            // The node it RAN on, by the planner's own attribution rule --
            // not the node the plan addressed, which is what an activation
            // is being checked against.
            SourceRef ranOn = RuntimeTraceContext.activationSource(receiver);
            active.d3Address = edu.uva.liftlab.graphchecker.runtime
                    .RowRuntime.beginActivation(active.token,
                            ranOn == null ? safe(admitted.sourceKey)
                                    : ranOn.key(),
                            admitted.regionId, admitted.taskId);
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
            // The execution-index frame this activation opened is now
            // addressable by the id every version and read the VM logs from
            // inside it carries, so a logged event can be given the frames
            // it stood on (FrameJournal).
            edu.uva.liftlab.graphchecker.runtime.RowRuntime.journalRegion(
                    active.vmRegionEnterEventId, active.d3Address);
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
            }
            prepare(active);
            api.resumePathCondition();
            pathConditionPaused = false;
            return active;
        } catch (Throwable throwable) {
            if (active != null) {
                ACTIVE.remove(active.token);
                // The index region is not unwound here either: the entry
                // hook that pushed it brackets this whole body, so its own
                // throw handler closes it (Hook.THROW_REGION_ENTRY ->
                // #closeRegionEntry).  Unwinding it here popped a region
                // this method never pushed.
                if (javaRegionPushed) {
                    popActiveRegion(active);
                }
                active.releaseActivation();
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
            taskUnanswered(admitted, "NOT_STARTED: engine start failed: "
                    + rootCause(throwable));
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
        RootMint.symbolizeReceiverFields(active, task, engine());
    }
    /**
     * Files the execution-index frame of one work start.
     *
     * <p>Woven at every {@code Thread.start}, executor submission and
     * fork-join fork inside the campaign's selected methods.  It pushes
     * nothing on the starter: the frame belongs to the work that was
     * started, which takes it when it runs.</p>
     */
    /**
     * Takes the execution-index frame filed for the work running here.
     *
     * <p>Woven at the entry of every functional method a start hands to a
     * thread ({@code WorkStartSites.entersWork}), in this pass and in the
     * recording alike.  The receiver IS the carrier the start was filed
     * under, so a pool worker -- handed its task by JDK code no weave
     * touches -- claims its own start frame at its own first instruction,
     * before the first send it makes.</p>
     */
    public static void claimStart(Object carrier) {
        try {
            RowRuntime.claimStart(carrier);
        } catch (Throwable unnamed) {
            // The work runs either way, and the hole is stated: the
            // occurrences this work publishes will be missing the
            // start-site frame that tells two siblings apart.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    carrier == null ? "" : carrier.getClass().getName(),
                    "the start frame filed for this work could not be "
                            + "claimed, so the occurrences it publishes carry "
                            + "no start-site frame in their execution index: "
                            + unnamed);
        }
    }

    /**
     * Enters the execution-index level of ONE application-scope method.
     *
     * <p>The replay's half of the one frame rule: the same hook, over the
     * same scope, that the recording weaves
     * ({@code CausynthTraceRecorder.enterMethodFrame}), from the one walk
     * ({@code CausynthPipeline.instrumentApplicationScope}).  The node is
     * not read here -- reading it costs a lock and this runs at every
     * application call -- because an event of a thread that names no node
     * of its own belongs to the node of the start that created its work.</p>
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterMethodFrame(String callSiteId) {
        return RowRuntime.enterFrame(safe(callSiteId));
    }

    /** Leaves the level {@link #enterMethodFrame} opened. */
    public static void exitMethodFrame(long token) {
        RowRuntime.exitFrame(token);
    }

    /** The exceptional edge of {@link #enterMethodFrame}. */
    public static void throwMethodFrame(long token, Throwable thrown) {
        RowRuntime.exitFrame(token);
    }

    public static void startWork(String startSiteId, Object carrier) {
        String site = safe(startSiteId);
        try {
            RowRuntime.startWork(site, carrier);
        } catch (Throwable unnamed) {
            // The start happens either way -- a hook may not turn it into a
            // failure -- and the hole is stated rather than swallowed: the
            // work this start created will publish an occurrence whose
            // index is missing the start-site frame.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    site, "the frame of this work start could not be filed, "
                            + "so the work it started carries no start-site "
                            + "frame in its execution index: " + unnamed);
        }
    }

    /**
     * Opens the execution-index region of one skeleton root the campaign did
     * not select.
     *
     * <p>The recording opens a region at EVERY skeleton root
     * (CausynthTraceRecorder.enterMethod), and an occurrence's execution
     * index is the frames from its scope root while every endpoint inside
     * it is indexed from its entry.  A replay that opened regions only at
     * its own task roots therefore stood on a different frame stack and
     * named a different occurrence for the same event -- the drift this
     * branch exists to remove.  So the same rule is woven here, over the
     * same skeleton file the recording read: frames and the occurrence
     * address, and no row -- an activation row belongs to the planned
     * occurrences alone.</p>
     */
    public static long enterRegionEntry(String regionId, String rootMethod,
                                        Object receiver) {
        // No claim here: a started work claims its start frame at its FIRST
        // identity event, which is the entry of the functional method the
        // start named (#claimStart) -- strictly earlier than any region
        // entry inside the work, and reached on a pool thread whose task
        // enters no region at all.
        long entry = TOKEN_COUNTER.incrementAndGet();
        int depth = edu.uva.liftlab.graphchecker.runtime.Identity.depth();
        // The other stack this entry is the one push of, read before the
        // push for the same reason the frame depth is.
        int regions = edu.uva.liftlab.graphchecker.runtime.Identity
                .regionDepth();
        // No frame here.  The level of this activation was opened by the
        // frame hook at this same entry (RowRuntime.enterFrame, woven at
        // every application-scope method in both passes), and it is
        // standing before the address is minted -- as it is in the
        // recording (CausynthTraceRecorder.enterMethod).
        String node = RuntimeTraceContext.activationSource(receiver).key();
        edu.uva.liftlab.graphchecker.runtime.Identity.occurrence(
                node, safe(regionId), true);
        REGION_ENTRIES.get().push(new RegionEntry(entry, depth, regions,
                safe(rootMethod)));
        return entry;
    }

    /** Closes the entry {@code entry} opened, and only that entry. */
    public static void exitRegionEntry(long entry) {
        closeRegionEntry(entry);
    }

    /** The exceptional edge of {@link #enterRegionEntry}. */
    public static void throwRegionEntry(long entry, Throwable throwable) {
        closeRegionEntry(entry);
    }

    /**
     * One open region entry: the token the workload frame holds, the index
     * depth it opened at, and the root it is the entry of.
     */
    private static final class RegionEntry {
        private final long token;
        private final int depthAtOpen;
        private final int regionsAtOpen;
        private final String rootMethod;

        private RegionEntry(long token, int depthAtOpen, int regionsAtOpen,
                            String rootMethod) {
            this.token = token;
            this.depthAtOpen = depthAtOpen;
            this.regionsAtOpen = regionsAtOpen;
            this.rootMethod = rootMethod;
        }
    }

    private static final ThreadLocal<Deque<RegionEntry>> REGION_ENTRIES =
            new ThreadLocal<Deque<RegionEntry>>() {
                @Override
                protected Deque<RegionEntry> initialValue() {
                    return new ArrayDeque<RegionEntry>();
                }
            };

    /**
     * Closes the entry the token owns: its region, its index frame, and
     * every entry that a missing exit left above it.
     *
     * <p>The token is a local of the workload frame the entry hook ran in,
     * so recursion holds a different one at every depth and several hooks
     * at ONE entry hold the same one -- which is what makes the push and
     * the pop pair without guessing at ownership.  An entry still open
     * above this one is an exit that did not run: its frames are dropped
     * here (the stack cannot stay deeper than the entry that is closing)
     * and the depth check below states it, fail-closed, because every row
     * published after a leaked frame is addressed by the wrong
     * occurrence.</p>
     */
    private static void closeRegionEntry(long entry) {
        if (entry <= 0L) return;
        Deque<RegionEntry> open = REGION_ENTRIES.get();
        RegionEntry mine = null;
        for (RegionEntry candidate : open) {
            if (candidate.token == entry) {
                mine = candidate;
                break;
            }
        }
        if (mine == null) return;
        while (!open.isEmpty()) {
            RegionEntry top = open.pop();
            RowRuntime.exitRegionIndex();
            if (top.token == entry) break;
        }
        if (open.isEmpty()) REGION_ENTRIES.remove();
        int depth = edu.uva.liftlab.graphchecker.runtime.Identity.depth();
        int regions = edu.uva.liftlab.graphchecker.runtime.Identity
                .regionDepth();
        // Both stacks of the execution index, under one rule: an activation
        // closes where it opened or it is refused.  The region stack needs
        // the same check as the frames because it decides which occurrence
        // an event belongs to and which frame its endpoints' site index is
        // measured from, so a region popped without a push does not break an
        // address -- it silently REBASES the next ones (see
        // #popActiveRegion).  One row, naming the stack that is off and what
        // it left standing.
        if (depth != mine.depthAtOpen) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .FRAME_UNBALANCED,
                    edu.uva.liftlab.graphchecker.contract.GapClass.BLOCKING,
                    mine.rootMethod,
                    "this activation closed at execution-index depth "
                            + depth + " and opened at " + mine.depthAtOpen
                            + "; the innermost frame left standing is "
                            + edu.uva.liftlab.graphchecker.runtime.Identity
                                    .innermostFrame());
        } else if (regions != mine.regionsAtOpen) {
            String standing = edu.uva.liftlab.graphchecker.runtime.Identity
                    .innermostRegion();
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .FRAME_UNBALANCED,
                    edu.uva.liftlab.graphchecker.contract.GapClass.BLOCKING,
                    mine.rootMethod,
                    "this activation closed with " + regions
                            + " region(s) open and opened with "
                            + mine.regionsAtOpen + "; "
                            + (regions > mine.regionsAtOpen
                            ? "a region it opened is left standing"
                            : "a region it did not open was closed under it")
                            + " and the site counts of every occurrence "
                            + "closed with it are gone, so the frames of "
                            + "what the enclosing occurrence runs next are "
                            + "renumbered; the innermost region now open is "
                            + (standing.isEmpty() ? "none" : standing));
        }
    }

    /** Instrumentation-facing root entry. */
    public static long enterRegionFrame(String instrumentationSelector,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
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
        // No index frame here.  The ENTRY owns it -- one per Java frame,
        // keyed by the token that frame holds (#enterRegionEntry) -- so a
        // second plan row at one entry cannot push a second frame and a
        // recursive entry cannot be mistaken for one.
        ActiveRegion active = admitRegion(config, group.key, rootMethod,
                receiver, rootArguments);
        long token = active == null ? 0L : active.token;
        frame.token = token;
        return token;
    }

    /**
     * Accounts for one attempted traversal of an instrumented normal CFG
     * backedge.
     */
    public static void checkLoopBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        LoopAccounting.checkBackedge(backedgeId, instrumentedMaxTraversals);
    }

    /**
     * Charges one loop body to the replay resource cap without consulting
     * the unroll bound.
     */
    public static void checkReplayLoopBody(
            String loopId, int instrumentedMaxTraversals) {
        LoopAccounting.checkReplayBody(loopId, instrumentedMaxTraversals);
    }

    /** Opens one dynamic invocation of a fixed-count loop. */
    public static void openLoopInvocation(String loopId) {
        LoopAccounting.openInvocation(loopId);
    }

    /** Closes the open dynamic invocation of a fixed-count loop. */
    public static void closeLoopInvocation(String loopId) {
        LoopAccounting.closeInvocation(loopId);
    }

    /**
     * Opens the lightweight enclosing call that addresses LOOP_BODY_ROOT
     * iterations.
     */
    public static long enterLoopRootInvocationFrame(
            String instrumentationSelector, String rootMethod,
            Object receiver, Object[] rootArguments) {
        return LoopAccounting.enterLoopRoot(instrumentationSelector,
                rootMethod, receiver, rootArguments);
    }

    /** Closes one enclosing LOOP_BODY_ROOT method call. */
    public static void exitLoopRootInvocationFrame(long token) {
        LoopAccounting.exitLoopRoot(token);
    }

    /** Exceptional counterpart of {@link #exitLoopRootInvocationFrame}. */
    public static void throwLoopRootInvocationFrame(
            long token, Throwable throwable) {
        LoopAccounting.exitLoopRoot(token);
    }

    /**
     * Whether the nearest matching outer call owns this loop task.
     *
     * <p>Stays here: {@code ConcolicTaskPlan} static-imports this name.</p>
     */
    static boolean enclosingLoopRootAdmits(RuntimeTask task) {
        return LoopAccounting.enclosingLoopRoot(task) != null;
    }

    /** Null-safe equality for either string naming one root hook. */
    static boolean sameHookIdentity(String left, String right) {
        return left == null ? right == null : left.equals(right);
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
    public static boolean materializeSymbolicBoolean(String name) {
        ActiveRegion active = activeRegion();
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


    /**
     * Tracks a declared region input's cell from this write onwards.
     *
     * <p>The VM retains a location BY VALUE: its version log begins at the
     * first symbolic value written to it, so a location nothing symbolic
     * has reached yet has no log and a store to it leaves no version
     * behind.  On hdfs-17960 that is why the snapshot counter's two
     * decrements published nothing and the anchor's read of the same cell
     * had no writer to join: the first symbolic value the cell ever saw was
     * the anchor's own placeholder mint, AFTER both writes.</p>
     *
     * <p>{@code System.observeExactPrimitiveField} attaches the value the
     * field holds right now as a concrete leaf -- a {@code ConExpression},
     * not a symbol, so no input is invented -- which is enough for the VM
     * to start versioning the location.  The Atomic RMW that follows is
     * then linearized by the VM's own summary
     * ({@code SymbolicAtomic::finish_method_helper} -&gt;
     * {@code publish_linearization}) and published as a version like any
     * other store's, carrying the expression the VM built.  The PLAN stage
     * decides WHICH write sites are observed; this states what the write
     * did.</p>
     */
    public static void observeDeclaredWriteSite(String siteId,
                                                String fieldSignature,
                                                Object receiver) {
        ActiveRegion active = activeRegion();
        if (active == null || receiver == null
                || safe(fieldSignature).isEmpty()) {
            return;
        }
        try {
            engine().observeExactPrimitiveField(receiver, fieldSignature);
            ensurePathRecordingStarted(active);
        } catch (Throwable failure) {
            // This call is what STARTS the location's version log, so a
            // loss here is not one row: every later read of the same cell
            // joins to no writer at all, which is the hdfs-17960 shape
            // this hook exists to close.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    firstNonBlank(safe(siteId), safe(fieldSignature)),
                    "this write site could not start the VM's version log"
                            + " for " + safe(fieldSignature) + ", so every"
                            + " later read of that location joins to no"
                            + " writer: " + rootCause(failure));
        }
    }

    /**
     * Called once per Java argument immediately after
     * {@link #enterRegionFrame}.
     */
    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        RootMint.symbolizeArgument(token, argumentIndex, value,
                primitiveValue);
    }

    /** Symbolizes one scheduler-selected helper-method argument in-region. */
    public static void symbolizeMethodArgument(String method,
                                               int argumentIndex,
                                               Object value,
                                               String primitiveValue) {
        RootMint.symbolizeMethodArgument(method, argumentIndex, value,
                primitiveValue);
    }

    /** Mints the declared root argument before Java control flow consumes it. */
    public static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        return RootMint.materializeArgument(token, argumentIndex,
                boxedOrReference, primitiveValue);
    }

    /** Mints a declared live-in at an exact in-region helper parameter. */
    public static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
        return RootMint.materializeMethodArgument(method, argumentIndex,
                boxedOrReference, primitiveValue);
    }

    /** Materializes a reference-valued live-in at its defining Jimple local. */
    public static Object materializeReference(String method, int unitIndex,
                                              String local, Object value) {
        return RootMint.materializeReference(method, unitIndex, local, value);
    }

    /** Materializes a primitive live-in and returns a fresh boxed value. */
    public static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        return RootMint.materializePrimitive(method, unitIndex, local,
                boxedValue);
    }

    /** Materializes the value one exact {@code getstatic} site consumes. */
    public static Object materializeStaticPrimitiveField(
            String method, int unitIndex, String fieldSignature,
            String fieldName, Object boxedValue) {
        return RootMint.materializeStaticPrimitiveField(method, unitIndex,
                fieldSignature, fieldName, boxedValue);
    }

    /** Materializes a declared heap field on its real owner. */
    public static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        RootMint.materializeField(method, unitIndex, owner, fieldSignature,
                fieldName);
    }

    /**
     * Mints one symbol for one entry of a declared mint site.
     *
     * <p>Called from outside this repository: the workload checkouts invoke
     * it directly from {@code org.apache.hadoop.ipc.CausynthSymbolicSource},
     * and it is the only symbolic root of HDFS-17960
     * (src/test/resources/external-callers.txt).</p>
     */
    public static boolean symbolizeConfiguredSourceField(
            String sourceId, Object owner, String fieldSignature) {
        return RootMint.configuredSource(sourceId, owner, fieldSignature);
    }

    /** Records a stable logical source a live occurrence just entered. */
    static void observeCausalSource(String sourceKey) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        if (sourceKey != null && !sourceKey.isEmpty()) {
            active.observedSourceKeys.add(sourceKey);
        }
    }


    /**
     * The name one unreadable propagated producer expression answers to.
     *
     * <p>A malformed or unreadable import is not "nothing propagated".  The
     * producer did deliver a value and it does carry an expression; what
     * failed is this replay's ability to read it.  Reading those two answers
     * as one is how a consumer whose producer expression could not be
     * imported acquired a <em>fresh unconstrained root</em> in its place:
     * {@link #carriesInputAuthority} was asked about a {@code null}, said
     * "nothing propagated", and the caller minted.  That manufactures a
     * freedom the recording never had, and a witness is free to exploit
     * it.</p>
     *
     * <p>So the failure travels as its own exception.  Every caller either
     * lets it reach a handler that files a named gap, or catches it here and
     * keeps the consumer's value concrete-and-flagged; none of them mints.
     * The row lands in {@code unresolvedInputs}, which {@code
     * the importer turns into {@code UNRESOLVED_INPUT} and
     * refuses the whole summary under, so the gap blocks rather than
     * decorates.</p>
     */
    static final String PROPAGATED_EXPRESSION_IMPORT_FAILED =
            "PROPAGATED_EXPRESSION_IMPORT_FAILED";

    /**
     * A propagated producer expression this replay could not import.
     *
     * <p>Its own type, so the three call sites that legitimately read "the VM
     * has no expression for this value" as {@code null} can keep doing that
     * for an unsymbolized read while still refusing an import that failed.
     * </p>
     */
    static final class PropagatedExpressionImportFailure
            extends IllegalStateException {
        private static final long serialVersionUID = 1L;

        PropagatedExpressionImportFailure(String detail, Throwable cause) {
            super(detail, cause);
        }
    }

    /** Package-visible for the import-refusal contract test. */
    static JsonElement engineExpression(String serialized) {
        ActiveRegion active = activeRegion();
        try {
            VmExpressionTable.Store store = active == null
                    ? workloadExpressionStore
                    : active.expressionStore;
            return store.importField(serialized, "expression");
        } catch (RuntimeException malformed) {
            String detail = PROPAGATED_EXPRESSION_IMPORT_FAILED
                    + ": producer=" + describeImportPayload(serialized)
                    + " occurrence=" + (active == null ? "<none>"
                    : safe(active.activation.occurrenceId))
                    + ": " + rootCause(malformed);
            throw new PropagatedExpressionImportFailure(detail, malformed);
        }
    }

    /** The outermost shape of a VM payload an import refused, for the row. */
    static String describeImportPayload(String serialized) {
        String value = safe(serialized);
        if (value.isEmpty()) return "<empty payload>";
        return value.length() <= 160 ? value
                : value.substring(0, 160) + "...(" + value.length() + " B)";
    }

    /** Resolves a native session DAG while retaining content sharing here. */
    static JsonObject decodeVmEnvelope(JsonObject envelope,
                                               ActiveRegion active) {
        VmExpressionTable.Store store = active == null
                ? workloadExpressionStore
                : active.expressionStore;
        return store.importEnvelope(envelope);
    }

    /** Result of one VM symbolic-expression export or attach. */
    private static final class HandoffResult {
        private final String stage;
        private final int status;
        private final long handle;
        /** The VM ledger events of a successful call, or {@code null}. */
        private final JsonObject record;

        private HandoffResult(String stage, int status, long handle,
                              JsonObject record) {
            this.stage = stage;
            this.status = status;
            this.handle = handle;
            this.record = record;
        }

        public boolean ok() {
            return status == ConcolicVmBroker.OK;
        }

        /** Named reason for a failure; empty for a successful call. */
        public String reason() {
            return ConcolicVmBroker.describe(status);
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
            return failed("EXPORT", ConcolicVmBroker.MISSING_METADATA, 0L);
        }
        ConcolicVmBroker api = engine();
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
            return failed("EXPORT", ConcolicVmBroker.INVOCATION_FAILED, 0L);
        }
        if (handle <= 0L) {
            return failed("EXPORT", exportStatus(handle), 0L);
        }
        JsonObject exported = new JsonObject();
        exported.addProperty("exportEventId", exportEvent[0]);
        return new HandoffResult("EXPORT", ConcolicVmBroker.OK, handle,
                exported);
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
            HandoffResult result = attach(owner, declaringClass,
                    fieldName, descriptor, carried.handle());
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
        // The producer site ran, so the message carries the value.  Which
        // occurrence produced it and which the plan addressed are what the
        // entry says about itself, not conditions on saying it.
        String producerTask = active == null ? UNPLANNED_ENDPOINT
                : active.activation.taskId;
        String producerOccurrence = active == null ? UNPLANNED_ENDPOINT
                : active.occurrenceId();
        return SymbolicMessageEnvelope.stage(portId, handle, producerTask,
                producerOccurrence);
    }

    /**
     * Stands in for an endpoint no plan named.
     *
     * <p>A leaf may be staged or taken under an identity the plan did not
     * select.  The value is still the value; the entry says plainly that its
     * endpoint was not planned rather than pretending to an occurrence.</p>
     */
    static final String UNPLANNED_ENDPOINT = "UNPLANNED";

    // ------------------------------------------------------------------
    // Declared communication ports
    // ------------------------------------------------------------------

    /**
     * Opens the frame around one message instance being serialized.
     *
     * <p>A declared port is one pair of bytecode sites, and a protocol sends
     * many unrelated values of that shape through it.  The frame is the thing
     * whose single construction builds one instance of the value the port
     * belongs to; leaves staged inside it are addressed within it, so two
     * groups of the same shape in one message stay apart.</p>
     */
    public static void pushOutboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.pushOutboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /** Closes the frame {@link #pushOutboundMessageFrame} opened. */
    public static void popOutboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.popOutboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /**
     * Opens the frame around one message instance being decoded.
     *
     * <p>The mirror of {@link #pushOutboundMessageFrame}: the receiver counts
     * its frames the way the sender counted theirs, so the k-th frame means
     * the same thing on both sides without either naming the other.</p>
     */
    public static void pushInboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.pushInboundFrame();
        } finally {
            endBookkeeping();
        }
    }

    /** Closes the frame {@link #pushInboundMessageFrame} opened. */
    public static void popInboundMessageFrame() {
        beginBookkeeping();
        try {
            SymbolicMessageEnvelope.popInboundFrame();
        } finally {
            endBookkeeping();
        }
    }

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
                && result.status != ConcolicVmBroker.NOT_SYMBOLIC) {
            return;
        }
        long handle = result.ok() ? result.handle() : 0L;
        if (!stageMessageExpression(site.portId(), handle)) {
            // The value crossed and the message could not carry its
            // expression: the row still states the endpoint, and the loss
            // is named rather than left as an export nobody can pair.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .DIAGNOSTIC, site.portId(),
                    "the communication leaf could not enter the message");
        }
        publishExportRow(site, carrier, field, descriptor, handle,
                result.ok() ? optionalLongInteger(result.record,
                        "exportEventId", 0L) : 0L);
    }

    /**
     * States one export as an endpoint the delivery can be paired to.
     *
     * <p>Every export, whether or not a region was live: the producer site
     * ran and the message carries the value, so the row exists and says
     * which occurrence produced it -- a degraded one when no live region
     * did, which is still an endpoint an arm can be keyed by (R-I1) and is
     * what the OUT side used to spell {@code UNPLANNED}.</p>
     */
    private static void publishExportRow(CommunicationHandoffSpec site,
                                         Object carrier, String field,
                                         String descriptor, long handle,
                                         long exportEventId) {
        beginBookkeeping();
        try {
            if (!RowRuntime.open()) return;
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            String nodeKey = view.source == null ? "" : view.source.key();
            ActiveRegion active = activeRegion();
            edu.uva.liftlab.graphchecker.contract.OccurrenceAddress
                    producer = active == null || active.d3Address == null
                    ? RowRuntime.degraded(nodeKey, site.portId())
                    : active.d3Address;
            if (active == null || active.d3Address == null) {
                RowRuntime.ambientActivation(producer);
            }
            JsonObject exported = null;
            String recordedValue = "";
            try {
                Field storage = declaredInstanceField(carrier, CARRIER_CLASS,
                        field, descriptor);
                if (storage != null) {
                    Object value = storage.get(carrier);
                    recordedValue = recordedScalar(value);
                    JsonElement expression = engineExpression(
                            engine().fieldExpression(carrier, CARRIER_CLASS,
                                    field, descriptor, value));
                    if (expression != null && expression.isJsonObject()) {
                        exported = expression.getAsJsonObject();
                    }
                }
            } catch (Throwable unreadable) {
                // The export happened; what it carried could not be read
                // back here, and the row says the endpoint without it.
                RowRuntime.gap(
                        edu.uva.liftlab.graphchecker.contract.GapKind
                                .UNSTATED_VALUE,
                        edu.uva.liftlab.graphchecker.contract.GapClass
                                .DIAGNOSTIC, site.portId(),
                        "the exported leaf's expression could not be read: "
                                + rootCause(unreadable));
            }
            RowRuntime.exported(producer, exportEventId, site.portId(),
                    handle, view.exchangeCorrelationId, attemptOf(view),
                    exported, descriptor, recordedValue);
        } catch (Throwable unstated) {
            // Publishing never ends a workload run -- and it never passes
            // in silence either: the value crossed the port and no row
            // states the endpoint, so nothing downstream can pair the
            // delivery to it.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, site.portId(),
                    "the export of this port published no endpoint row, so"
                            + " no delivery can be paired to it: "
                            + rootCause(unstated));
        } finally {
            endBookkeeping();
        }
    }



    /** The transport's retry number for this leg, or 0. */
    private static int attemptOf(RuntimeTraceContext.View view) {
        try {
            return Integer.parseInt(safe(view.exchangeAttemptId));
        } catch (NumberFormatException none) {
            return 0;
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
        if (site == null) {
            // A capture ran for a port no task of this campaign declares.
            // Rule 5: the run says so rather than returning in silence --
            // an attach that files nothing and an attach nobody planned
            // read identically from the corpus, and only one of them is a
            // coverage question.
            return;
        }
        if (carrier == null) {
            return;
        }
        Interactions.delivering(handle);
        try {
            attachDeliveredLeaf(site, carrier, field, descriptor, carried,
                    handle, leafCarried);
        } finally {
            Interactions.delivered();
        }
    }

    /**
     * Files one delivery on the occurrence it arrived in.
     *
     * <p>Split out so the delivery's own pairing evidence -- the VM handle
     * the producer staged -- is in force for the whole attach, including
     * the mint, without threading it through four signatures.</p>
     */
    private static void attachDeliveredLeaf(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor, SymbolicMessageEnvelope.Entry carried,
            long handle, boolean leafCarried) {
        if (!leafCarried || handle <= 0L) {
            // The delivery carried no producer expression, and the mint
            // happens anyway.  v_H is the consumer's boundary variable,
            // minted at the consumer's declared capture on the value that
            // ARRIVED; the envelope element only supplies e_p, which is one
            // member of H's family and not a condition of H existing.
            // Absent, the row says so and this delivery contributes no
            // family arm -- which is exactly right for a flip replay whose
            // job is the consumer's path under an assigned v_H, with the
            // producing node running concretely.
            //
            // Two ways for it to be absent, one fact for the consumer.  The
            // message may carry no element for this decode at all; or it may
            // carry one the producer staged with handle 0, which is what
            // exportCommunicationLeaf stages for a leaf the VM answered
            // NOT_SYMBOLIC -- "a concrete leaf is still a leaf the message
            // carried".  Either way there is no e_p and there is an arrived
            // value, so both take this path and the row states
            // elementAbsent.
            //
            // Refusing here left the assignment unapplied: on hdfs-17899
            // bug3 the flip replay of the target published zero handoff
            // rows, the fatal read still found the recorded key, and the
            // obligation ended REPLAY_NOT_ADMITTED with no primary case.
            mintArrivedCommunicationLeaf(site, carrier, field, descriptor);
            return;
        }
        attachDeclaredCommunicationExpression(carrier, CARRIER_CLASS, field,
                descriptor, carried, site);
    }

    /** The declared site of {@code portId} in this occurrence's plan. */
    /**
     * The declared site of {@code portId}, whoever is running.
     *
     * <p>Propagation is a property of the value, not of the activation that
     * happens to be on the stack.  The same conversion runs under several
     * region identities -- the one the plan selected for the port and the
     * ones that merely call the same helper -- and the leaf crossing the
     * wire is the same leaf in all of them.  Asking only the active task
     * meant a value arriving under an unselected identity was dropped, which
     * is how the four conversions that fill a DataNode's key map received no
     * producer expression at all.  Occurrences decide what gets published,
     * never whether a value propagates.</p>
     */
    private static CommunicationHandoffSpec communicationHandoffSite(
            String portId, boolean exporting) {
        if (safe(portId).isEmpty()) return null;
        ActiveRegion active = activeRegion();
        if (active != null) {
            CommunicationHandoffSpec declared =
                    active.activation.communicationHandoff(portId, exporting);
            if (declared != null) return declared;
        }
        for (ConcolicTaskPlan.RuntimeTask task : configuration().tasks) {
            CommunicationHandoffSpec declared =
                    task.communicationHandoff(portId, exporting);
            if (declared != null) return declared;
        }
        return null;
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
        if (site == null) return;
        ActiveRegion active = attachConsumerRegion(site);
        if (active == null) {
            // Same rule on the element-present side: the delivery happened.
            beginBookkeeping();
            try {
                mintAmbientHandoffLeaves(site, owner, declaringClass,
                        fieldName, descriptor);
            } finally {
                endBookkeeping();
            }
            return;
        }
        if (safe(producerTaskId).isEmpty()
                || safe(producerOccurrenceId).isEmpty()) {
            return;
        }
        long exportEvent = result.ok()
                ? optionalLongInteger(result.record, "exportEventId", 0L) : 0L;
        if (exportEvent <= 0L) {
            return;
        }
        // README RPC-1: the reference carries both endpoints of the edge.
        long attachEvent = result.ok()
                ? optionalLongInteger(result.record, "attachEventId", 0L) : 0L;
        if (attachEvent <= 0L) {
            return;
        }
        JsonElement expression;
        try {
            Field storage = declaredInstanceField(owner, declaringClass,
                    fieldName, descriptor);
            if (storage == null) {
                return;
            }
            Object value = storage.get(owner);
            ConcolicVmBroker api = engine();
            expression = RootMint.containerValue(value)
                    ? engineExpression(api.expression(value))
                    : engineExpression(api.fieldExpression(owner,
                    declaringClass, fieldName, descriptor, value));
        } catch (Throwable failure) {
            return;
        }
        if (expression == null || expression.isJsonNull()) {
            return;
        }
        Interactions.deliveringAt(attachEvent);
        mintHandoffVariable(active, site, exportEvent, attachEvent,
                expression, producerTaskId, producerOccurrenceId, owner,
                declaringClass, fieldName, descriptor, false);
    }

    /**
     * Mints v_H at a declared capture whose message carried no element.
     *
     * <p>The consumer's boundary variable is the consumer's, so it is minted
     * from what arrived: the row states {@code elementAbsent}, the delivered
     * value, and no producer -- and an assignment for this H answers the
     * mint exactly as it does when the element is there, because the answer
     * is written on the carrier leaf the receiving frame reads back.</p>
     */
    private static void mintArrivedCommunicationLeaf(
            CommunicationHandoffSpec site, Object carrier, String field,
            String descriptor) {
        beginBookkeeping();
        try {
            ActiveRegion active = attachConsumerRegion(site);
            if (active == null) {
                // The entry rule: the port is declared and the value
                // arrived, so v_H is minted on the ambient activation and
                // the row states the degraded occurrence it arrived in.
                mintAmbientHandoffLeaves(site, carrier, CARRIER_CLASS, field,
                        descriptor);
                return;
            }
                mintHandoffVariable(active, site, 0L, 0L, null, "", "", carrier,
                    CARRIER_CLASS, field, descriptor, true);
        } finally {
            endBookkeeping();
        }
    }

    /**
     * The activation this attach belongs to: the innermost live region whose
     * own plan declares this port as an IN site.
     *
     * <p>An attach happens inside whichever regions are live, and the
     * innermost of them is not always the one whose slice owns the attach
     * site: a loop-body region's activation spans one turn, and the same
     * decode site also runs outside the loop.  Filing on the innermost live
     * region regardless published the row under a region that never
     * declared the port -- on hdfs-17899 bug2, REGION.b7266d53, the caller,
     * carried both rows while REGION.16ba41cf, which declares them IN,
     * published none, so one attach was reported twice: unplanned there and
     * unreproduced here.</p>
     *
     * <p>When no live region declares it, the innermost live one still
     * carries the row: the replay is exact about what it did, and R5 then
     * says truthfully that a region ran a handoff nobody planned there.</p>
     */
    private static ActiveRegion attachConsumerRegion(
            CommunicationHandoffSpec site) {
        return site == null ? activeRegion()
                : declaringRegion(new Declares.Port(safe(site.portId())));
    }

    /**
     * THE ONE RULE: the innermost live region whose own plan declares this.
     *
     * <p>Three things are filed by it -- an attach's consumer region, the
     * consumer occurrence a handoff row states, and the occurrence a ROOT
     * MINT is addressed at -- and it was written twice and missing on the
     * third.  What it answers is the runtime counterpart of {@code
     * StaticScopeMap.holders}: regions nest, and the innermost one that
     * DECLARES the site is the one whose slice owns it, which is a fact of
     * the plan and not of which activation happened to be innermost when
     * the site ran.</p>
     *
     * <p>When no live region declares it the innermost live one still
     * carries the row: the replay is exact about what it did, and R5 then
     * says truthfully that a region ran something nobody planned there.</p>
     */
    static ActiveRegion declaringRegion(Declares what) {
        ActiveRegion innermost = activeRegion();
        if (what == null) return innermost;
        for (Long token : CURRENT_TOKENS.get()) {
            ActiveRegion candidate = ownerRegion(token);
            if (candidate != null && what.declaredBy(candidate)) {
                return candidate;
            }
        }
        return innermost;
    }

    /** What a region's plan is asked to declare. */
    interface Declares {
        boolean declaredBy(ActiveRegion region);

        /** A wire port, as an IN site. */
        final class Port implements Declares {
            private final String portId;

            Port(String portId) {
                this.portId = portId;
            }

            @Override
            public boolean declaredBy(ActiveRegion region) {
                return region.activation.communicationHandoff(portId, false)
                        != null;
            }
        }

        /**
         * A root the plan names as a symbolic input of this region.
         *
         * <p>Both spellings a root arrives under: a frozen SYMBOLIC action,
         * whose {@code symbol} IS the root id, and a CONFIGURED SOURCE,
         * whose publish phase names it.  One predicate, because "the region
         * that owns this mint" must not answer differently for the two.</p>
         */
        final class Root implements Declares {
            private final String rootId;

            Root(String rootId) {
                this.rootId = rootId;
            }

            @Override
            public boolean declaredBy(ActiveRegion region) {
                for (SymbolizeAction action : region.activation.symbolize) {
                    if (safe(action.symbol).equals(rootId)) return true;
                }
                for (ConfiguredSourcePhaseContract.Occurrence phase
                        : region.activation.configuredSourcePhases) {
                    if (phase.phase() == ConfiguredSourcePhaseContract
                            .Phase.PUBLISH
                            && safe(phase.sourceId()).equals(rootId)) {
                        return true;
                    }
                }
                return false;
            }
        }
    }

    /**
     * Mints the handoff variable v_H on the element this attach landed on.
     *
     * <p>The producer's expression {@code e_p} has just been attached and is
     * in {@code expression}; the element's shadow now becomes a fresh
     * variable instead, so the consumer's formula has a free variable at the
     * boundary rather than the producer's whole expression inlined into it.
     * That is what lets the two sides be explored independently and joined
     * offline at H: {@code e_p} travels on the row as one member of H's
     * family, never as a substitution.</p>
     *
     * <p>One variable per handoff occurrence per replay. A loop attaching the
     * same element on each turn gets one per turn, because k is part of H.
     * The mint is the configured-source mint -- same broker call, same model
     * answering, same "a mint the VM did not accept publishes no row" rule --
     * under a label that says handoff so nothing downstream mistakes it for a
     * configured source.</p>
     */
    private static void mintHandoffVariable(
            ActiveRegion active, CommunicationHandoffSpec site,
            long exportEvent, long attachEvent, JsonElement producerExpression,
            String producerTaskId, String producerOccurrenceId,
            Object owner, String declaringClass, String fieldName,
            String descriptor, boolean elementAbsent) {
        String portId = safe(site.portId());
        Field element = declaredInstanceField(owner, declaringClass,
                fieldName, descriptor);
        List<HandoffLeaf> leaves = handoffLeaves(portId, owner, element);
        if (leaves.isEmpty()) {
            // Never silence: a port whose delivered value exposes no
            // primitive leaf the VM can mint on has no v_H, and a row
            // without one names no occurrence two replays could be joined
            // at, so the loss is named -- in the same words the ambient
            // sibling uses, so one fact is stated once.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "the delivered element exposes no primitive leaf to mint"
                            + " a boundary variable on");
            return;
        }
        for (HandoffLeaf leaf : leaves) {
            mintHandoffLeaf(active, portId, exportEvent, attachEvent,
                    producerExpression, producerTaskId, producerOccurrenceId,
                    leaf, elementAbsent);
        }
    }

    /**
     * Mints v_H at one primitive leaf of one attach.
     *
     * <p>A port that crosses on a reference or an array is one attach and
     * several variables: {@code exportAllKeys} delivers a {@code BlockKey[]}
     * and what the consumer's formula reads are the leaves --
     * {@code [i].keyId}, {@code [i].expiryDate}.  One row per leaf, the leaf
     * in the element path, so each is its own handoff occurrence and R3
     * joins each to its own family.</p>
     */
    private static void mintHandoffLeaf(
            ActiveRegion active, String portId, long exportEvent,
            long attachEvent, JsonElement producerExpression,
            String producerTaskId, String producerOccurrenceId,
            HandoffLeaf leaf, boolean elementAbsent) {
        String elementPath = leaf.path;
        // H belongs to the occurrence the plan declares this IN site on,
        // not to whichever activation is live when the value arrives.  A
        // CALL_RETURN attach runs in the CALLER's frame -- the callee has
        // returned, so its activation has closed and published -- and the
        // row therefore rides on the caller while the handoff is the
        // callee's.  On hdfs-17899 bug2 that is REGION.16ba41cf's decode:
        // its rows landed on REGION.b7266d53, its caller, so one attach was
        // reported twice, unplanned there and unreproduced here.
        String consumerOccurrenceId = declaredConsumerOccurrence(portId,
                active);
        String phaseId = handoffMintKey(portId,
                consumerOccurrenceId,
                active.nextHandoffAttach(portId + "\n" + elementPath),
                elementPath);
        if (phaseId.isEmpty()) return;
        Object owner = leaf.owner;
        Field element = leaf.field;
        String declaringClass = element.getDeclaringClass().getName();
        String fieldName = element.getName();
        String descriptor = javaTypeDescriptor(
                element.getType().getTypeName());
        try {
            ConcolicVmBroker api = engine();
            String recordedValue = recordedScalar(element.get(owner));
            // Answering is the configured source's, by construction: a
            // handoff assignment IS a configured-source assignment whose
            // phase id is this one, so the solver emits one row shape and
            // the runtime runs one mechanism.
            // The identity is the leaf's indexed path; what the VM
            // resolves on the owner is the field signature itself.
            String signature = leaf.signature();
            // The phase id IS the identity of H -- it hashes the port, the
            // consumer occurrence, k and the element path -- so the answer
            // is looked up by it alone.  Naming the port and the element
            // path again beside it was a second spelling of the same fact,
            // and the solver emits the phase.
            // The endpoint first: an obligation answers an attach BY its
            // endpoint id (INTERACTION-ID), so the consumer endpoint has to
            // be named before the answer is written into the leaf.
            edu.uva.liftlab.graphchecker.contract.Endpoint consumer =
                    RowRuntime.nextEndpoint(active.d3Address, portId,
                            attemptOf(RuntimeTraceContext.current()));
            String answer = consumer == null ? ""
                    : edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .answer(consumer.id());
            if (!answer.isEmpty() && !RootMint.writeModeledField(owner, signature,
                    descriptor, answer)) {
                // The obligation's answer for this H was not written, so
                // this replay ran the value that arrived where the wave
                // asked for another one.  The same refusal a root mint
                // states (#applyFocusedRootAssignment), by name, instead of
                // an exception the catch below would have flattened into
                // "the mint failed".
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.ASSIGNMENT_UNPLANTED,
                        edu.uva.liftlab.graphchecker.contract.GapClass.BLOCKING, portId,
                        "the wave's answer for this handoff could not be"
                                + " written into " + signature);
                return;
            }
            api.symbolizeExactField(owner, signature,
                    handoffMintLabel(phaseId, portId));
            ensurePathRecordingStarted(active);
            JsonObject minted = exactSymbolOf(engineExpression(
                    api.fieldExpression(owner, declaringClass, fieldName,
                            descriptor, element.get(owner))));
            if (minted == null) {
                return;
            }
            publishAttachRow(consumer, portId,
                    optionalString(minted, "_exp"),
                    optionalString(minted, "_java_type"), recordedValue,
                    !answer.isEmpty(), answer);
        } catch (Throwable failure) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "the boundary variable of this attach was not minted, so"
                            + " the delivery names no occurrence two replays"
                            + " could be joined at: " + rootCause(failure));
        }
    }

    /**
     * The identity this attach mints v_H under, and the key an obligation's
     * answer for it is looked up by.
     *
     * <p>{@code (port, consumer occurrence, k-th attach of this element,
     * element path)} and nothing else, so the same attach in two replays
     * mints the same variable and an answer written for one is found by the
     * other.  Empty when any part is missing, which is an attach no replay
     * could be joined at.</p>
     *
     * <p>// D2: keyed by the consumer Endpoint and published as an AttachRow
     * by SessionPublisher (M2).</p>
     */
    private static final String HANDOFF_MINT_PREFIX = "HANDOFF_PHASE.";

    private static String handoffMintKey(String portId,
                                         String consumerAddress,
                                         int attachOrdinal,
                                         String elementPath) {
        if (safe(portId).isEmpty() || safe(consumerAddress).isEmpty()
                || safe(elementPath).isEmpty() || attachOrdinal < 1) {
            return "";
        }
        String identity = portId + "\n" + consumerAddress + "\n"
                + attachOrdinal + "\n" + elementPath;
        return HANDOFF_MINT_PREFIX + UUID.nameUUIDFromBytes(
                identity.getBytes(StandardCharsets.UTF_8));
    }

    /** The mint label of one key and port, for the caller that has both. */
    static String handoffMintLabelFor(String mintKey, String portId) {
        return handoffMintLabel(mintKey, portId);
    }

    /**
     * The label the VM mints v_H under.
     *
     * <p>Deliberately not the configured source's {@code SRC.} label: a
     * handoff root and a configured-source root are told apart by name
     * alone, because the importer recognises a configured-source mint by the
     * {@code _field_SRC.<label>_} marker inside the root it reads back.</p>
     */
    private static String handoffMintLabel(String mintKey, String portId) {
        return "HOFF." + ArtifactIO.sha256(mintKey + "\n"
                + safe(portId));
    }

    /**
     * The occurrence this port's IN site is declared on.
     *
     * <p>The plan names it, so it is the same string on both sides and in
     * every replay; the live activation is whatever the value happened to
     * arrive under.  Falls back to the carrying activation when no task
     * declares the port, which is the case R5 names UNPLANNED_HANDOFF.</p>
     */
    private static String declaredConsumerOccurrence(String portId,
                                                     ActiveRegion carrying) {
        // The live activation that declares it, innermost first.  Several
        // occurrences of one region declare the same port -- bug2's
        // REGION.1f6914ec has five -- so "the first task in the plan that
        // declares this port" names one of them for every attach: in lane
        // B2e every handoff row came out with consumerOccurrenceId
        // REGION.1f6914ec…#5 and ONE handoff phase id, which is one
        // variable for what are several handoffs, and left the occurrence
        // that did attach reported as not having reproduced its port.
        ActiveRegion declaring = declaringRegion(new Declares.Port(portId));
        // None live declares it: the attach is where it is, and the row
        // says so rather than borrowing another occurrence's address.  A
        // CALL_RETURN attach whose callee has already closed and published
        // lands here, and R5 then reports it against the carrier.
        return declaring == null ? carrying.activation.occurrenceId
                : declaring.activation.occurrenceId;
    }

    /**
     * States one delivered v_H as the consumer endpoint of an interaction.
     *
     * <p>The row carries both endpoints: this consumer, and the producer
     * the run paired it with -- by the VM handle the producer staged, which
     * is the pairing evidence the run itself recorded.  A delivery nothing
     * paired says so rather than naming a producer it guessed.</p>
     */
    private static void publishAttachRow(
            edu.uva.liftlab.graphchecker.contract.Endpoint consumer,
            String portId, String symbol, String javaType, String arrival,
            boolean answered, String answeredValue) {
        if (consumer == null || !RowRuntime.open()) return;
        try {
            RuntimeTraceContext.View view = RuntimeTraceContext.current();
            RowRuntime.attachedAt(consumer, Interactions.deliverySeq(), portId,
                    Interactions.deliveryHandle(),
                    view.exchangeCorrelationId, symbol, javaType, arrival,
                    answered, answeredValue);
        } catch (Throwable unstated) {
            // The same rule as the export side: the delivery happened, and
            // a consumer endpoint nothing published is a handoff no arm can
            // be keyed by.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                    "this delivery published no consumer endpoint row, so no"
                            + " arm can be keyed by it: "
                            + rootCause(unstated));
        }
    }

    /**
     * Mints v_H at a declared port that arrived outside every selected
     * occurrence -- the entry rule.
     *
     * <p>Every declared port mints on arrival, whatever is selected: the
     * value crossed the boundary and the consumer's formula needs a free
     * variable there, and which occurrence it happened in is what the row
     * says about itself rather than a condition on saying it.  Selection
     * decides only whose paths are explored (REPORT-ENTRY §2).  Path
     * recording is deliberately NOT started: an unselected activation
     * records no path, which is precisely what not selecting it means.</p>
     */
    private static void mintAmbientHandoffLeaves(
            CommunicationHandoffSpec site, Object owner,
            String declaringClass, String fieldName, String descriptor) {
        String portId = safe(site.portId());
        if (!RowRuntime.open()) return;
        RuntimeTraceContext.View view = RuntimeTraceContext.current();
        String nodeKey = view.source == null ? "" : view.source.key();
        edu.uva.liftlab.graphchecker.contract.OccurrenceAddress consumer =
                RowRuntime.degraded(nodeKey, portId);
        if (consumer == null) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .BLOCKING, portId,
                    "a declared port arrived on a thread naming no node, so"
                            + " the delivery has no consumer address");
            return;
        }
        RowRuntime.ambientActivation(consumer);
        Field element = declaredInstanceField(owner, declaringClass,
                fieldName, descriptor);
        List<HandoffLeaf> leaves = handoffLeaves(portId, owner, element);
        if (leaves.isEmpty()) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .UNSTATED_VALUE,
                    edu.uva.liftlab.graphchecker.contract.GapClass
                            .DIAGNOSTIC, portId,
                    "the delivered element exposes no primitive leaf to mint"
                            + " a boundary variable on");
            return;
        }
        for (HandoffLeaf leaf : leaves) {
            try {
                ConcolicVmBroker api = engine();
                Field field = leaf.field;
                String recordedValue = recordedScalar(field.get(leaf.owner));
                String mintKey = handoffMintKey(portId, consumer.render(),
                        1, leaf.path);
                api.symbolizeExactField(leaf.owner, leaf.signature(),
                        handoffMintLabelFor(mintKey, portId));
                JsonObject minted = exactSymbolOf(engineExpression(
                        api.fieldExpression(leaf.owner,
                                field.getDeclaringClass().getName(),
                                field.getName(), javaTypeDescriptor(
                                        field.getType().getTypeName()),
                                field.get(leaf.owner))));
                publishAttachRow(RowRuntime.nextEndpoint(consumer, portId,
                                attemptOf(view)), portId,
                        minted == null ? "" : optionalString(minted, "_exp"),
                        minted == null ? ""
                                : optionalString(minted, "_java_type"),
                        recordedValue, false, "");
            } catch (Throwable failure) {
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                                .UNSTATED_VALUE,
                        edu.uva.liftlab.graphchecker.contract.GapClass
                                .DIAGNOSTIC, portId,
                        "the entry-rule mint failed at " + portId + ": "
                                + rootCause(failure));
            }
        }
    }

    /** One primitive leaf of one attach, and how the row names it. */
    private static final class HandoffLeaf {
        private final Object owner;
        private final Field field;
        /** How the row names this leaf: indexed, so two elements differ. */
        private final String path;

        private HandoffLeaf(Object owner, Field field, String path) {
            this.owner = owner;
            this.field = field;
            this.path = path;
        }

        /** What the VM resolves on the owner: the bare field signature. */
        private String signature() {
            return exactFieldSignature(field);
        }
    }

    /** How many leaves of one attach are minted before the rest is named. */
    private static final int HANDOFF_LEAF_LIMIT = 64;

    /**
     * The primitive leaves one attach delivered.
     *
     * <p>A primitive destination is one leaf, itself.  A reference or array
     * destination is the leaves reachable through it that the VM can mint
     * on: each element's declared primitive instance fields, index-qualified
     * so two elements are two handoff occurrences.  An array of primitives
     * has no field to address and yields none, which the caller names rather
     * than passes over.</p>
     *
     * <p>The cap is named too.  A leaf above it is a boundary variable the
     * run never minted, so no later stage can join that half of the
     * delivery at all -- and an unnamed cap reads from the corpus exactly
     * like a delivery that carried nothing there.  The row states the port,
     * the cap, and what was left out, counted exactly and without a second
     * walk: the delivered array elements never visited, and the declared
     * primitive fields of the elements that were.</p>
     */
    private static List<HandoffLeaf> handoffLeaves(String portId,
                                                   Object owner,
                                                   Field element) {
        List<HandoffLeaf> leaves = new ArrayList<>();
        if (element == null) return leaves;
        if (element.getType().isPrimitive()) {
            leaves.add(new HandoffLeaf(owner, element,
                    exactFieldSignature(element)));
            return leaves;
        }
        final Object value;
        try {
            value = element.get(owner);
        } catch (Throwable unreadable) {
            return leaves;
        }
        if (value == null) return leaves;
        int droppedFields = 0;
        if (value.getClass().isArray()) {
            int length = java.lang.reflect.Array.getLength(value);
            int index = 0;
            for (; index < length
                    && leaves.size() < HANDOFF_LEAF_LIMIT; index++) {
                Object item = java.lang.reflect.Array.get(value, index);
                if (item == null) continue;
                droppedFields += addPrimitiveLeaves(item, "[" + index + "]",
                        leaves);
            }
            noteTruncatedHandoff(portId, leaves.size(), length - index,
                    droppedFields);
            return leaves;
        }
        droppedFields = addPrimitiveLeaves(value, "", leaves);
        noteTruncatedHandoff(portId, leaves.size(), 0, droppedFields);
        return leaves;
    }

    /** Names one delivery whose boundary variables did not fit the cap. */
    private static void noteTruncatedHandoff(String portId, int minted,
                                             int droppedElements,
                                             int droppedFields) {
        if (droppedElements <= 0 && droppedFields <= 0) return;
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.BOUND_INSUFFICIENT,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, portId,
                "this delivery minted " + minted + " boundary variable(s)"
                        + " and stopped at the " + HANDOFF_LEAF_LIMIT
                        + "-leaf cap, leaving " + droppedElements
                        + " delivered element(s) and " + droppedFields
                        + " declared primitive field(s) with none, so no"
                        + " later stage can join a handoff at them");
    }

    /** @return how many qualifying leaves the cap left out */
    private static int addPrimitiveLeaves(Object owner, String prefix,
                                          List<HandoffLeaf> leaves) {
        // Only the application's own objects.  An array of primitives boxes
        // each element on the way out of reflection, and java.lang.Integer's
        // own private "value" is not a leaf the workload addresses -- it is
        // the box the array element already is, and minting into it would
        // publish a handoff at a field no decode ever reads.
        if (owner.getClass().getName().startsWith("java.")) return 0;
        int dropped = 0;
        for (Field field : owner.getClass().getDeclaredFields()) {
            if (java.lang.reflect.Modifier.isStatic(field.getModifiers())
                    || !field.getType().isPrimitive()) {
                continue;
            }
            if (leaves.size() >= HANDOFF_LEAF_LIMIT) {
                // Counted, not minted: the caller names how many.
                dropped++;
                continue;
            }
            try {
                field.setAccessible(true);
            } catch (Throwable sealed) {
                continue;
            }
            leaves.add(new HandoffLeaf(owner, field,
                    prefix + exactFieldSignature(field)));
        }
        return dropped;
    }

    /** The one exact VM root of a read-back, or null when it is not one. */
    private static JsonObject exactSymbolOf(JsonElement expression) {
        if (expression == null || !expression.isJsonObject()) return null;
        JsonObject root = expression.getAsJsonObject();
        if (!"SymbolExpression".equals(optionalString(root, "_type"))
                || optionalString(root, "_exp").isEmpty()
                || optionalString(root, "_java_type").isEmpty()) {
            return null;
        }
        return root;
    }

    /**
     * Whether this decision is the declared target event of the addressed
     * occurrence.
     *
     * <p>The site the plan named, at the activation of it the plan
     * addressed, decided.  Nothing else: not whether the predicate there was
     * symbolic, not whether this activation followed a replay prefix, not
     * what the outcome was.  An anchor is the fatal predicate when the
     * branch has one and the concrete outcome when it has not, and which of
     * the two it is lives in the branch row beside the reach, where the
     * composer reads it to decide a propagation cut.</p>
     *
     * <p>It was gated on a solver witness.  On hdfs-17960 the target branch
     * compares two concrete ints -- {@code i != sm.getNumSnapshots()},
     * reached by control dependence because the flip skips a decrement -- so
     * the same activation recorded the decision and was then named by
     * {@code nameUnreachedTargetBranch} as never having decided it.  Those
     * two statements cannot both be true of one activation, and the second
     * one is the one that was wrong.</p>
     *
     * @param decided             whether the decision was recorded at all,
     *                            which is false only where the VM emitted no
     *                            branch event and no row exists to state a
     *                            reach beside
     * @param permutedOccurrence  whether a bounded loop ran the planned
     *                            target occurrence at another one, which the
     *                            replay contract addressed by value
     */
    static boolean statesTargetReach(
            boolean decided, boolean permutedOccurrence,
            String targetBranchSite, int targetBranchOccurrence,
            String branchSite, int occurrence) {
        return decided && !safe(targetBranchSite).isEmpty()
                && safe(targetBranchSite).equals(safe(branchSite))
                && (permutedOccurrence
                || targetBranchOccurrence == occurrence);
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
            return failed("ATTACH", ConcolicVmBroker.MISSING_METADATA,
                    handle);
        }
        ConcolicVmBroker api = engine();
        long exportEventId;
        // README RPC-1: both endpoints of the VALUE_HANDOFF edge leave the VM
        // together.
        long[] attachEvent = new long[1];
        try {
            exportEventId = api.attachExpression(owner, declaringClass,
                    fieldName, descriptor, handle, attachEvent);
        } catch (Throwable throwable) {
            return failed("ATTACH", ConcolicVmBroker.INVOCATION_FAILED,
                    handle);
        }
        if (exportEventId <= 0L) {
            return failed("ATTACH", exportStatus(exportEventId), handle);
        }
        if (attachEvent[0] <= 0L) {
            // A VM that accepted the attach but named no attach event has told
            // us half an edge.
            return failed("ATTACH", ConcolicVmBroker.MALFORMED_RESULT,
                    handle);
        }
        JsonObject success = new JsonObject();
        success.addProperty("exportEventId", exportEventId);
        success.addProperty("attachEventId", attachEvent[0]);
        return new HandoffResult("ATTACH",
                ConcolicVmBroker.OK, handle, success);
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
            return ConcolicVmBroker.MALFORMED_RESULT;
        }
        return (int) handle;
    }

    /**
     * One refused broker call, as the call's own answer.
     *
     * <p>No {@code detail}: the string every caller used to build here was
     * never read by anything, and the diagnostic {@code record(...)} that
     * was to have read it had decayed to an identity function.  What the
     * callers act on is {@link HandoffResult#ok()} and the status.</p>
     */
    private static HandoffResult failed(String stage, int status,
                                        long handle) {
        return new HandoffResult(stage, status, handle, null);
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
            // Runtime observation is fail-closed and cannot alter the
            // return.  Deliberate, and the loss is bounded: every stage
            // inside #finish states its own refusal (closeOccurrence files
            // UNSTATED_VALUE for a read-out it could not invoke, and
            // judgeFinishedOccurrence calls taskUnanswered), so what is
            // left here is the unwinding -- and a row published from the
            // workload's own return path could only be attempted through
            // the same publisher the terminal has just failed on.
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
            // Preserve the program's original throwable identity: the
            // injected bytecode rethrows it, and a refusal raised here
            // would replace it.  Bounded for the same reason as
            // #exitRegionFrame's.
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
        boolean matches = sameHookIdentity(frame.instrumentationSelector,
                instrumentationSelector)
                && sameHookIdentity(frame.rootMethod, rootMethod);
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

    /**
     * The sibling-hook accounting both root stacks share: one physical entry
     * emits one hook per plan row, and only the first is an activation.
     */
    static class SiblingHookGroupEntry {
        final String groupKey;
        private int remainingSiblingHooks;

        SiblingHookGroupEntry(String groupKey, int remainingSiblingHooks) {
            this.groupKey = safe(groupKey);
            this.remainingSiblingHooks = remainingSiblingHooks;
        }

        /** Absorbs one further hook emitted at this same physical entry. */
        final boolean claimsSiblingHook(String actualGroupKey) {
            if (remainingSiblingHooks <= 0
                    || !groupKey.equals(safe(actualGroupKey))) {
                return false;
            }
            remainingSiblingHooks--;
            return true;
        }
    }

    private static final class RootInvocationFrame
            extends SiblingHookGroupEntry {
        private final String instrumentationSelector;
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String instrumentationSelector,
                                    String rootMethod, String rootHookGroupKey,
                                    int remainingSiblingHooks,
                                    long token) {
            super(rootHookGroupKey, remainingSiblingHooks);
            this.instrumentationSelector = instrumentationSelector;
            this.rootMethod = rootMethod;
            this.token = token;
        }
    }

    /** Static hook group that instrumentation placed at one Java entry. */
    static final class RootHookGroup {
        final String key;
        final int hookCount;

        RootHookGroup(String key, int hookCount) {
            this.key = safe(key);
            this.hookCount = Math.max(1, hookCount);
        }
    }

    /**
     * Exact-event overload carrying the id returned by the native marker that
     * the instrumented class executes immediately before its original if.
     */
    /**
     * Reserves a VM-attested branch event immediately before the original
     * conditional executes.
     */
    public static long prepareBranch(String method, int unitIndex,
                                     String expression) {
        return BranchObservation.prepare(method, unitIndex, expression);
    }

    /**
     * Exact-event overload carrying the id returned by the native marker that
     * the instrumented class executes immediately before its original if.
     */
    public static boolean resolveBranch(long preparedHandle, long vmEventId,
                                        String method, int unitIndex,
                                        String expression,
                                        boolean observedOutcome) {
        BranchObservation.observe(BranchDecision.binary(observedOutcome),
                preparedHandle, vmEventId, method, unitIndex, expression);
        return observedOutcome;
    }

    /** Exact multiway counterpart of {@link #resolveBranch}. */
    public static int resolveSwitchBranch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        return BranchObservation.observeSwitch(preparedHandle, vmEventId,
                method, unitIndex, expression, branchKind, encodedCaseKeys,
                observedSuccessorIndex);
    }

    /** Marks one selected occurrence unusable before its VM close. */
    private static void abandonOccurrence(ActiveRegion active, String detail) {
        active.releaseActivation();
        active.abandoned = true;
        active.terminalGap = true;
        endLiveSelectedRegion();
        taskUnanswered(active.activation, detail);
    }

    /** Ends whichever selected occurrence owns {@code token}. */
    static void finish(long token, String exitKind,
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
                judgeFinishedOccurrence(active);
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
            active.activation.noteUnaddressedCandidate(
                    ConcolicTaskPlan.RefusedCandidate.stated(unaddressed));
            active.releaseActivation();
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
            abandonOccurrence(active, "REPLAY_PREFIX_UNMATCHED: the"
                    + " activation contradicts its obligation's prefix: "
                    + edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .refusal(active.d3Address));
            return;
        }
        // The obligation is answered at this terminal, by the one matcher.
        if (active.d3Address != null
                && !edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                        .complete(active.d3Address)) {
            abandonOccurrence(active, "REPLAY_PREFIX_UNMATCHED: the"
                    + " focused occurrence did not take the decision its"
                    + " obligation flips: "
                    + edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .refusal(active.d3Address));
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
        ConcolicVmBroker api = engine();
        boolean engineFinished = false;
        boolean pathConditionPaused = false;
        RawSharedStateReadOut rawSharedState = null;
        boolean publishRows = false;
        try {
            // Everything below is observational bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
            if (!active.abandoned) {
                publishRows = true;
                try {
                    rawSharedState = captureRecordedSharedStateRaw(active,
                            api);
                } catch (Throwable throwable) {
                    // A write log this run could not read out leaves every
                    // location it held with no version to join to, so the
                    // refusal is stated the way the one gap vocabulary states
                    // it rather than on an artifact nobody publishes.
                    RowRuntime.gap(
                            edu.uva.liftlab.graphchecker.contract.GapKind
                                    .UNSTATED_VALUE,
                            edu.uva.liftlab.graphchecker.contract.GapClass
                                    .DIAGNOSTIC,
                            SharedStateCapture.STAGE_VERSIONS,
                            "the tracked-location read-out could not be"
                                    + " invoked, so no write version of this"
                                    + " activation is stated: "
                                    + rootCause(throwable));
                }
            }
            api.finish();
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
        } catch (Throwable ignored) {
            // A read-out that threw is named by the gap the stage that threw
            // filed; the rows this activation can still state are published
            // below, and the native region is popped in the finally.
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
        if (!publishRows) {
            configuration().releaseCandidate(active.activation);
            if (active.terminalGap && !active.activation.loopBodyRoot) {
                active.activation.reserveCompletedEvidence(false);
                haltWhenCampaignSettled(active.activation.taskId, 2);
            }
            return false;
        }
        return submitCompletedResultPublication(active, rawSharedState);
    }


    static ActiveRegion activeRegion() {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long token = tokens.peek();
        return token == null ? null : ownerRegion(token);
    }

    private static void pushActiveRegion(ActiveRegion active) {
        CURRENT_TOKENS.get().push(active.token);
    }

    /** The stack, having proved {@code active} is its innermost entry. */
    private static Deque<Long> innermostActiveRegionStack(
            ActiveRegion active, String violation) {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long current = tokens.peek();
        if (current == null || current.longValue() != active.token) {
            throw new IllegalStateException(violation);
        }
        return tokens;
    }

    /** True only when {@code active} is the innermost region with a caller. */
    private static boolean hasEnclosingActiveRegion(ActiveRegion active) {
        return innermostActiveRegionStack(active,
                "selected regions must close in strict LIFO order").size() > 1;
    }

    /** The exact selected caller of the current innermost activation. */
    private static ActiveRegion enclosingActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = innermostActiveRegionStack(active,
                "selected regions must inspect callers in strict LIFO order");
        java.util.Iterator<Long> iterator = tokens.iterator();
        iterator.next();
        Long enclosingToken = iterator.hasNext() ? iterator.next() : null;
        return enclosingToken == null ? null : ownerRegion(enclosingToken);
    }

    /** Pops the exact innermost activation; an ownership mismatch is fatal. */
    private static void popActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = innermostActiveRegionStack(active,
                "selected region stack does not own token " + active.token);
        tokens.pop();
        if (tokens.isEmpty()) CURRENT_TOKENS.remove();
        // No index-region pop here.  The ENTRY hook owns the pair: it pushes
        // the region (#enterRegionEntry) and #closeRegionEntry pops it, by
        // the entry token.  This pop had no push left after beginActivation
        // stopped opening one (RowRuntime.beginActivation reads
        // currentOccurrence), so it closed the ENCLOSING region instead --
        // and the region exit of the day deleted the closing occurrence's
        // per-site counters, which were the counters that numbered the
        // frames of everything the enclosing occurrence still had to run
        // (counts live in the levels now, and a region holds none).  On
        // hdfs-17960 verification #3 that renumbered the 10 applyEditLogOp
        // entries of one loadEditRecords as 0 and then 0..8, so all 13 tasks
        // addressed under the NameNode restart were refused
        // OCCURRENCE_ANCHOR_UNMATCHED at one frame (planned @1/@2/@4/@6/@8,
        // ran @0/@1/@3/@5/@6) and the tasks whose region ran at every record
        // were answered by the WRONG record.  The frame stack stayed
        // balanced throughout, which is why nothing said so.
    }

    /**
     * Installs the VM's event clock the frame journal samples.
     *
     * <p>One reflective view of the engine exists ({@link ConcolicVmBroker});
     * the identity package holds none, so the clock is handed to it from
     * here.  Idempotent: a run installs the same clock at every region
     * start.</p>
     */
    private static void installEventClock(final ConcolicVmBroker api) {
        edu.uva.liftlab.graphchecker.runtime.RowRuntime.clock(
                new edu.uva.liftlab.graphchecker.runtime.FrameJournal
                        .Clock() {
                    @Override
                    public long now() {
                        try {
                            return api.currentEventId();
                        } catch (Throwable unavailable) {
                            return -1L;
                        }
                    }
                });
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

    static ActiveRegion ownerRegion(long token) {
        ActiveRegion active = ACTIVE.get(token);
        return active != null && active.thread == Thread.currentThread()
                ? active : null;
    }

    @SuppressWarnings("deprecation")

    /**
     * Opens the Java-side branch-observation gate when the first selected
     * input becomes symbolic.
     */
    static void ensurePathRecordingStarted(ActiveRegion active) {
        if (active.pathRecordingStarted) return;
        active.pathRecordingStarted = true;
    }





    static JsonElement parseJson(String value) {
        if (value == null || value.trim().isEmpty()) {
            return new JsonObject();
        }
        try {
            return new JsonParser().parse(value);
        } catch (RuntimeException ignored) {
            return GSON.toJsonTree(value);
        }
    }

    static String rootCause(Throwable throwable) {
        Throwable current = throwable;
        while (current instanceof InvocationTargetException
                && ((InvocationTargetException) current).getTargetException() != null) {
            current = ((InvocationTargetException) current).getTargetException();
        }
        return current == null ? "unknown" : current.toString();
    }



    /**
     * How a configured source's recorded value is spelled in the ledger.
     *
     * <p>The same spelling the recorded-root ledger already uses for a
     * manual root's {@code primitiveValue}, so one reader can compare a
     * witness against either: {@code "true"}/{@code "false"} for a Boolean,
     * the decimal digits for an integral, the literal text for a String. A
     * reference the runtime cannot spell as a scalar states nothing rather
     * than a {@code toString()} nobody can compare against.</p>
     */
    static String recordedScalar(Object value) {
        if (value instanceof Boolean || value instanceof Character
                || value instanceof Byte || value instanceof Short
                || value instanceof Integer || value instanceof Long
                || value instanceof Float || value instanceof Double
                || value instanceof String) {
            return String.valueOf(value);
        }
        return "";
    }

    static final class AccessorCallContext {
        private final long contextToken;
        final long regionToken;
        final Thread thread;
        private final String callerMethod;
        private final int callUnitIndex;
        final String callSiteId;
        private final String declaredCallee;
        final Object receiver;
        final int occurrence;
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

    /**
     * Activation-local ordinals for repeated executions of one hook.  A new
     * region activation owns a new counter, so no runtime event id or
     * process-global invocation ordinal becomes replay identity.
     */
    static final class OccurrenceCounter {
        private final Map<String, Integer> occurrences =
                new LinkedHashMap<>();

        int local(String method, int unitIndex, String local) {
            return observe("LOCAL\u0000"
                    + SiteId.render(method, unitIndex)
                    + "::" + safe(local));
        }

        int methodArgument(String method, int argumentIndex) {
            return observe("ARGUMENT\u0000" + safe(method) + "#arg"
                    + argumentIndex);
        }

        int observedMethodArgument(String method, int argumentIndex) {
            return observed("ARGUMENT\u0000" + safe(method) + "#arg"
                    + argumentIndex);
        }

        /**
         * One read site's occurrences.
         *
         * <p>{@code SiteId.render} and not {@code SiteId.of}: the
         * instrumentation deliberately passes a {@code -1} unit index for an
         * accessor implementation that has no unit of its own, and a strict
         * parse of that sentinel throws inside the workload.</p>
         */
        int field(String method, int unitIndex) {
            return observe("FIELD\u0000"
                    + SiteId.render(method, unitIndex));
        }

        /**
         * A workload-declared fault marker counts per activation and per
         * declared symbol.  The recorder counts the same firings per
         * activation and per call site
         * ({@code RuntimeRefinedGraphBuilder.collectAccessorBindings}); one
         * marker literal names one call site, so the two ordinals agree and
         * {@code replayOccurrence} selects the exact recorded firing.
         */
        int explicitFault(String symbolicName) {
            return observe("EXPLICIT_FAULT\u0000" + safe(symbolicName));
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

    static final class ActiveRegion {
        /** The thread this activation ran on, as the recording names it. */
        final String threadName = Thread.currentThread().getName();
        final long token;
        /** The one task whose region-local path this activation records. */
        final RuntimeTask activation;
        /**
         * This activation's identity v2 address, or null when this run can
         * name no node to put it on.
         *
         * <p>{@code node#epoch / lineage hops / region#k} (IDENTITY-V2): the
         * address every contract row of this activation is keyed by.  The v1
         * {@link #occurrenceId()} is unchanged beside it -- the two are
         * minted from the same activation and nothing reads one for the
         * other.</p>
         */
        edu.uva.liftlab.graphchecker.contract.OccurrenceAddress d3Address;
        /** Whether this activation counts against its address's set. */
        private boolean activationClaimed;
        /** VM context whose writes belong to this materialized activation. */
        long vmContextId;
        /** Exact event-ledger entry of this native region frame. */
        long vmRegionEnterEventId;
        final Object receiver;
        final Thread thread;
        /** Entry lacked local producer-source evidence; OUT must confirm it. */
        /** Exact outgoing message leaves this provisional activation reached. */
        final AtomicBoolean finished = new AtomicBoolean();
        private boolean prepared;
        /**
         * The declared target branch event this occurrence decided, or {@code
         * null} while it has not decided one.
         */
        JsonObject targetReach;
        /** Terminal outcome, frozen when the occurrence stops running. */
        boolean abandoned;
        /** A selected non-loop occurrence ended in a durable named gap. */
        private boolean terminalGap;
        private boolean closed;
        /** Loop bodies this activation has charged. */
        volatile long chargedLoopBodies;
        /**
         * The stable causal context this candidate observed while it was live:
         * the logical sources it ran on and the external request scopes it ran
         * inside.
         */
        private final Set<String> observedSourceKeys = new LinkedHashSet<>();
        /** element key -> attaches of it so far in this activation. */
        private final Map<String, Integer> handoffAttachOrdinals =
                new LinkedHashMap<>();
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

        /** Exact configured-source and planned-action observations. */
        final List<JsonObject> symbolizedRows = new ArrayList<>();
        final List<JsonObject> branchMappings = new ArrayList<>();
        /**
         * Case-local references into the VM's own handoff ledger: the
         * declared port an attach landed on and the export event the
         * {@code VALUE_HANDOFF} edge relates it to.
         */
        /**
         * VM export event most recently published at each declared port.
         *
         * <p>README {@code RPC-1}: written down from the VM's own export
         * answer so the producer's interaction row can name it.</p>
         */

        /** The write log this activation read out, and its gaps. */
        final Map<String, JsonObject> sharedStateRecords =
                new LinkedHashMap<>();
        /** Read-out batch every record of this activation is stamped with. */
        final Set<String> materialized = new LinkedHashSet<>();
        private final Map<String, Integer> branchOccurrences =
                new LinkedHashMap<>();
        final OccurrenceCounter
                materializationOccurrences =
                new OccurrenceCounter();
        private final Map<String, Integer> accessorCallOccurrences =
                new LinkedHashMap<>();
        final LoopBackedgeBudget loopBackedges;
        /**
         * The ordinal of the OPEN dynamic invocation of each fixed-count
         * loop, by runtime natural-loop id.
         *
         * <p>Its only reader is {@link #chargeLoopBody}, which scopes the
         * replay body budget to one dynamic invocation.  It used to also
         * publish a {@code loopCardinalities} row per invocation carrying
         * the exact array length, its ordinal and a cardinality authority;
         * nothing read those rows once R1 deleted the result envelope they
         * were written onto.</p>
         */
        private final Map<String, Integer> activeLoopInvocations =
                new LinkedHashMap<>();
        /** Next invocation ordinal by runtime natural-loop id. */
        private final Map<String, Integer> loopInvocationOrdinals =
                new LinkedHashMap<>();
        private final Map<Long, PreparedBranch> preparedBranches =
                new LinkedHashMap<>();
        /** One shared expression DAG for all read-outs in this VM session. */
        final VmExpressionTable.Store expressionStore;
        private long preparedBranchSequence;
        int lastPathConditionSize;
        /** Whether this activation's bounded local path has been cut. */
        boolean loopBoundCut;
        boolean pathRecordingStarted;

        ActiveRegion(long token, RuntimeTask activation,
                             Object receiver, Thread thread) {
            this.token = token;
            this.activation = activation;
            this.receiver = receiver;
            this.thread = thread;
            this.expressionStore = workloadExpressionStore;
            this.loopBackedges = new LoopBackedgeBudget(
                    activation.loopBound);
        }


        /**
         * Counts this activation against the published set of its address,
         * which is what bounds a loop-body region's occurrences.
         */
        void claimActivation() {
            if (activationClaimed) return;
            activationClaimed = true;
            activation.claimActivation();
        }

        /** Gives the slot back; this activation published nothing. */
        void releaseActivation() {
            if (!activationClaimed) return;
            activationClaimed = false;
            activation.releaseActivation();
        }

        /**
         * This activation's own occurrence identity.
         *
         * <p>The address, and nothing appended to it. Identity v1 numbered
         * the activations of one planned address and wrote {@code #a<n>}
         * beside it, because two runs of one address were two occurrences it
         * could not otherwise tell apart. Identity v3 distinguishes them by
         * the execution index they entered under, so an address IS the
         * occurrence and a suffix would be a second identity beside it.</p>
         */
        String occurrenceId() {
            return safe(activation.occurrenceId);
        }

        /**
         * Charges one body of this loop to the replay resource cap, returning
         * the cut that ends the activation once the cap is spent.
         */
        synchronized ReplayLoopResourceCut chargeLoopBody(
                String loopId) {
            int maxBodies = activation.maxLoopBodies(loopId);
            chargedLoopBodies++;
            // A fixed-count loop may be invoked repeatedly inside one region
            // activation.  Its resource ceiling applies to each dynamic
            // invocation; accumulating all invocations under the static loop
            // id cuts ordinary code after (for example) two 16-element array
            // walks.  openLoopInvocation opens the exact invocation before
            // the first body hook and closeLoopInvocation closes it.
            Integer invocation = activeLoopInvocations.get(loopId);
            String budgetKey = invocation == null ? loopId
                    : LoopBackedgeBudget.scoped(loopId,
                            invocation.intValue());
            long entered = loopBackedges.recordBody(budgetKey);
            if (entered <= maxBodies) return null;
            return new ReplayLoopResourceCut(loopId, maxBodies, entered);
        }

        /**
         * Opens one dynamic invocation of a fixed-count loop.
         *
         * <p>The resource ceiling applies per invocation, so the backedge
         * budget is scoped by which invocation this is; that an invocation
         * is open at all is the whole of what the hook states now.</p>
         */
        synchronized void openLoopInvocation(String loopId) {
            if (loopId.isEmpty()
                    || activeLoopInvocations.containsKey(loopId)) {
                return;
            }
            activeLoopInvocations.put(loopId,
                    loopInvocationOrdinals.merge(loopId, 1, Integer::sum));
        }

        synchronized void closeLoopInvocation(String loopId) {
            if (!loopId.isEmpty()) activeLoopInvocations.remove(loopId);
        }

        /** Records the terminal of this activation's bounded local path. */
        LoopBoundCut loopBoundCut(
                String backedgeId, int maxTraversals, String reason) {
            loopBoundCut = true;
            return new LoopBoundCut(backedgeId, maxTraversals, reason);
        }

        /** k for the next attach of one element in this activation. */
        private int nextHandoffAttach(String elementKey) {
            Integer previous = handoffAttachOrdinals.get(elementKey);
            int ordinal = previous == null ? 1 : previous + 1;
            handoffAttachOrdinals.put(elementKey, ordinal);
            return ordinal;
        }

        private int nextBranchOccurrence(String siteId) {
            Integer previous = branchOccurrences.get(siteId);
            int occurrence = previous == null ? 1 : previous + 1;
            branchOccurrences.put(siteId, occurrence);
            return occurrence;
        }

        /**
         * Records a decision while the symbolic gate is closed, and answers
         * with the occurrence of the site it charged, or {@code 0} where
         * nothing was recorded.
         */
        int recordConcreteDecision(
                String method, int unitIndex, BranchDecision decision) {
            try {
                // observeDecision is the only caller and it has already
                // returned for every undeclared site, so the site here is
                // always one the plan named.
                String site = SiteId.render(method, unitIndex);
                int occurrence = nextBranchOccurrence(site);
                recordDecisionRow(method, unitIndex, occurrence,
                        decision.outcome());
                if (activation.targetBranchSite.equals(site)
                        && activation.targetBranchOccurrence == occurrence) {
                    recordTargetReach(site, occurrence, decision.outcome(),
                            0L);
                }
                return occurrence;
            } catch (Throwable ignored) {
                // Observation must never alter the workload's own outcome.
                return 0;
            }
        }

        /** The branch row one decision that added no path condition is. */
        private void recordDecisionRow(
                String method, int unitIndex, int occurrence,
                boolean outcome) {
            JsonObject mapping = BranchObservation.branchMapping(
                    method, unitIndex, occurrence, 0L);
            mapping.addProperty("outcome", outcome);
            mapping.addProperty("rawPathConditionSize", 0);
            mapping.addProperty("rawPathConditionBaseline", 0);
            branchMappings.add(mapping);
        }

        /**
         * States one decision to the one prefix matcher.
         *
         * <p>{@code runtime/FocusedReplay} is the only account of
         * whether a replay is following its obligation: it reads the
         * obligation and the published decisions, and a second account of
         * the same decisions is how two answers to one question appear.</p>
         */
        boolean observeReplayDecision(
                String siteId, int occurrence, BranchDecision decision) {
            if (d3Address == null) return true;
            edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                    .observeDecision(d3Address, siteId, occurrence,
                            decision.outcome);
            return !edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                    .contradicted(d3Address);
        }

        /**
         * Whether this activation has already walked a branch its
         * obligation forbids.
         */
        boolean replayPrefixContradicted() {
            return d3Address != null
                    && edu.uva.liftlab.graphchecker.runtime.FocusedReplay
                            .contradicted(d3Address);
        }

        int nextLocalMaterializationOccurrence(
                String method, int unitIndex, String local) {
            return materializationOccurrences.local(method, unitIndex,
                    local);
        }

        PreparedBranch prepareBranch(
                String method, int unitIndex, String expression)
                throws Exception {
            String site = SiteId.render(method, unitIndex);
            int occurrence = nextBranchOccurrence(site);
            long sequence = ++preparedBranchSequence;
            if (sequence > Integer.MAX_VALUE) {
                return null;
            }
            long handle = (sequence << 32)
                    | (occurrence & 0xffffffffL);
            PreparedBranch prepared = new PreparedBranch(handle, method,
                    unitIndex, expression, occurrence);
            preparedBranches.put(handle, prepared);
            return prepared;
        }

        PreparedBranch takePreparedBranch(long handle) {
            return handle <= 0L ? null : preparedBranches.remove(handle);
        }

        /**
         * Records the declared target branch event this occurrence decided.
         */
        void recordTargetReach(String siteId, int occurrence,
                                       boolean outcome, long vmEventId) {
            if (targetReach != null) return;
            JsonObject reach = new JsonObject();
            reach.addProperty("kind", "TARGET_REACH_EVENT");
            reach.addProperty("siteId", safe(siteId));
            reach.addProperty("occurrence", occurrence);
            reach.addProperty("outcome", outcome);
            // The anchor is read on the same clock as the decisions, so a
            // composer can say which of them were taken before it.
            if (vmEventId > 0L) reach.addProperty("vmEventId", vmEventId);
            targetReach = reach;
        }

        /**
         * Records one firing of a fault marker this replay could not answer.
         *
         * <p>{@link #materializeSymbolicBoolean} must hand the workload a
         * {@code boolean}: the marker stands at a call site the program is
         * about to branch on, so there is no third value to return and no
         * point at which the replay can stop.  What it must not do is let
         * the {@code false} it returns pass for an answer.</p>
         *
         * <p>There are two answers, and a firing is unanswered only when it
         * has neither.  A flip replay answers from its model assignment; a
         * seed replay has no model by construction and answers from the
         * recording's own polarity, which the plan states as the action's
         * {@code primitiveValue} gated on {@code observed}.</p>
         *
         * <p>{@code controlled} decides the class, and it decides it the
         * way the frame does.  A marker the plan declares is a question the
         * search asked and neither answer came, so the polarity handed back
         * is the very one the obligation asked to move: the run did not run
         * what was asked, which is BLOCKING and is exactly what {@code
         * ASSIGNMENT_UNPLANTED} names.  A marker the plan never declared
         * put no question to this replay -- the recording ran the same hook
         * to the same {@code false} -- so it is named on the diagnostic
         * stream and nothing is refused.</p>
         *
         * <p>Both bodies used to be empty, so a fault that fired the plan's
         * controls and could not answer was silently {@code false}.</p>
         */
        void noteFaultIdle(String name, int occurrence, boolean controlled,
                           String reason) {
            String subject = "marker=" + safe(name) + "#" + occurrence;
            if (controlled) {
                RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.ASSIGNMENT_UNPLANTED,
                        edu.uva.liftlab.graphchecker.contract.GapClass.BLOCKING, subject,
                        "this activation's plan controls the marker and had"
                                + " neither answer for this firing ("
                                + safe(reason) + "), so it ran the polarity"
                                + " the obligation asked to move");
                return;
            }
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind.DECLARATION_MISSING,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC, subject,
                    "this fault marker fired where the case declares no"
                            + " action for it (" + safe(reason) + ")");
        }

        /**
         * The declared mint site one hook execution stands at, or null.
         *
         * <p>The catalog is a list of mint SITES, not a selection and not a
         * budget: any read at a known site binds to that site's symbol,
         * however many reads there are and whichever occurrence makes them.
         * A hook that fires at a site the catalog does not name is still a
         * gap - that is a plan/instrumentation disagreement, not a free
         * occurrence.</p>
         */
        synchronized RootMint.SourceSiteEntry observeConfiguredSourceEntry(
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
                refuseMint(edu.uva.liftlab.graphchecker.contract.GapKind
                                .DECLARATION_MISSING,
                        declaration.isEmpty() ? null : declaration.get(0),
                        "the PUBLISH hook for " + safe(sourceId)
                                + " ran under no active call site, so the"
                                + " mint is at no declared phase");
                return null;
            }
            if (declaration.isEmpty()) {
                refuseMint(edu.uva.liftlab.graphchecker.contract.GapKind
                                .DECLARATION_MISSING, null,
                        "PUBLISH " + site + " is outside the frozen phase"
                                + " catalog, so nothing declares this mint");
                return null;
            }
            // Every row of this list is one execution of ONE site, so they
            // agree on everything the mint reads off a declaration - the
            // phase id the symbol is derived from, the field and the callee.
            // Which execution the recording made is evidence on the row, not
            // a limit on the reads a replay may make.
            ConfiguredSourcePhaseContract.Occurrence matched =
                    declaration.get(0);
            if (!matched.fieldSignature().equals(
                    safe(runtimeFieldSignature))
                    || !matched.runtimeDeclaredCallee().equals(
                    context.declaredCallee())) {
                refuseMint(edu.uva.liftlab.graphchecker.contract.GapKind
                                .DECLARATION_MISSING, matched,
                        "the runtime field and callee differ from the ones"
                                + " the catalog site declares");
                return null;
            }
            return new RootMint.SourceSiteEntry(matched, site);
        }

        /** Publishes one mint row for one entry of a declared site. */
        synchronized void recordConfiguredSourceMint(
                RootMint.SourceSiteEntry entry, String sourceId,
                String fieldSignature, String symbol,
                JsonElement expression, boolean reused,
                String recordedValue) {
            JsonObject row = new JsonObject();
            // What the run read at the mint.  A root whose row states no
            // value has no centre for a relative domain to resolve
            // against -- [+0,+3] around nothing -- so the composer cannot
            // move it at all.
            if (recordedValue != null && !recordedValue.isEmpty()) {
                row.addProperty("observedValue", recordedValue);
                row.addProperty("recordedValue", recordedValue);
            }
            row.addProperty("sourceId", safe(sourceId));
            row.addProperty("sourcePhaseId", entry.phaseId());
            row.addProperty("occurrenceId", occurrenceId());
            row.addProperty("siteId", entry.siteId);
            row.addProperty("fieldSignature", safe(fieldSignature));
            row.addProperty("symbol", safe(symbol));
            row.add("expression", expression == null
                    ? JsonNull.INSTANCE : expression);
            row.addProperty("reused", reused);
            row.addProperty("mintOccurrence",
                    mintOccurrence(safe(sourceId)));
            symbolizedRows.add(row);
        }

        /**
         * The occurrence a mint of this root is ADDRESSED at, rendered.
         *
         * <p>The activation of the region whose plan owns the mint
         * ({@link #declaringRegion}), which is the runtime counterpart of
         * {@code StaticScopeMap.holders}.  Captured here because here is
         * where the region stack is live: the row is published when the
         * activation closes, and by then the nesting is gone.  It is what
         * makes a mint address the same in the seed and in a replay -- the
         * row used to carry whichever activation happened to be innermost,
         * and hdfs-11741 campaign #3 has one session (e635d55d...) whose
         * SERIAL_NO row landed on REGION.08ab84c9 at index depth 1 where
         * every other session and the seed put it on REGION.aaa1cfd7 at
         * depth 2, so the focus row's rootMints address matched nothing.</p>
         */
        private String mintOccurrence(String rootId) {
            ActiveRegion owner = declaringRegion(new Declares.Root(rootId));
            if (owner == null) owner = this;
            return owner.d3Address == null ? ""
                    : owner.d3Address.render();
        }

        /**
         * Records what one exact frozen {@code SYMBOLIC} action observed after
         * its runtime hook either minted a value or retained a propagated one.
         * The requested VM label is descriptive only; downstream authority is
         * derived from the exact expression, never from this label.
         */
        synchronized void recordManualSymbolization(
                SymbolizeAction action, String requestedSymbol,
                List<String> fieldPath, String fieldSignature,
                JsonElement expression, boolean minted, boolean reused) {
            recordManualSymbolization(action, requestedSymbol, fieldPath,
                    fieldSignature, expression, minted, reused, "");
        }

        /**
         * The same row, with the concrete value the mint read.
         *
         * <p>One mint publication shape: a configured-source mint states
         * what the field held
         * and a manual one stated nothing, so a root the composer met
         * through a manual input had no recorded value to lower -- on lane
         * VM12 that is DelegationKey.expiryDate, minted as
         * {@code M_J_field_REGION.aaa1cfd7...}, and
         * RECORDED_ROOT_VALUE_UNSTATED was the anchor's last refusal.  The
         * suppression rule is the configured source's too: a replay that
         * wrote a model into the value read the model back, and publishing
         * that as "recorded" is how a counterfactual becomes the
         * recording.</p>
         */
        synchronized void recordManualSymbolization(
                SymbolizeAction action, String requestedSymbol,
                List<String> fieldPath, String fieldSignature,
                JsonElement expression, boolean minted, boolean reused,
                String recordedValue) {
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
            // WHERE in the region this read stood, captured here because
            // here is where it runs: the row is published at the end of the
            // activation, and the frames are gone by then.  Two reads of one
            // accessor site inside one occurrence differ by the site index's
            // own innermost frame (Identity.eventSiteIndex), not by an
            // ordinal and not by a frame only a replay stands on.
            row.addProperty("siteIndex", RowRuntime.siteIndexHere());
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
            if (recordedValue != null && !recordedValue.isEmpty()) {
                // What THIS execution read at the mint, under both names.
                // A clock is no exception: the seed replay IS the reference
                // execution, so the instant it read is the one the composer's
                // deltas are relative to, and a row that carried the PLAN's
                // instant instead described an execution nobody ran.  A
                // replay that planted a value read the model back and states
                // neither (the guard above): a counterfactual is not a
                // recording.
                row.addProperty("observedValue", recordedValue);
                row.addProperty("recordedValue", recordedValue);
            }
            // The case declared this read a wall clock, so the mint row
            // states it and no reader downstream has to guess a clock from a
            // callee or a site name.  It states WHERE the plan observed the
            // read and nothing about its value: the value is the one above,
            // which is what THIS execution read.
            //
            // The plan's own instant used to be published here as
            // recordedValue.  The seed replay is THE reference execution --
            // the composer's clock deltas are relative to the recordedValue
            // its rows state -- so a row that names the PLAN's instant makes
            // every delta relative to an execution that is not the one the
            // session describes.  A replay that planted `now + skew` states
            // no recordedValue at all, by the rule above: a counterfactual
            // is not a recording.
            if (action.declaresWallClockRead()) {
                row.addProperty(InputActionCatalog.DECLARED_WALL_CLOCK, true);
                row.addProperty("eventSeq", action.eventSeq);
            }
            row.addProperty("mintOccurrence",
                    mintOccurrence(safe(action.symbol)));
            symbolizedRows.add(row);
        }

        /**
         * Names one refusal at a configured source's mint, as a row.
         *
         * <p>One gap vocabulary: this used to build a second row shape into
         * a list nothing downstream read, so a mint the replay refused was
         * invisible to the claim.  Every one of these means the wave's value
         * was NOT written at the mint the obligation is about, so they are
         * BLOCKING for the session that met them and the subject is the
         * phase the declaration names.</p>
         */
        private void refuseMint(
                edu.uva.liftlab.graphchecker.contract.GapKind kind,
                ConfiguredSourcePhaseContract.Occurrence phase,
                String detail) {
            RowRuntime.gap(kind, edu.uva.liftlab.graphchecker.contract
                            .GapClass.BLOCKING,
                    phase == null ? occurrenceId() : phase.phaseId(),
                    safe(detail));
        }

        /**
         * Whether this run can place this mint at the node and epoch the
         * plan addresses, filing the gap that says why not.
         *
         * <p>A configured source names one mint SITE, and the site is
         * reached once per node lifecycle.  The site is not the address: the
         * address is (node, epoch, region, k-th activation), and the epoch
         * is the half nothing was checking.  On hdfs-17960 the flip replay
         * threw inside the workload before it restarted the NameNode, so
         * the only activation it offered was epoch 0 -- and root=false was
         * written there, at the mint the recording made before the restart,
         * instead of at the epoch-1 mint the plan addresses.  The recorded
         * execution was rewritten at a point the wave said nothing
         * about.</p>
         */
        synchronized boolean mintIsPlaceable(Object mintOwner) {
            String unattributed = mintIsNotThePlannedNode(mintOwner);
            if (unattributed.isEmpty()) return true;
            refuseMint(mintAttribution(mintOwner).isEmpty()
                            ? edu.uva.liftlab.graphchecker.contract.GapKind
                                    .MINT_UNATTRIBUTED
                            : edu.uva.liftlab.graphchecker.contract.GapKind
                                    .EPOCH_UNMATCHED, null, unattributed);
            return false;
        }

        /**
         * Every node this run can attribute this mint to, at mint time.
         *
         * <p>Three registrations, all the workload's own: the object whose
         * field is being minted, the source this occurrence was entered
         * under, and whatever the thread is carrying now.  The registry is
         * the same one {@link ConcolicTaskPlan#lifecycleMismatch} reads, so
         * the epoch here is the epoch admission compared.</p>
         */
        private Set<String> mintAttribution(Object mintOwner) {
            Set<String> attributed = new LinkedHashSet<>(
                    attributedSourceKeys());
            SourceRef owner = RuntimeTraceContext.sourceFor(mintOwner);
            if (owner != null) attributed.add(owner.key());
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            if (context != null && context.source != null) {
                attributed.add(context.source.key());
            }
            return attributed;
        }

        /**
         * Why this mint cannot be shown to be the planned node and epoch,
         * or {@code ""}.
         *
         * <p>Deliberately stricter than root admission, and the asymmetry is
         * the point.  Admission admits an activation nothing attributed --
         * absence of evidence is not evidence of another occurrence, and a
         * replay routinely reconstructs a receiver without repeating its
         * alias registration.  A model is different in kind: it <em>rewrites
         * the recorded execution</em>, and doing that at a mint the run
         * cannot place is asserting an occurrence nobody established.  So a
         * mint must be attributed positively, and an unattributed one
         * refuses the model and keeps the value the recording made.</p>
         *
         * <p>This is the hdfs-17960 flip in its general form.  The address is
         * (node, epoch, region, k-th activation); the mint site is reached
         * once per node lifecycle, so the epoch is what tells two mints of
         * one site apart, and root=false landing on the epoch-0 mint
         * rewrote a value the solver had said nothing about.  Refusing on a
         * different epoch closed that where the run attributes the mint;
         * requiring attribution closes it where the run does not.</p>
         */
        private String mintIsNotThePlannedNode(Object mintOwner) {
            String planned = safe(activation.sourceKey);
            if (!RuntimeTraceContext.declaresEpoch(planned)) return "";
            Set<String> attributed = mintAttribution(mintOwner);
            if (attributed.contains(planned)) return "";
            if (attributed.isEmpty()) {
                return "the registry attributes this mint to no node, so it "
                        + "cannot be shown to be " + planned + "; the "
                        + "recorded value stands";
            }
            String elsewhere = ConcolicTaskPlan.lifecycleMismatch(planned,
                    attributed);
            return elsewhere.isEmpty()
                    ? "the registry attributes this mint to " + attributed
                    + ", which does not include " + planned
                    : elsewhere;
        }
    }

    static final class SymbolizeAction {
        final String symbol;
        /** Canonical identity of the exact frozen task action row. */
        final String actionDigest;
        final String cell;
        final String location;
        final int index;
        final int replayOccurrence;
        final List<List<String>> fieldPaths;
        final String bindingMode;
        final String method;
        final String local;
        final String accessField;
        final String accessOwnerClass;
        final String accessFieldSignature;
        final Set<String> accessSites = new LinkedHashSet<>();
        final String accessorCallerMethod;
        final int accessorCallUnitIndex;
        final String accessorDeclaredCallee;
        final String accessorImplementationMethod;
        /** How the finalizer classified the port that minted this action. */
        final String sourceKind;
        /** Whether the case declared this read to be a wall clock. */
        final boolean clock;
        /** The static site the plan observed this read at, or "". */
        final String siteId;
        /** The recorded event this read was observed at, or -1. */
        final long eventSeq;
        /** What this read returned in the recording, or "" when unobserved. */
        final String recordedPrimitiveValue;
        /** The selection file named this input by hand: mint, do not reuse. */
        final boolean declaredSymbolicRoot;
        final String rootKind;
        final List<String> fieldPath;
        final String javaType;
        final String symbolicName;
        final Set<Integer> definitionUnitIndices =
                new LinkedHashSet<>();
        final Map<String, String> leafFieldSignaturesByPath =
                new LinkedHashMap<>();

        SymbolizeAction(JsonObject json) {
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
            this.sourceKind = optionalString(json, "sourceKind");
            this.clock = optionalBool(json,
                    InputActionCatalog.DECLARED_WALL_CLOCK, false);
            this.siteId = optionalString(json, "siteId");
            this.eventSeq = optionalLongInteger(json, "eventSeq", -1L);
            this.recordedPrimitiveValue = optionalBool(json, "observed", false)
                    ? optionalString(json, "primitiveValue") : "";
            this.declaredSymbolicRoot = optionalBool(json,
                    InputActionCatalog.DECLARED_SYMBOLIC_ROOT, false);
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

        boolean declaresArrayInput(List<String> actualPath) {
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

        boolean matchesLocal(String actualMethod,
                                     int actualUnitIndex,
                                     String actualLocal) {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && (definitionUnitIndices.isEmpty()
                    || definitionUnitIndices.contains(actualUnitIndex))
                    && local.equals(safe(actualLocal));
        }

        boolean matchesMethodArgument(String actualMethod,
                                              int actualIndex) {
            return "METHOD_ARGUMENT".equals(bindingMode)
                    && method.equals(safe(actualMethod))
                    && index == actualIndex;
        }

        boolean acceptsOccurrence(int actualOccurrence) {
            return replayOccurrence < 1
                    || replayOccurrence == actualOccurrence;
        }

        boolean acceptsDirectFieldOccurrence(int actualOccurrence) {
            boolean accessorConstrained = !accessorCallerMethod.isEmpty()
                    || accessorCallUnitIndex >= 0
                    || !accessorDeclaredCallee.isEmpty()
                    || !accessorImplementationMethod.isEmpty();
            return accessorConstrained || acceptsOccurrence(actualOccurrence);
        }

        boolean repeatedPrimitiveAccessor() {
            return "LOCAL_DEFINITION".equals(bindingMode)
                    && "CALL_RETURN".equals(location)
                    && JavaPrimitiveBoxing.unboxReturn(cell);
        }

        /**
         * Whether this root is a wall-clock read whose recorded answer is
         * known.
         *
         * <p>The case's {@code symbolic-inputs.jsonl} row declares it
         * ({@link InputActionCatalog#DECLARED_WALL_CLOCK}); nothing here
         * matches a callee signature against a list of clock names.  A root
         * the case declares a clock is exactly the root the composer moves by
         * an offset from what the recording read.</p>
         */
        boolean declaresWallClockRead() {
            return clock && !recordedPrimitiveValue.isEmpty();
        }

        boolean matchesStaticField(String actualMethod,
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
            return accessSites.contains(SiteId.render(actualMethod,
                    actualUnitIndex))
                    && (cell.contains(exactSignature)
                    || accessFieldSignature.equals(exactSignature));
        }

        /**
         * Reconstructs the activation's logical path for an exact getstatic
         * materialization.
         */
        List<String> exactStaticFieldPath(
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

        boolean matchesField(String actualMethod,
                                     int actualUnitIndex, Object owner,
                                     String signature, String actualField) {
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
                    : SiteId.render(accessorCallerMethod,
                            accessorCallUnitIndex);
            boolean accessSiteConstrained = !accessSites.isEmpty();
            // Accessor actions name their caller's invoke site in accessSites,
            // while this hook runs at the implementation's field read.
            if (accessSiteConstrained) {
                String constrainedSite = accessorConstrained
                        ? accessorSiteId
                        : SiteId.render(actualMethod, actualUnitIndex);
                if (constrainedSite.isEmpty()
                        || !accessSites.contains(constrainedSite)) {
                    return false;
                }
            }
            Boolean lightweightContext = lightweightAccessorContextMatches(
                    accessorCallerMethod, accessorCallUnitIndex,
                    accessorSiteId, accessorDeclaredCallee, owner);
            boolean accessorContextMatches = lightweightContext != null
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

        Object leafOwner(Object accessOwner) {
            return resolveFieldPathLeafOwner(accessOwner, fieldPath);
        }

        /**
         * Returns the exact declaration of the scalar/array leaf that will
         * actually be symbolized.
         */
        String exactLeafFieldSignature() {
            return exactLeafFieldSignature(fieldPath);
        }

        String exactLeafFieldSignature(List<String> actualPath) {
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
}
