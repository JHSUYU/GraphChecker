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
    static final String MANUAL_INPUT_OBSERVATION_KIND =
            "MANUAL_SYMBOLIC_INPUT_OBSERVATION";
    static final String MANUAL_INPUT_OBSERVATION_AUTHORITY =
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
    static volatile VmExpressionTable.Store workloadExpressionStore =
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
            //
            // This journal is never evicted, and this class cannot be the
            // one that evicts it: the activation's rows are written by the
            // publication pool (#closeOccurrence ->
            // submitCompletedResultPublication), which returns before they
            // are, and an ENCLOSING activation may publish a read performed
            // inside this one under this regionEnterEventId -- so neither
            // #closeOccurrence nor #popActiveRegion is a point at which the
            // journal is provably dead.  The only barrier that is,
            // awaitSelectedResultPublications, is workload-wide, i.e. it
            // comes at the moment the process ends anyway.  A bounded leak
            // (7,266 journals on 11741, 266 on 17960), not a correctness
            // defect; the owner of the eviction is whoever owns the
            // publication's completion, not the region hook.
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
        // The carrier IS the work, so with none there is no frame to claim
        // and nothing for a refusal below to be ABOUT.  Answered here
        // rather than by passing "" as the subject of a gap row -- which
        // Fields.text refuses, out of a woven hook, into the workload.
        if (carrier == null) return;
        try {
            RowRuntime.claimStart(carrier);
        } catch (Throwable unnamed) {
            // The work runs either way, and the hole is stated: the
            // occurrences this work publishes will be missing the
            // start-site frame that tells two siblings apart.
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    carrier.getClass().getName(),
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
                    // The woven start site, else the work it was filed
                    // for: one of the two is always spelled.
                    firstNonBlank(site, carrier == null ? ""
                            : carrier.getClass().getName()),
                    "the frame of this work start could not be filed, "
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

    /**
     * Opens the frame around one message instance being serialized.
     *
     * <p>A declared port is one pair of bytecode sites, and a protocol
     * sends many unrelated values of that shape through it.  The frame is
     * the thing whose single construction builds one instance of the value
     * the port belongs to.</p>
     */
    public static void pushOutboundMessageFrame() {
        WireExport.pushOutboundFrame();
    }

    /** Closes the frame {@link #pushOutboundMessageFrame} opened. */
    public static void popOutboundMessageFrame() {
        WireExport.popOutboundFrame();
    }

    /** Opens the frame around one message instance being decoded. */
    public static void pushInboundMessageFrame() {
        WireExport.pushInboundFrame();
    }

    /** Closes the frame {@link #pushInboundMessageFrame} opened. */
    public static void popInboundMessageFrame() {
        WireExport.popInboundFrame();
    }

    /** Exports the live expression of one declared communication port. */
    public static void exportCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        WireExport.exportLeaf(portId, carrier, field, descriptor);
    }

    /** Attaches the exported expression of one declared communication port. */
    public static void attachCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor) {
        WireExport.attachLeaf(portId, carrier, field, descriptor);
    }

    /**
     * The one instance field a declared communication port crosses on.
     *
     * <p>Stays nested here: {@code CausynthPipeline} allocates it by the
     * binary name {@code ...ConcolicRegionRuntime$HandoffLeafCarrier}
     * ({@code CausynthPipeline:1714}), so this class name is woven
     * bytecode.</p>
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

    static final String CARRIER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                    + "$HandoffLeafCarrier";
    // ------------------------------------------------------------------
    // Communication message flow
    // ------------------------------------------------------------------

    // ------------------------------------------------------------------
    // Declared communication ports
    // ------------------------------------------------------------------



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
    static Boolean lightweightAccessorContextMatches(
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

    static int lightweightAccessorContextOccurrence() {
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
}
