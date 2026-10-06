package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.stream.JsonReader;
import com.google.gson.stream.JsonToken;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.VmExpressionTable;
import edu.uva.liftlab.graphchecker.plan.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.runtime.BranchObservation.BranchDecision;
import edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.RuntimeTask;
import edu.uva.liftlab.graphchecker.runtime.LoopAccounting.LoopBoundCut;
import edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.SharedStateReadOut;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import java.io.IOException;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.Predicate;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.safe;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicTaskPlan.configuration;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.beginLiveSelectedRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.beginSelectedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.endSelectedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.endLiveSelectedRegion;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.submitCompletedResultPublication;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicResultPublisher.taskUnanswered;
import static edu.uva.liftlab.graphchecker.runtime.ConcolicVmBroker.engine;
import static edu.uva.liftlab.graphchecker.runtime.SharedStateCapture.captureRecordedSharedState;

/**
 * Runtime bridge injected at symbolic-region roots for the second (concolic)
 * unit-test execution.
 *
 * <p>The class uses reflection for the custom {@code java.lang.System} APIs so
 * GraphChecker itself remains buildable and testable on an ordinary JDK.</p>
 */
public final class ConcolicRegionRuntime {
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    /** Shared with {@link LoopAccounting}, which mints a loop-root entry. */
    static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    /**
     * Selected activations on this thread, innermost first; mirrors the VM's
     * native region stack, since a selected helper can run inside a selected
     * caller.
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
    /** Root-invocation frames of the injected entry/exit hooks. */
    private static final ThreadLocal<Deque<RootInvocationFrame>>
            ROOT_INVOCATION_FRAMES = new ThreadLocal<Deque<RootInvocationFrame>>() {
        @Override
        protected Deque<RootInvocationFrame> initialValue() {
            return new ArrayDeque<>();
                }
            };
    private static final ThreadLocal<AccessorCallContext>
            CURRENT_ACCESSOR_CALL_CONTEXT = new ThreadLocal<>();
    /** Session this JVM opened for its workload, or zero when it opened none. */
    private static volatile long workloadSessionId;
    /**
     * Expression store of the current workload session; native expression
     * ids are session-wide, so one store serves every region.
     */
    static volatile VmExpressionTable.Store workloadExpressionStore =
            new VmExpressionTable.Store();
    private ConcolicRegionRuntime() {
    }

    /**
     * Mutes symbolic propagation before an instrumented method calls back
     * into this runtime; the VM still balances its shadow frames.  Also
     * mutes this layer's own bookkeeping (pair with {@link
     * #resumeObservation} in a finally): unmuted, GraphChecker's control
     * flow over symbolized objects lands in the workload's path condition.
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

    /** Opens the static call-site context for a configured-source hook. */
    public static long enterConfiguredSourcePhaseCallSite(
            String method, int unitIndex, String declaredCallee) {
        try {
            ActiveRegion active = activeRegion();
            long replayOwnerId = active == null ? 0L : active.token;
            return CausynthTraceRecorder.beginCall(replayOwnerId, safe(method),
                    unitIndex, safe(declaredCallee), null, true);
        } catch (Throwable ignored) {
            // Never perturb the workload; id 0 makes both close hooks no-ops.
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
            // A trace failure is not an application failure.
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
     * The innermost activation, or null while observation is muted: a hook
     * reached from GraphChecker's own bookkeeping accounts for nothing.
     */
    static ActiveRegion observingActiveRegion() {
        return OBSERVATION_PAUSE_DEPTH.get() > 0 ? null : activeRegion();
    }

    /**
     * Opens the accessor invocation selected by one activation's symbolize
     * action.  The woven token starts at zero and the exit hook always runs,
     * so unselected executions are harmless.
     */
    public static long enterAccessorCallContext(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object receiver) {
        // No index frame: the recording weaves no accessor context, so a
        // frame here would deepen the replay's execution index past the
        // recorded one.  Repeated reads are told apart by
        // Identity.eventSiteIndex instead.
        //
        // Trap: this context is NOT redundant with
        // CausynthTraceRecorder.currentCallParentSiteMatches -- the concolic
        // weave (HookCatalog.concolic()) pushes no recorder call frames, and
        // MATERIALIZE_FIELD runs in the caller before the accessor (possibly
        // a JDK body) is entered.
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
            String occurrenceKey = caller + "\n" + site + "\n" + callee;
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
            // Out of order: malformed instrumentation or a missed throw edge.
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
     * Opens the workload-wide symbolic session that outlives every region in
     * this JVM.
     *
     * @return an empty string on success, otherwise a named diagnostic
     */
    public static String openWorkloadSession() {
        // Before any admission: an export can cross a port before anything
        // is selected, and an unpublished row reads as a site that never ran.
        RowRuntime.configure(configuration().resultFile);
        if (configuration().tasks.isEmpty()) {
            workloadExpressionStore = new VmExpressionTable.Store();
            return "";
        }
        ConcolicVmBroker api = engine();
        api.requireCurrentCapabilities();
        // Guarded store sites (a PLAN output) must be installed before any
        // store; a session that cannot read them is refused by name.
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
        // The durability boundary, whichever launcher owns it.
        ConcolicResultPublisher.awaitSelectedResultPublications();
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

    private static String workloadSessionStatusName(long status) {
        if (status == 0L) return "OK";
        if (status == -1L) return "ALREADY_OPEN";
        if (status == -2L) return "NOT_OPEN";
        if (status == -3L) return "MEMBERS_REMAIN";
        if (status == -4L) return "CLOSING";
        return "UNNAMED_STATUS(" + status + ")";
    }

    /** Set once the run has ended ({@link #endAdmission}). */
    private static volatile boolean admissionEnded;

    /**
     * Ends the run's admission: no region starts after it.  The run ends
     * before its VM session does ({@code JUnitMethodRunner#exit}): cluster
     * threads outlive the test, and a region they start once the session is
     * closed opens a fresh one, where every handle the old one made is
     * foreign.
     */
    static void endAdmission() {
        admissionEnded = true;
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
        if (admissionEnded || config.tasks.isEmpty() || rootMethod == null) {
            return null;
        }
        RuntimeTask admitted = selectTask(config, rootHookGroupKey,
                rootMethod, receiver, rootArguments);
        if (admitted == null) return null;
        if (boundedLoopOccurrenceCut(admitted)) {
            // Occurrence set full: release so the next iteration re-selects;
            // this one runs concretely.
            config.releaseCandidate(admitted);
            return null;
        }
        return startSymbolicRegion(admitted, receiver);
    }

    /**
     * The activations a hop's naming started on this thread, by the hop
     * ({@link #regionNamed}).
     */
    private static final ThreadLocal<Map<Long, Long>> NAMED_ACTIVATIONS =
            ThreadLocal.withInitial(LinkedHashMap::new);

    /**
     * A hop named a standing region ({@code Identity#hopOpened}): admits the
     * task planned at that occurrence, by its whole address, and starts its
     * VM region here, mid-method.  The VM's attach shadows every frame then
     * standing with no expression (ShadowStack's constructor walks the
     * thread's frames), so the region's work before the hop is concrete
     * and stated by nothing.
     */
    static void regionNamed(OccurrenceAddress address, Object receiver,
                            long hop) {
        ConcolicTaskPlan config = configuration();
        if (admissionEnded || config.tasks.isEmpty()) return;
        RuntimeTask admitted;
        pauseObservation();
        try {
            admitted = config.selectNamed(address,
                    RuntimeTraceContext.activationSource(receiver));
        } finally {
            resumeObservation();
        }
        if (admitted == null) return;
        ActiveRegion active = startSymbolicRegion(admitted, receiver);
        if (active != null) NAMED_ACTIVATIONS.get().put(hop, active.token);
    }

    /**
     * The occurrence the hop {@code hop} named ends, by the hop's end or by
     * its region's exit ({@code thrown} when by a throw): so does the
     * activation it admitted.
     */
    static void regionUnnamed(long hop, Throwable thrown) {
        Map<Long, Long> named = NAMED_ACTIVATIONS.get();
        Long token = named.remove(hop);
        if (named.isEmpty()) NAMED_ACTIVATIONS.remove();
        if (token == null) return;
        try {
            if (thrown == null) {
                finish(token, "NORMAL", "", null);
            } else {
                finishThrown(token, thrown);
            }
        } catch (Throwable ignored) {
            // Every stage inside #finish states its own refusal.
        }
    }

    /**
     * Decides which planned occurrence this root invocation admits, muted:
     * the selection is GraphChecker control flow over workload objects.
     */
    private static RuntimeTask selectTask(ConcolicTaskPlan config,
                                          String rootHookGroupKey,
                                          String rootMethod,
                                          Object receiver,
                                          Object[] rootArguments) {
        pauseObservation();
        try {
            return config.select(rootHookGroupKey, rootMethod, receiver,
                    rootArguments);
        } finally {
            resumeObservation();
        }
    }

    /**
     * Whether this admission is a loop-body region whose captured occurrence
     * set is already full (K_L).  If so the marker row is written once and
     * the iteration runs concretely, with no VM region or capture.
     */
    private static boolean boundedLoopOccurrenceCut(RuntimeTask admitted) {
        if (!admitted.cutsBoundedLoopOccurrence()) return false;
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
            // Setup is bookkeeping.
            api.pausePathCondition();
            pathConditionPaused = true;
            ActiveRegion enclosing = activeRegion();
            active = new ActiveRegion(TOKEN_COUNTER.incrementAndGet(),
                    admitted, receiver, Thread.currentThread());
            // A nested region inherits its caller's symbolic state, so its
            // branches record even if it mints no root of its own; a region
            // reading tracked state records from entry (its reads are
            // versions another occurrence wrote).
            if (admitted.readsTrackedState
                    || enclosing != null && enclosing.pathRecordingStarted) {
                active.pathRecordingStarted = true;
            }
            active.claimActivation();
            RowRuntime.configure(configuration().resultFile);
            if (configuration().answeredByShape(admitted)) {
                RowRuntime.answered(Identity.answer(admitted.address),
                        admitted.address);
            }
            // The node it RAN on, by the function its admission and the
            // recording both addressed it with; never the planned node.
            active.d3Address = RowRuntime.beginActivation(active.token,
                    RuntimeTraceContext.activationSource(receiver).key(),
                    admitted.regionId, admitted.taskId);
            ACTIVE.put(active.token, active);
            pushActiveRegion(active);
            javaRegionPushed = true;
            if (api.currentContextId() <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no context id");
            }
            active.vmRegionEnterEventId = api.currentRegionEnterEventId();
            if (active.vmRegionEnterEventId <= 0L) {
                throw new IllegalStateException(
                        "custom concolic engine returned no region-entry "
                                + "event id");
            }
            // Journals this activation's frame under its region-entry id so
            // logged events get their frames (FrameJournal).  Never evicted
            // here: publication is asynchronous and an enclosing activation
            // may still publish under this id -- a bounded leak.
            RowRuntime.journalRegion(active.vmRegionEnterEventId,
                    active.d3Address);
            // A delivery may have set the causal source just before entry.
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            SourceRef receiverSource = RuntimeTraceContext.sourceFor(receiver);
            if (receiverSource != null) {
                observeCausalSource(receiverSource.key());
            } else if (context.source != null
                    && RuntimeTraceContext.sameSourceIdentity(
                    admitted.sourceKey, context.source.key())) {
                observeCausalSource(context.source.key());
            }
            // The declared entry setup.
            RootMint.symbolizeReceiverFields(active, admitted, api);
            api.resumePathCondition();
            pathConditionPaused = false;
            return active;
        } catch (Throwable throwable) {
            if (active != null) {
                ACTIVE.remove(active.token);
                // The index region is the entry hook's to unwind
                // (#closeRegionEntry), not this method's.
                if (javaRegionPushed) {
                    popActiveRegion(active);
                }
                active.releaseActivation();
            }
            if (engineStarted) {
                if (pathConditionPaused) {
                    // Best effort; cleanupAfterFailure owns the real cleanup.
                    try {
                        api.resumePathCondition();
                    } catch (Throwable ignored) {
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

    /**
     * Takes the execution-index frame filed for the work running here.
     * Woven at the entry of every functional method a start hands to a
     * thread ({@code WorkStartSites.entersWork}) in both passes, before the
     * method's level; the receiver is the carrier the start was filed under.
     *
     * @return what ends the claim when the work returns ({@link #endClaim})
     */
    public static long claimStart(Object carrier) {
        return RowRuntime.claimStart(carrier);
    }

    /** Ends a work entry's claim, after its level, at every exit. */
    public static void endClaim(long claim) {
        RowRuntime.endClaim(claim);
    }

    /** Takes the start filed for an item taken off a queue. */
    public static void claimItem(Object item) {
        RowRuntime.claimItem(item);
    }

    /**
     * Enters the execution-index level of one application-scope method: the
     * replay's half of the one frame rule, same hook and scope as
     * {@code CausynthTraceRecorder.enterMethodFrame}.  The node is not read
     * here (a lock per call); a thread's events inherit its start's node.
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterMethodFrame(String callSiteId, Object receiver) {
        return Identity.enterFrame(safe(callSiteId), receiver);
    }

    /** Leaves the level {@link #enterMethodFrame} opened. */
    public static void exitMethodFrame(long token) {
        Identity.exitFrame(token);
    }

    /** The exceptional edge of {@link #enterMethodFrame}. */
    public static void throwMethodFrame(long token, Throwable thrown) {
        Identity.exitFrame(token);
    }

    /**
     * Files the execution-index frame of one work start (thread start,
     * executor submit, fork).  Nothing is pushed on the starter; the started
     * work claims the frame ({@link #claimStart}).
     */
    public static void startWork(String startSiteId, Object carrier) {
        RowRuntime.startWork(startSiteId, carrier);
    }

    /**
     * Opens the execution-index region of every skeleton root, selected or
     * not, exactly as the recording does ({@code
     * CausynthTraceRecorder#enterMethod}); otherwise the replay stands on a
     * different frame stack and names a different occurrence.  Frames and
     * address only -- activation rows belong to planned occurrences.
     *
     * <p>Whether the entry opens an occurrence or folds into the running one
     * is {@code Identity#fold}'s decision in both passes (paper SS3.1.2).
     * The push is unconditional, so the balance check sees the same
     * stacks.</p>
     */
    public static long enterRegionEntry(String regionId, String rootMethod,
                                        Object receiver) {
        // No claim here: work claims its start frame earlier (#claimStart).
        long entry = TOKEN_COUNTER.incrementAndGet();
        int depth = Identity.depth();
        int regions = Identity.regionDepth();
        // No frame here: the frame hook at this same entry already opened it.
        String node = RuntimeTraceContext.activationSource(receiver).key();
        Identity.occurrence(node, safe(regionId), true);
        REGION_ENTRIES.get().push(new RegionEntry(entry, depth, regions,
                safe(rootMethod)));
        return entry;
    }

    /** Closes the entry {@code entry} opened, and only that entry. */
    public static void exitRegionEntry(long entry) {
        closeRegionEntry(entry, null);
    }

    /** The exceptional edge of {@link #enterRegionEntry}. */
    public static void throwRegionEntry(long entry, Throwable throwable) {
        closeRegionEntry(entry, throwable);
    }

    /** One open region entry: its token, the depths it opened at, its root. */
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
     * Closes the entry the token owns and every entry a missing exit left
     * above it.  The token is a local of the entry's workload frame, so push
     * and pop pair without guessing.  A leaked entry is refused BLOCKING:
     * every later row would carry the wrong occurrence.
     */
    private static void closeRegionEntry(long entry, Throwable thrown) {
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
            Identity.regionExit(top.token == entry ? thrown : null);
            if (top.token == entry) break;
        }
        if (open.isEmpty()) REGION_ENTRIES.remove();
        int depth = Identity.depth();
        int regions = Identity.regionDepth();
        // Both index stacks must close where they opened.  An unbalanced
        // region stack silently rebases later addresses rather than breaking
        // one.
        if (depth != mine.depthAtOpen) {
            RowRuntime.gap(GapKind.FRAME_UNBALANCED, GapClass.BLOCKING,
                    mine.rootMethod,
                    "this activation closed at execution-index depth "
                            + depth + " and opened at " + mine.depthAtOpen
                            + "; the innermost frame left standing is "
                            + Identity.innermostFrame());
        } else if (regions != mine.regionsAtOpen) {
            String standing = Identity.innermostRegion();
            RowRuntime.gap(GapKind.FRAME_UNBALANCED, GapClass.BLOCKING,
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

    /**
     * Instrumentation-facing root entry: ONE per root hook group
     * ({@code ExecutionTask#rootHookGroup}), which offers each invocation to
     * every task of the group ({@link ConcolicTaskPlan#select}).
     */
    public static long enterRegionFrame(String rootHookGroup,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        RootInvocationFrame frame = new RootInvocationFrame(rootHookGroup,
                rootMethod);
        ROOT_INVOCATION_FRAMES.get().push(frame);
        // No index frame here: the entry hook owns it (#enterRegionEntry).
        //
        // IDENTITY §1 -- an entry that opened no occurrence starts no
        // activation: a fold (I1) is a call inside the running occurrence,
        // and a second activation would give one address two rows; unnamed
        // work has no address of its own (Identity#occurrence).  The
        // tokenless frame still pairs the exit.
        // Exception: a LOOP_BODY_ROOT body is an iteration of the loop-root
        // occurrence, not a region entry (LoopAccounting#bodiesAddressedHere).
        // Trap: loop contexts are keyed by the group's loop root, not by
        // the group.
        ActiveRegion active = Identity.openedNone()
                && !LoopAccounting.bodiesAddressedHere(
                        config.loopRootOf(rootHookGroup))
                ? null
                : admitRegion(config, rootHookGroup, rootMethod, receiver,
                        rootArguments);
        frame.token = active == null ? 0L : active.token;
        return frame.token;
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

    /**
     * Opens the enclosing call that addresses LOOP_BODY_ROOT iterations: ONE
     * entry per loop root ({@code ExecutionTask#loopRootHookGroup}), for
     * every loop-body task rooted there.
     */
    public static long enterLoopRootInvocationFrame(
            String loopRootHookGroup, String rootMethod,
            Object receiver, Object[] rootArguments) {
        return LoopAccounting.enterLoopRoot(loopRootHookGroup, rootMethod,
                receiver, rootArguments);
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
     * A fault marker's ({@code Debug.makeSymbolicBoolean}) polarity: {@code
     * false}, as recorded, but where a native reproduction's plant names this
     * call ({@link RecordingPlant}).  A replay's polarity is planted by the
     * local-definition mint ({@link RootMint#materializePrimitive}), not
     * here.  External caller (workload trees); keep the name.
     */
    public static boolean materializeSymbolicBoolean(String name) {
        return RecordingPlant.marker(name);
    }


    /**
     * Starts versioning a tracked cell at this access, unless its log
     * already stands.
     *
     * <p>The VM logs a location only from its first symbolic value, so
     * earlier concrete stores leave no writer for a later read to join.
     * This attaches the current value as a concrete leaf (no new input),
     * after which a store -- including an Atomic RMW, linearized by the VM
     * -- publishes a version, and a read states the version it saw, the
     * INITIAL one when no store of the window came first.  PLAN decides
     * which sites are observed.</p>
     */
    public static void observeTrackedSite(String siteId,
                                          String fieldSignature,
                                          Object receiver) {
        ActiveRegion active = activeRegion();
        if (active == null || receiver == null
                || safe(fieldSignature).isEmpty()) {
            return;
        }
        try {
            engine().observeField(receiver, fieldSignature);
            active.pathRecordingStarted = true;
        } catch (Throwable failure) {
            // Not one lost row: every later read of the cell joins nothing.
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    firstNonBlank(safe(siteId), safe(fieldSignature)),
                    "this access could not start the VM's version log"
                            + " for " + safe(fieldSignature) + ", so every"
                            + " later read of that location joins to no"
                            + " writer: " + rootCause(failure));
        }
    }

    /**
     * Starts versioning the state of the container a tracked cell holds, at
     * a read of the cell (the referent it returned) or before a container
     * mutation through it (the call's receiver), unless its log already
     * stands (SYMBOL-SCOPE §5.2); just after a mutation, on a thread outside
     * every region, marks a standing log incomplete instead.
     *
     * <p>A container a field holds is mutated in place; while its contents
     * stay concrete nothing starts its log, so a query of it names no
     * version and no mutation is a writer to re-pair it with.  After this,
     * every modeled mutation is a version and every query reads one.
     * Outside every region a mutation runs as bytecode no model sees: the VM
     * marks the log after it, so a log another thread started meanwhile is
     * marked as well.  A value that is no container the VM models is named
     * once per site.  PLAN decides which sites are observed.</p>
     */
    public static void observeTrackedContainer(String siteId,
                                               String fieldSignature,
                                               Object container,
                                               boolean afterMutation) {
        // A region thread starts the log before; one outside every region
        // marks it after.
        if (container == null || (activeRegion() == null) != afterMutation) {
            return;
        }
        try {
            if (engine().observeContainer(container, afterMutation)
                    == ConcolicVmBroker.UNSUPPORTED_TARGET) {
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        firstNonBlank(safe(siteId), safe(fieldSignature)),
                        safe(fieldSignature) + " holds a "
                                + container.getClass().getName() + ", which"
                                + " no container model of the VM knows, so"
                                + " its state at this site is not versioned"
                                + " and a query of it reads no version");
            }
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    firstNonBlank(safe(siteId), safe(fieldSignature)),
                    "this access could not start the VM's version log of the"
                            + " container " + safe(fieldSignature) + " holds,"
                            + " so a query of it reads no version: "
                            + rootCause(failure));
        }
    }

    /**
     * Called once per Java argument immediately after
     * {@link #enterRegionFrame}.
     */
    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        RootMint.symbolizeArgument(token, argumentIndex, value);
    }

    /** Symbolizes one scheduler-selected helper-method argument in-region. */
    public static void symbolizeMethodArgument(String method,
                                               int argumentIndex,
                                               Object value,
                                               String primitiveValue) {
        RootMint.symbolizeMethodArgument(method, argumentIndex, value);
    }

    /** Mints the declared root argument before Java control flow consumes it. */
    public static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        return RootMint.materializeArgument(token, argumentIndex,
                boxedOrReference);
    }

    /** Mints a declared live-in at an exact in-region helper parameter. */
    public static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
        return RootMint.materializeMethodArgument(method, argumentIndex,
                boxedOrReference);
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
     * Mints one symbol for one entry of a declared mint site.  External
     * caller ({@code CausynthSymbolicSource}, see
     * src/test/resources/external-callers.txt).
     */
    public static boolean symbolizeConfiguredSourceField(
            String sourceId, Object owner, String fieldSignature) {
        return RootMint.configuredSource(sourceId, owner, fieldSignature);
    }

    /** The engine's configuration read, woven before a configuration
     *  field's {@code getfield} (SYMBOL-SCOPE §4.3); it names a failure
     *  and never throws into the workload's own read. */
    public static void readConfiguration(
            String sourceId, Object owner, String fieldSignature) {
        RootMint.configuration(sourceId, owner, fieldSignature);
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
     * The name of an unreadable propagated producer expression.
     *
     * <p>An import failure is not "nothing propagated": treating it so
     * mints a fresh unconstrained root the recording never had.  It travels
     * as its own exception; no caller mints on it, and the importer refuses
     * the summary as {@code UNRESOLVED_INPUT}.</p>
     */
    private static final String PROPAGATED_EXPRESSION_IMPORT_FAILED =
            "PROPAGATED_EXPRESSION_IMPORT_FAILED";

    /**
     * A propagated producer expression this replay could not import; its own
     * type so {@code null} keeps meaning "no expression".
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
            return expressionStore(active).importField(serialized,
                    "expression");
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
    private static String describeImportPayload(String serialized) {
        String value = safe(serialized);
        if (value.isEmpty()) return "<empty payload>";
        return value.length() <= 160 ? value
                : value.substring(0, 160) + "...(" + value.length() + " B)";
    }

    /** One page of a paged VM read-out, record by record, in the store an
     *  activation's expressions import into
     *  ({@link VmExpressionTable.Store#importRecords}). */
    static JsonObject decodeVmRecords(String page, String records,
                                      ActiveRegion active,
                                      Predicate<JsonObject> admit,
                                      Consumer<JsonElement> each) {
        return expressionStore(active).importRecords(page, records, admit,
                each);
    }

    /** The store an activation's expressions import into. */
    private static VmExpressionTable.Store expressionStore(
            ActiveRegion active) {
        return active == null ? workloadExpressionStore
                : active.expressionStore;
    }

    /**
     * Opens the frame around one message instance being serialized; it
     * separates the many values that cross one declared port.
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
     * The instance field a declared port crosses on.  Its binary name is
     * woven by {@code CausynthPipeline}; do not move or rename.
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

    /**
     * The innermost live region whose own plan declares {@code what}: the
     * runtime counterpart of {@code StaticScopeMap.holders}, used for attach
     * consumers, handoff rows and root mints alike.
     *
     * <p>If none declares it, the innermost live region carries the row and
     * the unplanned execution is reported.</p>
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
                return region.activation.attachSite(portId) != null;
            }
        }

        /**
         * A root the plan names as a symbolic input of this region, under
         * either spelling: a SYMBOLIC action's symbol or a configured
         * source's PUBLISH phase.
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
                    if (safe(phase.sourceId()).equals(rootId)) {
                        return true;
                    }
                }
                return false;
            }
        }
    }

    /**
     * Whether this decision is the declared target event of the addressed
     * occurrence: the planned site decided at the planned activation.
     * Nothing else -- not whether the predicate was symbolic nor the
     * outcome; a concrete target branch is still reached.
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
            boolean decided, boolean permutedOccurrence, boolean targetTest,
            int targetBranchOccurrence, int occurrence) {
        return decided && targetTest
                && (permutedOccurrence
                || targetBranchOccurrence == occurrence);
    }


    /**
     * Normal-return cleanup of an injected root.  No-throw: a hook must not
     * turn a return into an exception.
     */
    public static void exitRegionFrame(String rootHookGroup,
                                       String rootMethod) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    rootHookGroup, rootMethod);
            if (frame != null && frame.token != 0L) {
                finish(frame.token, "NORMAL", "", null);
            }
        } catch (Throwable ignored) {
            // Deliberate: every stage inside #finish states its own refusal.
        }
    }

    /**
     * Exceptional cleanup for the synthetic catch-all, which rethrows the
     * original; failures here are swallowed so they cannot replace it.
     */
    public static void throwRegionFrame(String rootHookGroup,
                                        String rootMethod,
                                        Throwable throwable) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    rootHookGroup, rootMethod);
            if (frame != null && frame.token != 0L) {
                finishThrown(frame.token, throwable);
            }
        } catch (Throwable ignored) {
            // Keep the program's throwable; see #exitRegionFrame.
        }
    }

    /** Ends the activation {@code token} by a throw: a bound's cut is CUT. */
    private static void finishThrown(long token, Throwable throwable) {
        if (throwable instanceof LoopBoundCut) {
            finish(token, "CUT", "", throwable);
        } else {
            finish(token, "THROW", throwable == null ? ""
                    : throwable.getClass().getName(), throwable);
        }
    }

    private static RootInvocationFrame popRootInvocationFrame(
            String rootHookGroup, String rootMethod) {
        Deque<RootInvocationFrame> frames = ROOT_INVOCATION_FRAMES.get();
        RootInvocationFrame frame = frames.peek();
        if (frame == null) {
            ROOT_INVOCATION_FRAMES.remove();
            SILENCED.remove();
            return null;
        }
        boolean matches = Objects.equals(frame.rootHookGroup,
                rootHookGroup)
                && Objects.equals(frame.rootMethod, rootMethod);
        if (!matches) {
            // Never guess ownership, never close an outer frame.
            return null;
        }
        frames.pop();
        // The frame returns, so its silenced activation (I3) is over.
        Deque<Long> silenced = SILENCED.get();
        silenced.remove(Long.valueOf(frame.token));
        if (frames.isEmpty()) {
            ROOT_INVOCATION_FRAMES.remove();
            // A leaked token would silence this thread for good.
            silenced.clear();
        }
        if (silenced.isEmpty()) SILENCED.remove();
        return frame;
    }

    /** One woven root entry's invocation, and the activation it admitted
     *  (0: none). */
    private static final class RootInvocationFrame {
        private final String rootHookGroup;
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String rootHookGroup, String rootMethod) {
            this.rootHookGroup = rootHookGroup;
            this.rootMethod = rootMethod;
        }
    }

    /** Reserves a VM-attested branch event before the original conditional. */
    public static long prepareBranch(String method, int unitIndex,
                                     String expression) {
        return BranchObservation.prepare(method, unitIndex, expression);
    }

    /**
     * Records a binary decision under the native marker's event id, on the
     * arm the branch took: an observation, which never steers the run.
     */
    public static void resolveBranch(long preparedHandle, long vmEventId,
                                     String method, int unitIndex,
                                     String expression,
                                     boolean observedOutcome) {
        BranchObservation.observe(BranchDecision.binary(observedOutcome),
                preparedHandle, vmEventId, method, unitIndex, expression);
    }

    /** Exact multiway counterpart of {@link #resolveBranch}. */
    public static void resolveSwitchBranch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        BranchObservation.observeSwitch(preparedHandle, vmEventId,
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

    /**
     * Activations the end of the run settled while their roots still ran
     * ({@code ConcolicResultPublisher#strandWithoutTerminal}), by token.
     */
    static final Map<Long, ActiveRegion> STRANDED =
            new ConcurrentHashMap<>();

    /** Makes finishing and stranding one step each ({@link #strand}). */
    private static final Object STRAND_LOCK = new Object();

    /**
     * Takes a live activation out of the run, settled without its terminal,
     * in one step: finished, abandoned and moved to {@link #STRANDED}
     * together, so its own terminal either wins first (and the activation
     * ends as usual) or finds it stranded.  Its VM region is its thread's
     * (the VM closes a region on the thread that opened it), so the
     * terminal that thread still reaches closes it ({@link #finish}).
     *
     * @return whether it was stranded, rather than already finished
     */
    static boolean strand(ActiveRegion active) {
        synchronized (STRAND_LOCK) {
            if (!active.finished.compareAndSet(false, true)) return false;
            active.abandoned = true;
            ACTIVE.remove(active.token, active);
            STRANDED.put(active.token, active);
            return true;
        }
    }

    /** Ends whichever selected occurrence owns {@code token}. */
    static void finish(long token, String exitKind,
                               String exceptionType, Throwable throwable) {
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.finished.compareAndSet(false, true)) {
            // Stranded, or being stranded now: its VM region is still ours.
            closeStranded(token);
            return;
        }
        beginSelectedResultPublication();
        boolean publicationDeferred = false;
        // Judgement and publication are bookkeeping: muted until VM close.
        pauseObservation();
        try {
            try {
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
            resumeObservation();
            if (!publicationDeferred) endSelectedResultPublication();
        }
    }

    /**
     * A stranded activation's own terminal: its VM region closes on its
     * thread, and nothing more publishes (the strand published its mints).
     */
    static void closeStranded(long token) {
        ActiveRegion stranded;
        synchronized (STRAND_LOCK) {
            stranded = STRANDED.get(token);
            if (stranded == null
                    || stranded.thread != Thread.currentThread()) {
                return;
            }
            STRANDED.remove(token);
        }
        pauseObservation();
        try {
            closeOccurrence(stranded);
        } finally {
            resumeObservation();
        }
    }

    /** The admission gates a finished occurrence must pass to publish. */
    private static void judgeFinishedOccurrence(ActiveRegion active) {
        // Claimed: it was admitted by its whole address, node included, at
        // entry (ConcolicTaskPlan#refusal), and nothing it entered since
        // re-attributes it.  A close-time recheck against the sources its
        // frames published was the replay half of the planner's frame-stamp
        // rule; it dropped the q13 dzup target.  A later rejection owns the
        // sole diagnostic, so it is not also reported as unmatched at
        // termination.  An activation missing the target event still
        // publishes, with targetReached:false.
        configuration().markOccurrenceClaimed(active.activation);

        if (active.replayPrefixContradicted()) {
            abandonOccurrence(active, "REPLAY_PREFIX_UNMATCHED: the"
                    + " activation contradicts its obligation's prefix: "
                    + FocusedReplay.refusal(active.d3Address));
            return;
        }
        // Completeness is asked only of an occurrence this terminal ENDS.
        // Trap: a LOOP_BODY_ROOT body is one iteration of a shared address;
        // asking per body abandons every body before the flip, and that gap
        // turns the whole session NOT_ADMITTED.  A wrong arm is still refused
        // above; "no flip at all" is FocusedReplay#results' end-of-run check.
        if (active.d3Address != null
                && !active.activation.loopBodyRoot
                && !FocusedReplay.complete(active.d3Address)) {
            // Not contradicted (above), so no refusal to name: it closed
            // before reaching the decision.
            abandonOccurrence(active, "REPLAY_PREFIX_UNMATCHED: the"
                    + " focused occurrence closed without taking the"
                    + " decision its obligation flips");
        }
    }

    /**
     * Names an activation the VM aborted (its {@code abortReason}: a
     * container operation it does not model, a shadow stack out of frames):
     * the thread ran on concretely from there, so its decisions stop and the
     * published path is a prefix nobody stated.  BLOCKING, never silent.
     */
    private static void aborted(ActiveRegion active, JsonObject region) {
        if (!JsonFields.optionalBool(region, "aborted", false)) return;
        RowRuntime.gap(GapKind.UNATTESTED_ARM, GapClass.BLOCKING,
                firstNonBlank(active.address(), Long.toString(active.token)),
                "the VM aborted this activation's symbolic execution ("
                        + firstNonBlank(JsonFields.optionalString(region,
                        "abortReason"), "no reason stated") + "), so every"
                        + " decision it took afterwards is unrecorded and the"
                        + " published path is a prefix nobody stated");
    }

    /**
     * What a VM model ran on the run's own values though symbolic content
     * reached it (VM.md §4: a stream pipeline it could not state), each a
     * DIAGNOSTIC gap named by the model's reason and the call's site, so a
     * chain missing there is diagnosable.  Its subject is no occurrence
     * address, so it is no frame (SmtLowering#frames).
     */
    private static void modelGaps(ActiveRegion active, JsonObject summary) {
        for (JsonElement gap : JsonFields.array(summary, "modelGaps")) {
            if (!gap.isJsonObject()) continue;
            JsonObject named = gap.getAsJsonObject();
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    JsonFields.optionalString(named, "name"),
                    "at " + JsonFields.optionalString(named, "site")
                            + " in " + firstNonBlank(active.address(),
                            Long.toString(active.token)) + ": the VM ran"
                            + " this call on the run's own values though"
                            + " symbolic content reached it, so what it"
                            + " computed is stated only in part");
        }
    }

    /**
     * Reads one occurrence and closes its VM region on the owner thread;
     * decoding and publication go to the daemon pool.
     *
     * @return true only when the publication executor owns the in-flight
     *         publication counter
     */
    private static boolean closeOccurrence(ActiveRegion active) {
        if (!active.beginClose()) return false;
        silenceStillRunningFrame(active);
        Iterator<Long> stack = innermostActiveRegionStack(active,
                "selected regions must close in strict LIFO order")
                .iterator();
        stack.next();
        boolean hasEnclosingRegion = stack.hasNext();
        ActiveRegion enclosingRegion = hasEnclosingRegion
                ? ownerRegion(stack.next()) : null;
        ConcolicVmBroker api = engine();
        boolean engineFinished = false;
        boolean pathConditionPaused = false;
        SharedStateReadOut sharedState = null;
        boolean publishRows = false;
        try {
            api.pausePathCondition();
            pathConditionPaused = true;
            if (!active.abandoned) {
                publishRows = true;
                try {
                    sharedState = captureRecordedSharedState(active, api);
                } catch (Throwable throwable) {
                    // An unread write log leaves its locations unjoinable.
                    RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            SharedStateCapture.STAGE_VERSIONS,
                            "the tracked-location read-out could not be"
                                    + " invoked, so no write version of this"
                                    + " activation is stated: "
                                    + rootCause(throwable));
                }
            }
            // What the summary states that is read; the rest is skipped.
            JsonObject summary = members(api.finish(), "aborted",
                    "abortReason", "modelGaps");
            engineFinished = true;
            if (publishRows && summary != null) {
                aborted(active, summary);
                modelGaps(active, summary);
            }
            // Symbolic values flow back to the caller, so open its gate too.
            if (enclosingRegion != null && active.pathRecordingStarted) {
                enclosingRegion.pathRecordingStarted = true;
            }
            // An inner finish leaves the caller's context paused; undo it.
            // An outermost finish detached the context.
            if (hasEnclosingRegion) {
                api.resumePathCondition();
                pathConditionPaused = false;
            }
        } catch (Throwable ignored) {
            // The failing stage filed its own gap; the rest still publishes.
        } finally {
            if (pathConditionPaused && hasEnclosingRegion) {
                try {
                    api.resumePathCondition();
                    pathConditionPaused = false;
                } catch (Throwable ignored) {
                }
            }
            if (!engineFinished) {
                // Trap: a failed finish may already have popped this region;
                // clean up only if the VM's current region is still ours.
                try {
                    if (api.currentRegionEnterEventId()
                            == active.vmRegionEnterEventId) {
                        api.cleanupAfterFailure();
                    }
                } catch (Throwable ignored) {
                }
            }
            ACTIVE.remove(active.token, active);
            popActiveRegion(active);
            if (!active.abandoned) endLiveSelectedRegion();
        }
        if (!publishRows) {
            // The path is withheld, but its mints are published: other
            // activations' expressions already use those symbols.
            RowPublication.publishMints(active);
            configuration().releaseCandidate(active.activation);
            if (active.terminalGap && !active.activation.loopBodyRoot) {
                active.activation.reserveCompletedEvidence();
            }
            return false;
        }
        return submitCompletedResultPublication(active, sharedState);
    }


    static ActiveRegion activeRegion() {
        // I3: see #silenceStillRunningFrame.
        if (!SILENCED.get().isEmpty()) return null;
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long token = tokens.peek();
        return token == null ? null : ownerRegion(token);
    }

    /**
     * Activations that ended while their Java frame kept running; each is
     * dropped when that frame returns ({@link #popRootInvocationFrame}).
     */
    private static final ThreadLocal<Deque<Long>> SILENCED =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<Long>();
                }
            };

    /**
     * I3 -- an activation ended from inside its own frame (prefix
     * contradiction, spent budget) hands the rest of that frame to nobody.
     * Otherwise its later branches, mints and exports would be recorded on
     * the enclosing activation, which did not perform them.  Only while the
     * frame is still open.
     */
    private static void silenceStillRunningFrame(ActiveRegion active) {
        for (RootInvocationFrame open : ROOT_INVOCATION_FRAMES.get()) {
            if (open.token != active.token) continue;
            SILENCED.get().push(Long.valueOf(active.token));
            return;
        }
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

    /** Pops the exact innermost activation; an ownership mismatch is fatal. */
    private static void popActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = innermostActiveRegionStack(active,
                "selected region stack does not own token " + active.token);
        tokens.pop();
        if (tokens.isEmpty()) CURRENT_TOKENS.remove();
        // No index-region pop here: the entry hook owns that pair
        // (#enterRegionEntry / #closeRegionEntry).  A pop here would close
        // the ENCLOSING region and silently renumber its later frames.
    }

    /**
     * Hands the VM event clock ({@link ConcolicVmBroker}) to the frame
     * journal; idempotent, called at every region start.
     */
    private static void installEventClock(final ConcolicVmBroker api) {
        Identity.clock(new FrameJournal.Clock() {
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
        if (!context.live()) {
            CURRENT_ACCESSOR_CALL_CONTEXT.remove();
            return Boolean.FALSE;
        }
        return context.matches(callerMethod, callUnitIndex, callSiteId,
                declaredCallee, fieldOwner);
    }

    static int lightweightAccessorContextOccurrence() {
        AccessorCallContext context = CURRENT_ACCESSOR_CALL_CONTEXT.get();
        return context == null || !context.live() ? -1 : context.occurrence;
    }

    static ActiveRegion ownerRegion(long token) {
        ActiveRegion active = ACTIVE.get(token);
        return active != null && active.thread == Thread.currentThread()
                ? active : null;
    }

    /**
     * The members {@code names} of one VM read-out (a region summary, a
     * read-out page's header), streamed off its top level: every other
     * member is skipped, never built, and the reading stops once each named
     * one is read (a page's header sits behind its records).  A blank
     * read-out states none; null when it is no JSON object.
     */
    static JsonObject members(String serialized, String... names) {
        JsonObject read = new JsonObject();
        if (serialized == null || serialized.trim().isEmpty()) return read;
        Set<String> wanted = new HashSet<String>(Arrays.asList(names));
        try {
            JsonReader reader = new JsonReader(new StringReader(serialized));
            reader.setLenient(true);
            if (reader.peek() != JsonToken.BEGIN_OBJECT) return null;
            reader.beginObject();
            while (reader.hasNext() && read.size() < wanted.size()) {
                String name = reader.nextName();
                if (wanted.contains(name) && !read.has(name)) {
                    read.add(name, JsonParser.parseReader(reader));
                } else {
                    reader.skipValue();
                }
            }
            return read;
        } catch (IOException | RuntimeException malformed) {
            return null;
        }
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
     * A configured source's recorded value, spelled as the ledger spells a
     * manual root's {@code primitiveValue}; empty for a non-scalar.
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

        /** Opened by the live activation, on this thread. */
        private boolean live() {
            ActiveRegion active = activeRegion();
            return active != null && regionToken == active.token
                    && thread == Thread.currentThread();
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
     * Activation-local ordinals of one hook's repeated executions, so no
     * process-global counter becomes replay identity.
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
            return observe(argumentKey(method, argumentIndex));
        }

        int observedMethodArgument(String method, int argumentIndex) {
            return observed(argumentKey(method, argumentIndex));
        }

        private static String argumentKey(String method, int argumentIndex) {
            return "ARGUMENT\u0000" + safe(method) + "#arg" + argumentIndex;
        }

        /**
         * One read site's occurrences.  {@code SiteId.render}, not {@code
         * SiteId.of}: an accessor site may carry unit index {@code -1}.
         */
        int field(String method, int unitIndex) {
            return observe("FIELD\u0000"
                    + SiteId.render(method, unitIndex));
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
