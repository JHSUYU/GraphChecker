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
import edu.uva.liftlab.graphchecker.contract.LocationId;
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

import static edu.uva.liftlab.graphchecker.smt.JsonFields.nonNull;
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

public final class ConcolicRegionRuntime {
    private static final Gson GSON = new GsonBuilder().disableHtmlEscaping().create();
    static final AtomicLong TOKEN_COUNTER = new AtomicLong();
    private static final AtomicLong ACCESSOR_CONTEXT_TOKEN_COUNTER =
            new AtomicLong();
    static final Map<Long, ActiveRegion> ACTIVE = new ConcurrentHashMap<>();
    private static final ThreadLocal<Deque<Long>> CURRENT_TOKENS =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<>();
                }
            };
    private static final ThreadLocal<Integer> OBSERVATION_PAUSE_DEPTH =
            ThreadLocal.withInitial(() -> 0);
    private static final ThreadLocal<Deque<RootInvocationFrame>>
            ROOT_INVOCATION_FRAMES = new ThreadLocal<Deque<RootInvocationFrame>>() {
        @Override
        protected Deque<RootInvocationFrame> initialValue() {
            return new ArrayDeque<>();
                }
            };
    private static final ThreadLocal<AccessorCallContext>
            CURRENT_ACCESSOR_CALL_CONTEXT = new ThreadLocal<>();
    static volatile VmExpressionTable.Store workloadExpressionStore =
            new VmExpressionTable.Store(
                    EnginePlumbing.VM_CLASSES);
    private ConcolicRegionRuntime() {
    }

    public static void pauseObservation() {
        OBSERVATION_PAUSE_DEPTH.set(OBSERVATION_PAUSE_DEPTH.get() + 1);
        try {
            engine().pausePathCondition();
        } catch (Throwable ignored) {
        }
        closeDoorWindow();
    }

    public static final int CONTAINER_BEFORE_MUTATION = 0;
    public static final int CONTAINER_AFTER_MUTATION = 1;
    public static final int CONTAINER_READ = 2;

    private static final ThreadLocal<ActiveRegion> DOOR_WINDOW =
            new ThreadLocal<>();

    static void openDoorWindow(ActiveRegion active) {
        if (!active.activation.doorsOnly || !active.basePaused) return;
        if (OBSERVATION_PAUSE_DEPTH.get() == 0) {
            RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING,
                    firstNonBlank(active.address(),
                            Long.toString(active.token)),
                    "a door window was asked for outside every woven"
                            + " observation bracket, where the engine's own"
                            + " frames would track: it is not opened, so"
                            + " this door decides nothing");
            return;
        }
        try {
            engine().resumeBase();
            active.basePaused = false;
            DOOR_WINDOW.set(active);
        } catch (Throwable ignored) {
        }
    }

    private static void closeDoorWindow() {
        ActiveRegion open = DOOR_WINDOW.get();
        if (open == null) return;
        DOOR_WINDOW.remove();
        try {
            engine().pauseBase();
            open.basePaused = true;
        } catch (Throwable ignored) {
        }
    }

    private static void releaseBasePause(ActiveRegion active) {
        if (DOOR_WINDOW.get() == active) DOOR_WINDOW.remove();
        if (!active.basePaused) return;
        try {
            engine().resumeBase();
            active.basePaused = false;
        } catch (Throwable ignored) {
        }
    }

    public static void resumeObservation() {
        int depth = OBSERVATION_PAUSE_DEPTH.get();
        if (depth <= 1) OBSERVATION_PAUSE_DEPTH.remove();
        else OBSERVATION_PAUSE_DEPTH.set(depth - 1);
        try {
            engine().resumePathCondition();
        } catch (Throwable ignored) {
        }
        if (depth <= 1) holdBasePause();
    }

    private static void holdBasePause() {
        if (DOOR_WINDOW.get() != null) return;
        ActiveRegion active = activeRegion();
        if (active == null || !active.activation.doorsOnly
                || active.basePaused || active.finished.get()) {
            return;
        }
        try {
            engine().pauseBase();
            active.basePaused = true;
        } catch (Throwable ignored) {
        }
    }

    public static long enterConfiguredSourcePhaseCallSite(
            String method, int unitIndex, String declaredCallee) {
        try {
            ActiveRegion active = activeRegion();
            long replayOwnerId = active == null ? 0L : active.token;
            return CausynthTraceRecorder.beginCall(replayOwnerId,
                    nonNull(method), unitIndex, nonNull(declaredCallee), null,
                    true);
        } catch (Throwable ignored) {
            return 0L;
        }
    }

    public static void exitConfiguredSourcePhaseCallSite(
            long invocationId, Object returnValue, String primitiveValue) {
        if (invocationId <= 0L) return;
        try {
            CausynthTraceRecorder.endCall(invocationId, returnValue,
                    nonNull(primitiveValue));
        } catch (Throwable ignored) {
        }
    }

    public static void throwConfiguredSourcePhaseCallSite(long invocationId) {
        if (invocationId <= 0L) return;
        try {
            CausynthTraceRecorder.throwCall(invocationId);
        } catch (Throwable ignored) {
        }
    }

    static ActiveRegion observingActiveRegion() {
        return OBSERVATION_PAUSE_DEPTH.get() > 0 ? null : activeRegion();
    }

    static boolean recordsHere(ActiveRegion active) {
        return OBSERVATION_PAUSE_DEPTH.get() == 0
                && !(active.activation.doorsOnly && active.basePaused);
    }

    public static long enterAccessorCallContext(
            String callerMethod, int callUnitIndex, String callSiteId,
            String declaredCallee, Object receiver) {
        try {
            ActiveRegion active = activeRegion();
            String caller = nonNull(callerMethod);
            String site = nonNull(callSiteId);
            String callee = nonNull(declaredCallee);
            if (active == null || caller.isEmpty() || callUnitIndex < 0
                    || callee.isEmpty()
                    || !site.equals(SiteId.render(caller, callUnitIndex))) {
                return 0L;
            }
            AccessorCallContext previous =
                    CURRENT_ACCESSOR_CALL_CONTEXT.get();
            if (previous != null && previous.regionToken != active.token) {
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
            return 0L;
        }
    }

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


    public static String openWorkloadSession() {
        RowRuntime.configure(configuration().resultFile);
        if (configuration().tasks.isEmpty()) {
            workloadExpressionStore = new VmExpressionTable.Store(
                    EnginePlumbing.VM_CLASSES);
            return "";
        }
        ConcolicVmBroker api = engine();
        api.requireCurrentCapabilities();
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
        workloadExpressionStore = new VmExpressionTable.Store(
                    EnginePlumbing.VM_CLASSES);
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

    private static volatile boolean admissionEnded;

    static void endAdmission() {
        admissionEnded = true;
    }

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
            config.releaseCandidate(admitted);
            return null;
        }
        return startSymbolicRegion(admitted, receiver);
    }

    private static final ThreadLocal<Map<Long, Long>> NAMED_ACTIVATIONS =
            ThreadLocal.withInitial(LinkedHashMap::new);

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
        }
    }

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
            api.pausePathCondition();
            pathConditionPaused = true;
            ActiveRegion enclosing = activeRegion();
            active = new ActiveRegion(TOKEN_COUNTER.incrementAndGet(),
                    admitted, receiver, Thread.currentThread());
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
            active.d3Address = RowRuntime.beginActivation(active.token,
                    RuntimeTraceContext.activationSource(receiver).key(),
                    admitted.regionId, admitted.taskId);
            ForcedArms.arm(active);
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
            RowRuntime.journalRegion(active.vmRegionEnterEventId,
                    active.d3Address);
            RuntimeTraceContext.View context = RuntimeTraceContext.current();
            SourceRef receiverSource = RuntimeTraceContext.sourceFor(receiver);
            if (receiverSource != null) {
                observeCausalSource(receiverSource.key());
            } else if (context.source != null
                    && RuntimeTraceContext.sameSourceIdentity(
                    admitted.sourceKey, context.source.key())) {
                observeCausalSource(context.source.key());
            }
            RootMint.symbolizeReceiverFields(active, admitted, api);
            api.resumePathCondition();
            pathConditionPaused = false;
            if (admitted.doorsOnly) RowRuntime.ranDoorsOnly(active.d3Address);
            return active;
        } catch (Throwable throwable) {
            if (active != null) {
                ACTIVE.remove(active.token);
                if (javaRegionPushed) {
                    popActiveRegion(active);
                }
                active.releaseActivation();
            }
            if (engineStarted) {
                if (pathConditionPaused) {
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

    public static long claimStart(Object carrier) {
        return RowRuntime.claimStart(carrier);
    }

    public static void endClaim(long claim) {
        RowRuntime.endClaim(claim);
    }

    public static void claimItem(Object item) {
        RowRuntime.claimItem(item);
    }

    public static long enterMethodFrame(String callSiteId, Object receiver) {
        return Identity.enterFrame(nonNull(callSiteId), receiver);
    }

    public static void exitMethodFrame(long token) {
        Identity.exitFrame(token);
    }

    public static void throwMethodFrame(long token, Throwable thrown) {
        ForcedArms.unwinding(thrown);
        Identity.exitFrame(token);
    }

    public static void startWork(String startSiteId, Object carrier,
                                 Object submittedTo) {
        RowRuntime.startWork(startSiteId, carrier, submittedTo);
    }

    public static long enterRegionEntry(String regionId, String rootMethod,
                                        Object receiver) {
        long entry = TOKEN_COUNTER.incrementAndGet();
        int depth = Identity.depth();
        int regions = Identity.regionDepth();
        String node = RuntimeTraceContext.activationSource(receiver).key();
        Identity.occurrence(node, nonNull(regionId), true);
        REGION_ENTRIES.get().push(new RegionEntry(entry, depth, regions,
                nonNull(rootMethod)));
        return entry;
    }

    public static void exitRegionEntry(long entry) {
        closeRegionEntry(entry, null);
    }

    public static void throwRegionEntry(long entry, Throwable throwable) {
        closeRegionEntry(entry, throwable);
    }

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

    public static long enterRegionFrame(String rootHookGroup,
                                        String rootMethod,
                                        Object receiver,
                                        Object[] rootArguments) {
        ConcolicTaskPlan config = configuration();
        RootInvocationFrame frame = new RootInvocationFrame(rootHookGroup,
                rootMethod);
        ROOT_INVOCATION_FRAMES.get().push(frame);
        ActiveRegion active = Identity.openedNone()
                && !LoopAccounting.bodiesAddressedHere(
                        config.loopRootOf(rootHookGroup))
                ? null
                : admitRegion(config, rootHookGroup, rootMethod, receiver,
                        rootArguments);
        frame.token = active == null ? 0L : active.token;
        return frame.token;
    }

    public static void checkLoopBackedge(
            String backedgeId, int instrumentedMaxTraversals) {
        LoopAccounting.checkBackedge(backedgeId, instrumentedMaxTraversals);
    }

    public static void checkReplayLoopBody(
            String loopId, int instrumentedMaxTraversals) {
        LoopAccounting.checkReplayBody(loopId, instrumentedMaxTraversals);
    }

    public static long enterLoopRootInvocationFrame(
            String loopRootHookGroup, String rootMethod,
            Object receiver, Object[] rootArguments) {
        return LoopAccounting.enterLoopRoot(loopRootHookGroup, rootMethod,
                receiver, rootArguments);
    }

    public static void exitLoopRootInvocationFrame(long token) {
        LoopAccounting.exitLoopRoot(token);
    }

    public static void throwLoopRootInvocationFrame(
            long token, Throwable throwable) {
        LoopAccounting.exitLoopRoot(token);
    }

    public static boolean materializeSymbolicBoolean(String name) {
        return RecordingPlant.marker(name);
    }


    public static void observeTrackedSite(String siteId,
                                          String fieldSignature,
                                          Object receiver) {
        ActiveRegion active = activeRegion();
        if (active == null || receiver == null
                || nonNull(fieldSignature).isEmpty()
                || active.activation.doorsOnly) {
            return;
        }
        try {
            engine().observeField(receiver, fieldSignature);
            active.pathRecordingStarted = true;
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    firstNonBlank(nonNull(siteId), nonNull(fieldSignature)),
                    "this access could not start the VM's version log"
                            + " for " + nonNull(fieldSignature) + ", so every"
                            + " later read of that location joins to no"
                            + " writer: " + rootCause(failure));
        }
    }

    public static void observeProvenance(String siteId, Object receiver,
                                         Object holder) {
        try {
            observeVersion(siteId, receiver, holder);
        } catch (RuntimeException fault) {
            MessageDoors.doorFault("observeProvenance " + siteId, fault);
        }
    }

    private static void observeVersion(String siteId, Object receiver,
                                       Object holder) {
        Provenance.Version version = Provenance.observe(receiver, holder,
                new boolean[1]);
        ActiveRegion active = activeRegion();
        if (active == null || active.d3Address == null) return;
        if (version == null) {
            Provenance.unregistered(nonNull(siteId), receiver);
            return;
        }
        RowRuntime.storeRead(active.d3Address, Identity.enginePosition(),
                nonNull(siteId), version.location, version.version);
        LocationId view = MessageDoors.viewOf(version.location,
                active.d3Address);
        if (view != null) {
            RowRuntime.viewRead(active.d3Address, Identity.enginePosition(),
                    nonNull(siteId) + "#VIEW", view, version.version);
        }
    }

    public static void observeTrackedContainer(String siteId,
                                               String fieldSignature,
                                               Object container,
                                               int phase) {
        boolean afterMutation = phase == CONTAINER_AFTER_MUTATION;
        ActiveRegion active = activeRegion();
        if (container == null || (active == null) != afterMutation) {
            return;
        }
        if (active != null && phase == CONTAINER_BEFORE_MUTATION
                && active.activation.doorsOnly) {
            openDoorWindow(active);
        }
        try {
            if (engine().observeContainer(container, afterMutation)
                    == ConcolicVmBroker.UNSUPPORTED_TARGET) {
                Object sorted = sortedContainer(container);
                String site = firstNonBlank(nonNull(siteId),
                        nonNull(fieldSignature));
                RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                        sorted == null ? site
                                : site + " " + ORDERED_MAP_UNMODELED + "=0",
                        nonNull(fieldSignature) + " holds a "
                                + container.getClass().getName()
                                + (sorted == null ? ""
                                : ", a sorted " + sorted.getClass().getName()
                                + " whose order and navigable views no"
                                + " model states")
                                + ", which no container model of the VM"
                                + " knows, so its state at this site is not"
                                + " versioned and a query of it decides on"
                                + " the run's contents");
            }
        } catch (Throwable failure) {
            RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                    firstNonBlank(nonNull(siteId), nonNull(fieldSignature)),
                    "this access could not start the VM's version log of the"
                            + " container " + nonNull(fieldSignature)
                            + " holds,"
                            + " so a query of it reads no version: "
                            + rootCause(failure));
        }
    }

    static final String ORDERED_MAP_UNMODELED = "ordered-map-unmodeled";
    private static final String[] BACKING_FIELDS = {"m", "c", "this$0"};

    static Object sortedContainer(Object container) {
        Object at = container;
        for (int hop = 0; at != null && hop < 4; hop++) {
            if (at instanceof java.util.SortedMap
                    || at instanceof java.util.SortedSet) {
                return at;
            }
            at = backing(at);
        }
        return null;
    }

    private static Object backing(Object view) {
        for (Class<?> type = view.getClass(); type != null
                && type.getName().startsWith("java.util.");
             type = type.getSuperclass()) {
            for (String name : BACKING_FIELDS) {
                try {
                    java.lang.reflect.Field field = type.getDeclaredField(name);
                    field.setAccessible(true);
                    return field.get(view);
                } catch (ReflectiveOperationException | RuntimeException none) {
                }
            }
        }
        return null;
    }

    public static void symbolizeArgument(long token, int argumentIndex,
                                         Object value, String primitiveValue) {
        RootMint.symbolizeArgument(token, argumentIndex, value);
    }

    public static void symbolizeMethodArgument(String method,
                                               int argumentIndex,
                                               Object value,
                                               String primitiveValue) {
        RootMint.symbolizeMethodArgument(method, argumentIndex, value);
    }

    public static Object materializeArgument(long token, int argumentIndex,
                                             Object boxedOrReference,
                                             String primitiveValue) {
        return RootMint.materializeArgument(token, argumentIndex,
                boxedOrReference);
    }

    public static Object materializeMethodArgument(String method,
                                                   int argumentIndex,
                                                   Object boxedOrReference,
                                                   String primitiveValue) {
        return RootMint.materializeMethodArgument(method, argumentIndex,
                boxedOrReference);
    }

    public static Object materializeReference(String method, int unitIndex,
                                              String local, Object value) {
        return RootMint.materializeReference(method, unitIndex, local, value);
    }

    public static Object materializePrimitive(String method, int unitIndex,
                                              String local,
                                              Object boxedValue) {
        return RootMint.materializePrimitive(method, unitIndex, local,
                boxedValue);
    }

    public static Object materializeStaticPrimitiveField(
            String method, int unitIndex, String fieldSignature,
            String fieldName, Object boxedValue) {
        return RootMint.materializeStaticPrimitiveField(method, unitIndex,
                fieldSignature, fieldName, boxedValue);
    }

    public static void materializeField(String method, int unitIndex,
                                        Object owner, String fieldSignature,
                                        String fieldName) {
        RootMint.materializeField(method, unitIndex, owner, fieldSignature,
                fieldName);
    }

    public static boolean symbolizeConfiguredSourceField(
            String sourceId, Object owner, String fieldSignature) {
        return RootMint.configuredSource(sourceId, owner, fieldSignature);
    }

    public static void readConfiguration(
            String sourceId, Object owner, String fieldSignature) {
        RootMint.configuration(sourceId, owner, fieldSignature);
    }

    static void observeCausalSource(String sourceKey) {
        ActiveRegion active = activeRegion();
        if (active == null) return;
        if (sourceKey != null && !sourceKey.isEmpty()) {
            active.observedSourceKeys.add(sourceKey);
        }
    }


    private static final String PROPAGATED_EXPRESSION_IMPORT_FAILED =
            "PROPAGATED_EXPRESSION_IMPORT_FAILED";

    static final class PropagatedExpressionImportFailure
            extends IllegalStateException {
        private static final long serialVersionUID = 1L;

        PropagatedExpressionImportFailure(String detail, Throwable cause) {
            super(detail, cause);
        }
    }

    static JsonElement engineExpression(String serialized) {
        ActiveRegion active = activeRegion();
        try {
            return expressionStore(active).importField(serialized,
                    "expression");
        } catch (RuntimeException malformed) {
            String detail = PROPAGATED_EXPRESSION_IMPORT_FAILED
                    + ": producer=" + describeImportPayload(serialized)
                    + " occurrence=" + (active == null ? "<none>"
                    : nonNull(active.activation.occurrenceId))
                    + ": " + rootCause(malformed);
            throw new PropagatedExpressionImportFailure(detail, malformed);
        }
    }

    private static String describeImportPayload(String serialized) {
        String value = nonNull(serialized);
        if (value.isEmpty()) return "<empty payload>";
        return value.length() <= 160 ? value
                : value.substring(0, 160) + "...(" + value.length() + " B)";
    }

    static VmExpressionTable.Store expressionStore(
            ActiveRegion active) {
        return active == null ? workloadExpressionStore
                : active.expressionStore;
    }

    public static void exportCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor,
                                               Object builder) {
        WireExport.exportLeaf(portId, carrier, field, descriptor, builder);
    }

    public static void builtMessage(Object builder, Object message) {
        pauseObservation();
        try {
            MessageCodec.built(builder, message);
        } finally {
            resumeObservation();
        }
    }

    public static void attachCommunicationLeaf(String portId, Object carrier,
                                               String field,
                                               String descriptor,
                                               Object receiver) {
        WireExport.attachLeaf(portId, carrier, field, descriptor, receiver);
    }

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

        public static HandoffLeafCarrier of(boolean value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.z = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(byte value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.b = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(short value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.s = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(char value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.c = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(int value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.i = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(long value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.j = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(float value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.f = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(double value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.d = value;
            return carrier;
        }

        public static HandoffLeafCarrier of(Object value) {
            HandoffLeafCarrier carrier = new HandoffLeafCarrier();
            carrier.o = value;
            return carrier;
        }

        public boolean z() {
            return z;
        }

        public byte b() {
            return b;
        }

        public short s() {
            return s;
        }

        public char c() {
            return c;
        }

        public int i() {
            return i;
        }

        public long j() {
            return j;
        }

        public float f() {
            return f;
        }

        public double d() {
            return d;
        }

        public Object o() {
            return o;
        }
    }

    static final String CARRIER_CLASS =
            "edu.uva.liftlab.graphchecker.runtime.ConcolicRegionRuntime"
                    + "$HandoffLeafCarrier";

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

    interface Declares {
        boolean declaredBy(ActiveRegion region);

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

        final class Root implements Declares {
            private final String rootId;

            Root(String rootId) {
                this.rootId = rootId;
            }

            @Override
            public boolean declaredBy(ActiveRegion region) {
                for (SymbolizeAction action : region.activation.symbolize) {
                    if (nonNull(action.symbol).equals(rootId)) return true;
                }
                for (ConfiguredSourcePhaseContract.Occurrence phase
                        : region.activation.configuredSourcePhases) {
                    if (nonNull(phase.sourceId()).equals(rootId)) {
                        return true;
                    }
                }
                return false;
            }
        }
    }

    static boolean statesTargetReach(
            boolean decided, boolean permutedOccurrence, boolean targetTest,
            int targetBranchOccurrence, int occurrence) {
        return decided && targetTest
                && (permutedOccurrence
                || targetBranchOccurrence == occurrence);
    }


    public static void exitRegionFrame(String rootHookGroup,
                                       String rootMethod) {
        try {
            RootInvocationFrame frame = popRootInvocationFrame(
                    rootHookGroup, rootMethod);
            if (frame != null && frame.token != 0L) {
                finish(frame.token, "NORMAL", "", null);
            }
        } catch (Throwable ignored) {
        }
    }

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
        }
    }

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
            return null;
        }
        frames.pop();
        Deque<Long> silenced = SILENCED.get();
        silenced.remove(Long.valueOf(frame.token));
        if (frames.isEmpty()) {
            ROOT_INVOCATION_FRAMES.remove();
            silenced.clear();
        }
        if (silenced.isEmpty()) SILENCED.remove();
        return frame;
    }

    private static final class RootInvocationFrame {
        private final String rootHookGroup;
        private final String rootMethod;
        private long token;

        private RootInvocationFrame(String rootHookGroup, String rootMethod) {
            this.rootHookGroup = rootHookGroup;
            this.rootMethod = rootMethod;
        }
    }

    public static long prepareBranch(String method, int unitIndex,
                                     String expression) {
        return BranchObservation.prepare(method, unitIndex, expression);
    }

    public static void resolveBranch(long preparedHandle, long vmEventId,
                                     String method, int unitIndex,
                                     String expression,
                                     boolean observedOutcome) {
        BranchObservation.observe(BranchDecision.binary(observedOutcome),
                preparedHandle, vmEventId, method, unitIndex, expression);
    }

    public static void resolveSwitchBranch(
            long preparedHandle, long vmEventId, String method, int unitIndex,
            String expression, String branchKind, String encodedCaseKeys,
            int observedSuccessorIndex) {
        BranchObservation.observeSwitch(preparedHandle, vmEventId,
                method, unitIndex, expression, branchKind, encodedCaseKeys,
                observedSuccessorIndex);
    }

    private static void abandonOccurrence(ActiveRegion active, String detail) {
        active.releaseActivation();
        active.abandoned = true;
        active.terminalGap = true;
        endLiveSelectedRegion();
        taskUnanswered(active.activation, detail);
    }

    static final Map<Long, ActiveRegion> STRANDED =
            new ConcurrentHashMap<>();

    private static final Object STRAND_LOCK = new Object();

    static boolean strand(ActiveRegion active) {
        synchronized (STRAND_LOCK) {
            if (!active.finished.compareAndSet(false, true)) return false;
            active.abandoned = true;
            ACTIVE.remove(active.token, active);
            STRANDED.put(active.token, active);
            return true;
        }
    }

    static void finish(long token, String exitKind,
                               String exceptionType, Throwable throwable) {
        ActiveRegion active = ownerRegion(token);
        if (active == null || !active.finished.compareAndSet(false, true)) {
            closeStranded(token);
            return;
        }
        beginSelectedResultPublication();
        boolean publicationDeferred = false;
        String diverged = ForcedArms.finished(active, exitKind,
                exceptionType);
        if (!diverged.isEmpty() && FocusedReplay.decideForced(diverged)) {
            ConcolicResultPublisher.concludeAtRefusal();
        }
        pauseObservation();
        releaseBasePause(active);
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
        releaseBasePause(stranded);
        try {
            closeOccurrence(stranded);
        } finally {
            resumeObservation();
        }
    }

    private static void judgeFinishedOccurrence(ActiveRegion active) {
        configuration().markOccurrenceClaimed(active.activation);

        if (active.replayPrefixContradicted()) {
            abandonOccurrence(active, "REPLAY_PREFIX_UNMATCHED: the"
                    + " activation contradicts its obligation's prefix: "
                    + FocusedReplay.refusal(active.d3Address));
            return;
        }
        if (active.d3Address != null
                && !active.activation.loopBodyRoot
                && !FocusedReplay.complete(active.d3Address)) {
            abandonOccurrence(active, "REPLAY_PREFIX_UNMATCHED: the"
                    + " focused occurrence closed without taking the"
                    + " decision its obligation flips");
        }
    }

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

    static void refusedResumes(ActiveRegion active, JsonObject summary) {
        long refused = JsonFields.optionalLongInteger(summary,
                "refusedObservationResumes", 0L);
        if (refused <= 0L) return;
        RowRuntime.gap(GapKind.ENGINE_FAULT, GapClass.BLOCKING,
                firstNonBlank(active.address(), Long.toString(active.token)),
                refused + " observation resume(s) in this activation found"
                        + " no observation pause above the base pause; the VM"
                        + " refused each, so the engine's pause brackets are"
                        + " unbalanced here");
    }

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
                    RowRuntime.gap(GapKind.UNSTATED_VALUE, GapClass.DIAGNOSTIC,
                            SharedStateCapture.STAGE_VERSIONS,
                            "the tracked-location read-out could not be"
                                    + " invoked, so no write version of this"
                                    + " activation is stated: "
                                    + rootCause(throwable));
                }
            }
            JsonObject summary = members(api.finish(), "aborted",
                    "abortReason", "modelGaps", "refusedObservationResumes");
            engineFinished = true;
            if (publishRows && summary != null) {
                aborted(active, summary);
                modelGaps(active, summary);
                refusedResumes(active, summary);
            }
            if (enclosingRegion != null && active.pathRecordingStarted) {
                enclosingRegion.pathRecordingStarted = true;
            }
            if (hasEnclosingRegion) {
                api.resumePathCondition();
                pathConditionPaused = false;
            }
        } catch (Throwable ignored) {
        } finally {
            if (pathConditionPaused && hasEnclosingRegion) {
                try {
                    api.resumePathCondition();
                    pathConditionPaused = false;
                } catch (Throwable ignored) {
                }
            }
            if (!engineFinished) {
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
        if (!SILENCED.get().isEmpty()) return null;
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long token = tokens.peek();
        return token == null ? null : ownerRegion(token);
    }

    private static final ThreadLocal<Deque<Long>> SILENCED =
            new ThreadLocal<Deque<Long>>() {
                @Override
                protected Deque<Long> initialValue() {
                    return new ArrayDeque<Long>();
                }
            };

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

    private static Deque<Long> innermostActiveRegionStack(
            ActiveRegion active, String violation) {
        Deque<Long> tokens = CURRENT_TOKENS.get();
        Long current = tokens.peek();
        if (current == null || current.longValue() != active.token) {
            throw new IllegalStateException(violation);
        }
        return tokens;
    }

    private static void popActiveRegion(ActiveRegion active) {
        Deque<Long> tokens = innermostActiveRegionStack(active,
                "selected region stack does not own token " + active.token);
        tokens.pop();
        if (tokens.isEmpty()) CURRENT_TOKENS.remove();
    }

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

        private boolean live() {
            ActiveRegion active = activeRegion();
            return active != null && regionToken == active.token
                    && thread == Thread.currentThread();
        }

        private boolean matches(
                String actualCallerMethod, int actualCallUnitIndex,
                String actualCallSiteId, String actualDeclaredCallee,
                Object actualFieldOwner) {
            return callerMethod.equals(nonNull(actualCallerMethod))
                    && callUnitIndex == actualCallUnitIndex
                    && callSiteId.equals(nonNull(actualCallSiteId))
                    && declaredCallee.equals(nonNull(actualDeclaredCallee))
                    && receiver == actualFieldOwner;
        }
    }

    static final class OccurrenceCounter {
        private final Map<String, Integer> occurrences =
                new LinkedHashMap<>();

        int local(String method, int unitIndex, String local) {
            return observe("LOCAL\u0000"
                    + SiteId.render(method, unitIndex)
                    + "::" + nonNull(local));
        }

        int methodArgument(String method, int argumentIndex) {
            return observe(argumentKey(method, argumentIndex));
        }

        int observedMethodArgument(String method, int argumentIndex) {
            return observed(argumentKey(method, argumentIndex));
        }

        private static String argumentKey(String method, int argumentIndex) {
            return "ARGUMENT\u0000" + nonNull(method) + "#arg" + argumentIndex;
        }

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
