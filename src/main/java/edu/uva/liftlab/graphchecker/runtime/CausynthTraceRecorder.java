package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import com.google.gson.JsonElement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.plan.DeclaredSymbolicInputs;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
import edu.uva.liftlab.graphchecker.plan.WorkStartSites;
import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayDeque;
import java.util.ArrayList;
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
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;

import static edu.uva.liftlab.graphchecker.smt.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.objectWithoutNulls;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalBool;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalInteger;
import static edu.uva.liftlab.graphchecker.smt.JsonFields.optionalString;

public final class CausynthTraceRecorder {
    private static final Object LOCK = new Object();
    private static final AtomicBoolean INITIALIZED = new AtomicBoolean();
    private static final AtomicLong EVENT_COUNTER = new AtomicLong();
    /** Exact process-local object tokens; identity hash collisions are unsafe. */
    private static final IdentityHashMap<Object, Integer> OBJECT_IDS =
            new IdentityHashMap<>();
    private static int nextObjectId = 1;
    private static final ThreadLocal<Deque<ActiveCall>> ACTIVE_CALLS =
            ThreadLocal.withInitial(ArrayDeque::new);
    private static final ThreadLocal<Deque<ActiveCallSite>> ACTIVE_CALL_SITES =
            ThreadLocal.withInitial(ArrayDeque::new);
    /** A concolic replay keeps call stacks but does not publish a trace. */
    private static volatile boolean contextOnlyConcolicReplay;
    private static volatile boolean recordingEnabled = true;
    /** Whether the workload has called {@link #startRecording()} here. */
    private static volatile boolean recordingStarted;

    private static volatile File outputDir;
    private static volatile String testName;
    /** Guarded by {@link #LOCK}; persisted in the streaming close manifest. */
    private static boolean traceWriteFailure;
    private static BufferedWriter traceWriter;
    /** Guarded by {@link #LOCK}; a reset must not install duplicate hooks. */
    private static boolean shutdownHookRegistered;

    private CausynthTraceRecorder() {
    }

    /** Opens the workload-defined trace boundary after source initialization. */
    public static void startRecording() {
        initialize();
        recordingEnabled = true;
        recordingStarted = true;
        // k is window-local on both ends: the recording counts from the
        // moment the workload opens its window and so does every replay of
        // it, so a hop's k names the same activation in both.
        edu.uva.liftlab.graphchecker.runtime.Lineage.openWindow();
    }

    /**
     * Whether the workload has opened its recorded window in this run.
     *
     * <p>One moment, shared by both executions because the workload makes
     * it: the recording writes its first trace line here, so the plan counts
     * activations from here and a replay must count from here too.</p>
     *
     * <p>Monotonic, and deliberately not {@link #recordingEnabled}: the
     * trace pass starts paused and the replay pass does not, so that flag is
     * already true in a replay before the workload has opened anything.
     * Nor is it "a source has been registered" -- registration is state the
     * workload may establish long before it starts recording.  On hdfs-11741
     * it registers the balancer, then {@code TestBalancer} restarts the
     * cluster, and only then registers the new NameNode's RPC server and
     * starts recording; a whole NameNode generation runs in between, whose
     * handler activations the recording never wrote a line for and the
     * replay counted, numbering a population the plan never numbered.</p>
     */
    static boolean recordingStarted() {
        return recordingStarted;
    }

    /** Test hook: a fixture states whether its run has opened the window. */
    static void setRecordingStartedForTests(boolean started) {
        recordingStarted = started;
    }

    public static void main(String[] args) {
        Map<String, String> params = parseArgs(args);
        File directory = new File(requiredArg(params, "trace-dir"));
        String test = requiredArg(params, "test");
        boolean skeletonOnly = Boolean.parseBoolean(
                params.get("region-skeleton-only"));
        String configuredSkeletons = params.get("region-skeletons");
        File candidateSkeletons = configuredSkeletons == null
                || configuredSkeletons.trim().isEmpty()
                ? null : new File(configuredSkeletons.trim());
        if (candidateSkeletons == null) {
            throw new IllegalArgumentException(
                    "--region-skeletons is required");
        }
        File graph = skeletonOnly ? null
                : new File(requiredArg(params, "candidate-graph"));
        String configuredOutput = params.get("output-dir");
        File planOutputDirectory = configuredOutput == null
                || configuredOutput.trim().isEmpty()
                ? directory : new File(configuredOutput.trim());
        try {
            if (skeletonOnly) {
                aggregateSkeletonTrace(directory, candidateSkeletons,
                        test, planOutputDirectory);
            } else {
                String configuredRefined = params.get("refined-graph");
                File refinedGraph = configuredRefined == null
                        || configuredRefined.trim().isEmpty()
                        ? new File(planOutputDirectory,
                        "refined_dataflow_edges.jsonl.gz")
                        : new File(configuredRefined.trim());
                aggregateStateTrace(directory, graph, candidateSkeletons,
                        refinedGraph, test, planOutputDirectory,
                        new File(requiredArg(params, "recording-gaps")),
                        new File(requiredArg(params, "static-scope-map")));
            }
        } catch (Throwable throwable) {
            System.err.println("Failed to aggregate Causynth runtime trace: "
                    + throwable);
            throwable.printStackTrace(System.err);
            System.exit(1);
        }
    }

    /**
     * Rich method-entry event used by graph-directed symbolic
     * instrumentation.
     *
     * @param openedRegionId the region this method is the ROOT of, or
     *                       {@code ""}: the recording pushes an execution
     *                       index frame and states an occurrence address
     *                       exactly where the replay does
     */
    public static long enterMethod(String method, Object receiver,
                                   String openedRegionId) {
        if (method == null) {
            return 0L;
        }
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        long tid = thread.getId();
        int objectId = identity(receiver);
        Deque<ActiveCall> calls = ACTIVE_CALLS.get();
        ActiveCall parent = calls.peek();
        Deque<ActiveCallSite> sites = ACTIVE_CALL_SITES.get();
        ActiveCallSite parentSite = sites.peek();
        long parentCallId = parent == null ? 0L : parent.callId;
        long parentSiteId = parentSite == null ? 0L : parentSite.invocationId;
        RuntimeTraceContext.View context = parent == null
                ? RuntimeTraceContext.enterRoot(receiver)
                : RuntimeTraceContext.current();
        boolean receiverAttributed = parent == null
                ? context.receiverAttributed
                : context.source != null && context.source.equals(
                RuntimeTraceContext.sourceFor(receiver));
        String region = MapFields.safe(openedRegionId);
        calls.push(new ActiveCall(id, parentSiteId, method,
                context.spanId, parent == null, !region.isEmpty()));
        // No frame here.  The level of THIS activation was opened by the
        // frame hook at this same entry (#enterMethodFrame), which every
        // method of the application scope carries in both passes (G11), and
        // it is standing before this row reads the address.  A second push
        // at one entry would add a frame the replay does not have and move
        // every address below it.
        String address = "";
        boolean folded = false;
        if (!region.isEmpty()) {
            // No claim here.  A started work claims its start frame at its
            // FIRST identity event, which is the entry of the functional
            // method the start named (#claimStart, woven by
            // CausynthPipeline.claimWorkEntry in both passes) -- strictly
            // earlier than any region entry inside the work, and reached on
            // a pool thread whose task enters no region at all.  A second
            // claim point for one notion is a second identity.
            String node = RuntimeTraceContext.activationSource(receiver).key();
            // Opened, as a replay opens it: the endpoints of the events
            // inside this activation are indexed from here and name this
            // occurrence (Identity.currentOccurrence), which is how the
            // recording files the same producer endpoint a replay does.
            address = occurrenceAddress(node, region);
            // F1: an entry that FOLDED into the occurrence already running
            // opened none, so it is no activation and this row states no
            // address -- the trace carries it as the plain frame it is, and
            // PLAN builds one activation per occurrence
            // (RuntimeRegionPlanner#regionRoots).  The marker the fold
            // pushed is still popped by this call's own exit, which is what
            // the region frame above is for.
            //
            // Asked of the identity, not read off the empty address: an
            // entry the run could name no NODE for also states none, and
            // that one is a hole PLAN refuses rather than a fold it skips.
            folded = Identity.foldedEntry();
        }
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName,
                        threadName, tid, method, objectId,
                        runtimeType(receiver), id, parentCallId, parentSiteId,
                        context.laneId, context.spanId,
                        context.remoteParentSpanId, context.source,
                        receiverAttributed,
                        context.requestKey, context.requestApi, address,
                        folded);
        if (contextOnlyConcolicReplay) {
            return id;
        }
        synchronized (LOCK) {
            writeTraceLine(event);
        }
        return id;
    }

    /**
     * The address of the activation entering here, by the one computation.
     *
     * <p>{@code Identity.occurrence} -- the same function, over the same
     * frame stack and scope, that a replay calls from its region hook -- and
     * the node by {@code RuntimeTraceContext.activationSource}, which is the
     * rule the replay evaluates at its own root entry.  The region is not
     * opened here: the recording indexes no endpoints from it.</p>
     *
     * <p>Which means the FOLD is the same one the replay takes: a declared
     * region entered synchronously inside another region's occurrence opens
     * none of its own ({@code Identity#fold}, paper SS3.1.2), so the address
     * this row carries for such an entry is the enclosing occurrence's -- and
     * the plan built from these rows names the occurrence the replay will
     * open.  Two passes cannot disagree about it because neither of them
     * decides it.</p>
     */
    private static String occurrenceAddress(String nodeKey, String regionId) {
        edu.uva.liftlab.graphchecker.contract.OccurrenceAddress address =
                Identity.occurrence(nodeKey, regionId, true);
        // F1: a folded entry is a method call inside the occurrence already
        // running, not the entry of one, so this row states no address --
        // the occurrence it folded into stated its own when it was entered,
        // and a second row carrying that address would be a second
        // activation of one occurrence.  The call above still runs: it is
        // what PUSHES the fold's marker, and the marker is what makes this
        // entry's exit close nothing.
        if (Identity.foldedEntry()) return "";
        return address == null ? "" : address.render();
    }

    /**
     * Files the frame of one work start, for the work it started.
     *
     * <p>The work starts whether or not its frame can be named -- an
     * instrumentation hook may not turn a start into a failure -- but a
     * start nobody could name is a lineage hole and says so: the occurrence
     * the started work will publish is the one that loses its start-site
     * frame, so the failure is stated where it happened, in the channel
     * each pass has (a session gap row in a replay, a plan gap through the
     * trace in the recording).  It is never swallowed.</p>
     */
    public static void claimStart(Object carrier) {
        try {
            Identity.claimStart(carrier);
        } catch (Throwable unnamed) {
            // Same rule as the filing half: the work runs either way, and a
            // frame nobody could claim is stated where it happened rather
            // than swallowed.
            String subject = lineageSubject(carrier == null ? ""
                    : carrier.getClass().getName());
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    subject, "the start frame filed for this work could not "
                            + "be claimed, so the occurrences it publishes "
                            + "carry no start-site frame in their execution "
                            + "index: " + unnamed);
            writeLineageGap(subject, "the start frame filed for this work "
                    + "could not be claimed, so the occurrences it publishes "
                    + "carry no start-site frame in their execution index: "
                    + unnamed);
        }
    }

    public static void startWork(String startSiteId, Object carrier) {
        String site = MapFields.safe(startSiteId);
        try {
            Identity.startWork(site, carrier,
                    RuntimeTraceContext.activationSource(null).key());
        } catch (Throwable unnamed) {
            RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST,
                    edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                    lineageSubject(site.isEmpty() && carrier != null
                                    ? carrier.getClass().getName() : site),
                    "the frame of this work start could not be filed, "
                            + "so the work it started carries no start-site "
                            + "frame in its execution index: "
                            + unnamed);
            writeLineageGap(lineageSubject(site.isEmpty() && carrier != null
                            ? carrier.getClass().getName() : site),
                    "the frame of this work start could not be "
                    + "filed, so the work it started carries no start-site "
                    + "frame in its execution index: " + unnamed);
        }
    }

    /** {@code event} of one lineage gap the RECORDING states. */
    static final String LINEAGE_GAP_EVENT = "LINEAGE_GAP";

    /**
     * A gap row names its own subject.
     *
     * <p>Both lineage gaps above are raised exactly where an identity could
     * NOT be established, which is where the name they would like to state
     * is most likely missing: a null carrier, a blank start site.  The row's
     * door substitutes the session for a blank subject, so the row was still
     * filed -- and named the session rather than the thing that lost its
     * frame, which is the one fact a reader needs from it.  The fallbacks
     * are the frames this thread is actually in: the source key the
     * recording attributes its work to, then the thread itself, which always
     * has a name and an id.</p>
     */
    private static String lineageSubject(String named) {
        String subject = MapFields.safe(named);
        if (!subject.isEmpty()) return subject;
        try {
            subject = MapFields.safe(
                    RuntimeTraceContext.activationSource(null).key());
        } catch (Throwable unnamed) {
            subject = "";
        }
        if (!subject.isEmpty()) return subject;
        Thread current = Thread.currentThread();
        return "thread:" + MapFields.safe(current.getName())
                + "#" + current.getId();
    }

    /**
     * States one lineage gap of the recording, for the plan to publish.
     *
     * <p>The recording has no session to hold a gap row, and the aggregation
     * is the next reader of everything it writes, so the fact travels as a
     * trace row and {@link #aggregateStateTrace} hands it to the plan's own
     * gap list.  A gap the recording cannot state is a gap nobody ever
     * hears about.</p>
     */
    private static void writeLineageGap(String subject, String detail) {
        if (!recordingEnabled) return;
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 3,
                    "event", LINEAGE_GAP_EVENT,
                    "seq", EVENT_COUNTER.incrementAndGet(),
                    // Stated the way every other gap row states it: the
                    // kind, and the class its producer decided (item 1 of
                    // the PLAN cleanup -- there is no ledger to look it up
                    // in).  A degraded address is a diagnostic: the row it
                    // is about still says what it observed.
                    "kind", edu.uva.liftlab.graphchecker.contract.GapKind
                            .LINEAGE_LOST.name(),
                    "cls", edu.uva.liftlab.graphchecker.contract.GapClass
                            .DIAGNOSTIC.name(),
                    "subject", MapFields.safe(subject),
                    "detail", MapFields.safe(detail));
        }
    }

    /** Records only the balanced activation tree for skeleton selection. */
    public static long enterMethodLite(String method, Object receiver) {
        if (method == null) {
            return 0L;
        }
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        Deque<ActiveCall> calls = ACTIVE_CALLS.get();
        ActiveCall parent = calls.peek();
        long parentCallId = parent == null ? 0L : parent.callId;
        RuntimeTraceContext.View context = parent == null
                ? RuntimeTraceContext.enterRoot(receiver)
                : RuntimeTraceContext.current();
        boolean receiverAttributed = parent == null
                ? context.receiverAttributed
                : context.source != null && context.source.equals(
                RuntimeTraceContext.sourceFor(receiver));
        calls.push(new ActiveCall(id, 0L, method, context.spanId,
                parent == null, false));
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName,
                        threadName, thread.getId(), method, 0, "", id,
                        parentCallId, 0L, context.laneId, context.spanId,
                        context.remoteParentSpanId,
                        context.source, receiverAttributed,
                        context.requestKey, context.requestApi);
        if (!contextOnlyConcolicReplay) {
            synchronized (LOCK) {
                writeTraceLine(event);
            }
        }
        return id;
    }

    public static void recordMethodArgument(long callId, int argumentIndex,
                                            String declaredType, Object value,
                                            String primitiveValue) {
        ActiveCall call = activeCall(callId);
        ExecutionEvent event = newExecutionEvent("METHOD_ARGUMENT",
                call == null ? "" : call.method, callId);
        event.argumentIndex = argumentIndex;
        event.runtimeType = runtimeType(value);
        event.objectId = identity(value);
        event.primitiveValue = MapFields.safe(primitiveValue);
        emitExecutionEvent(event);
    }

    public static long beginCall(long ownerCallId, String caller, int unitIndex,
                                 String declaredCallee, Object receiver) {
        ActiveCall owner = activeCall(ownerCallId);
        closeStaleCallSite(ownerCallId);
        ExecutionEvent event = newExecutionEvent("CALL_SITE_ENTER",
                firstNonBlank(caller, owner == null ? "" : owner.method), ownerCallId);
        event.siteId = SiteId.render(event.method, unitIndex);
        event.declaredCallee = MapFields.safe(declaredCallee);
        event.runtimeType = runtimeType(receiver);
        event.objectId = identity(receiver);
        event.invocationId = event.id;
        emitExecutionEvent(event);
        if (WorkStartSites.startsReceiver(
                WorkStartSites.calleeName(declaredCallee),
                WorkStartSites.argumentCount(declaredCallee),
                WorkStartSites.typesOf(receiver))) {
            RuntimeTraceContext.captureAsync(receiver);
        }
        if (event.id > 0L) {
            ACTIVE_CALL_SITES.get().push(new ActiveCallSite(event.id, ownerCallId,
                    event.siteId, event.method, event.declaredCallee));
        }
        return event.id;
    }

    public static void recordCallArgument(long invocationId, int argumentIndex,
                                          String declaredType, Object value,
                                          String primitiveValue) {
        ActiveCallSite site = activeCallSite(invocationId);
        ExecutionEvent event = callSiteEvent("CALL_ARGUMENT", site,
                invocationId);
        event.argumentIndex = argumentIndex;
        event.runtimeType = runtimeType(value);
        event.objectId = identity(value);
        event.primitiveValue = MapFields.safe(primitiveValue);
        // Any argument, not only the first: a fork-join batch submits its
        // tasks as the arguments of one invokeAll, and each of them is a
        // submission whose endpoint the task it started runs under.  The
        // shapes are WorkStartSites' -- the same list the weave files the
        // start-site frames from.
        String submission = site == null ? "" : site.declaredCallee;
        if (WorkStartSites.submitsArguments(
                WorkStartSites.calleeName(submission),
                WorkStartSites.argumentCount(submission))
                && WorkStartSites.carriesWork(
                        WorkStartSites.typesOf(value))) {
            RuntimeTraceContext.captureAsync(value);
        }
        emitExecutionEvent(event);
    }

    /**
     * Enters the execution-index level of ONE application-scope method.
     *
     * <p>The recording's half of the one frame rule: every method of the
     * application scope opens a level at its entry and closes it at every
     * exit, in this pass and in the replay alike, woven by the one walk
     * ({@code CausynthPipeline.instrumentApplicationScope}).  The calling
     * context of every event is then the application methods it is inside,
     * so a thread outside every region has one -- which is what the
     * region-root-only frame rule could not give it, leaving its site
     * counts run-length ordinals over the process (IDENTITY-V3 §1).</p>
     *
     * <p>The node is not read here, and the level does not want one: a
     * level's counts are keyed by (level, root hop, site) and by nothing
     * else ({@code Identity.State#nextSiteEvent}).</p>
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterMethodFrame(String callSiteId) {
        return edu.uva.liftlab.graphchecker.runtime.Identity.enterFrame(
                MapFields.safe(callSiteId));
    }

    /** Leaves the level {@link #enterMethodFrame} opened. */
    public static void exitMethodFrame(long token) {
        edu.uva.liftlab.graphchecker.runtime.Identity.exitFrame(token);
    }

    /** The exceptional edge of {@link #enterMethodFrame}. */
    public static void throwMethodFrame(long token, Throwable thrown) {
        edu.uva.liftlab.graphchecker.runtime.Identity.exitFrame(token);
    }

    /** Leaves the region one rich activation opened. */
    private static void popRegion() {
        edu.uva.liftlab.graphchecker.runtime.Identity.regionExit();
    }

    public static void endCall(long invocationId, Object returnValue,
                               String primitiveValue) {
        ActiveCallSite site = activeCallSite(invocationId);
        ExecutionEvent event = callSiteEvent("CALL_SITE_RETURN", site,
                invocationId);
        event.runtimeType = runtimeType(returnValue);
        event.objectId = identity(returnValue);
        event.primitiveValue = MapFields.safe(primitiveValue);
        emitExecutionEvent(event);
        removeCallSite(invocationId);
    }

    /** Closes one exact call-site activation on its exceptional edge. */
    public static void throwCall(long invocationId) {
        closeCallSite(activeCallSite(invocationId), "CALL_SITE_THROW");
    }

    public static void recordBranch(long callId, String method, int unitIndex,
                                    String expression, boolean outcome) {
        ExecutionEvent event = branchEvent(callId, method, unitIndex);
        event.outcome = outcome;
        emitExecutionEvent(event);
    }

    /** One branch row at the exact unit of the method that executed it. */
    private static ExecutionEvent branchEvent(long callId, String method,
                                              int unitIndex) {
        ExecutionEvent event = newExecutionEvent("BRANCH",
                firstNonBlank(method, methodForCall(callId)), callId);
        event.siteId = SiteId.render(event.method, unitIndex);
        return event;
    }

    /** Records one exact case/default successor of a JVM switch. */
    public static void recordSwitchBranch(long callId, String method,
                                          int unitIndex, String expression,
                                          int successorIndex,
                                          String branchKind,
                                          String encodedCaseKeys) {
        ExecutionEvent event = branchEvent(callId, method, unitIndex);
        event.branchKind = MapFields.safe(branchKind);
        event.switchCaseKeys = MapFields.safe(encodedCaseKeys);
        event.successorIndex = successorIndex >= 0 ? successorIndex : null;
        int caseCount = encodedCaseKeys == null
                || encodedCaseKeys.isEmpty() ? 0
                : encodedCaseKeys.split(",", -1).length;
        event.outcome = event.successorIndex == null ? null
                : successorIndex < caseCount;
        emitExecutionEvent(event);
    }

    /** Normal exit resolved from the current thread-local call stack. */
    public static void exitActiveMethod(Object returnValue,
                                        String primitiveValue) {
        ActiveCall call = activeCall(0L);
        long resolvedCallId = call == null ? 0L : call.callId;
        closeCallSites(resolvedCallId, "CALL_SITE_INCOMPLETE");
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_NORMAL",
                call == null ? "" : call.method, resolvedCallId);
        event.runtimeType = runtimeType(returnValue);
        event.objectId = identity(returnValue);
        event.primitiveValue = MapFields.safe(primitiveValue);
        emitExecutionEvent(event);
        removeCall(resolvedCallId);
        if (call != null && call.regionFrame) {
            popRegion();
        }
        if (call != null && call.rootContext) {
            RuntimeTraceContext.exitRoot(call.spanId);
        }
    }

    /**
     * Exceptional-exit hook that resolves the call id from the thread-local
     * call stack.  The injected catch-all handler deliberately does not read
     * the synthetic long local: some JVM/Soot stack-map combinations do not
     * keep that local live at an exceptional handler entry.
     */
    public static void throwActiveMethod(Throwable throwable) {
        ActiveCall call = activeCall(0L);
        long resolvedCallId = call == null ? 0L : call.callId;
        String exceptionType = throwable == null ? "" : throwable.getClass().getName();
        closeCallSites(resolvedCallId, "CALL_SITE_THROW");
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_THROW",
                call == null ? "" : call.method, resolvedCallId);
        event.runtimeType = exceptionType;
        event.objectId = identity(throwable);
        emitExecutionEvent(event);
        if (call != null && call.parentSiteId > 0L) {
            ActiveCallSite parentSite = activeCallSite(call.parentSiteId);
            if (parentSite != null) {
                closeCallSite(parentSite, "CALL_SITE_THROW");
            }
        }
        removeCall(resolvedCallId);
        if (call != null && call.regionFrame) {
            popRegion();
        }
        if (call != null && call.rootContext) {
            RuntimeTraceContext.exitRoot(call.spanId);
        }
    }

    /** Removes the current lite activation without emitting an exit row. */
    public static void exitActiveMethodLite() {
        exitActiveMethodLite("CALL_SITE_INCOMPLETE");
    }

    private static void exitActiveMethodLite(String callSiteExit) {
        ActiveCall call = ACTIVE_CALLS.get().peek();
        if (call != null) {
            closeCallSites(call.callId, callSiteExit);
            removeCall(call.callId);
            if (call.regionFrame) {
                popRegion();
            }
            if (call.rootContext) {
                RuntimeTraceContext.exitRoot(call.spanId);
            }
        }
    }

    /** Removes an exceptionally exiting lite activation without trace output. */
    public static void throwActiveMethodLite(Throwable ignored) {
        exitActiveMethodLite("CALL_SITE_THROW");
    }

    public static void recordField(String kind, String method, int unitIndex,
                                   String field, Object methodReceiver,
                                   Object fieldReceiver, Object valueObject,
                                   String primitiveValue) {
        if (method == null || field == null) {
            return;
        }
        initialize();
        if (contextOnlyConcolicReplay) {
            return;
        }
        long id = EVENT_COUNTER.incrementAndGet();
        int receiverObjectId = identity(fieldReceiver);
        int valueObjectId = identity(valueObject);
        ActiveCall activeCall = ACTIVE_CALLS.get().peek();
        RuntimeRegionPlanner.FieldAccessEvent event =
                new RuntimeRegionPlanner.FieldAccessEvent(id, kind, method,
                        activeCall == null ? 0L : activeCall.callId,
                        unitIndex, SiteId.render(method, unitIndex), field,
                        receiverObjectId, valueObjectId, primitiveValue);
        synchronized (LOCK) {
            writeFieldTraceLine(event);
        }
    }

    /**
     * The request scope of the calling thread, to be carried with the work
     * it is creating.
     *
     * <p>Hadoop builds a {@code Call} on the caller's thread and writes it
     * from a sender thread its connection pool created once; the scope has
     * to travel with the call, because the thread that performs the write
     * may never have been inside it.</p>
     */
    public static Object captureScope() {
        initialize();
        return RuntimeTraceContext.captureScope();
    }

    /** Sends one exchange leg and returns its message-carried trace context. */
    public static String outboundExchange(String transport,
                                          String correlationId,
                                          String attemptId, String half,
                                          Object localOwner) {
        return outboundExchange(transport, correlationId, attemptId, half,
                localOwner, null);
    }

    /** The same exchange, for work carrying the scope it was made in. */
    public static String outboundExchange(String transport,
                                          String correlationId,
                                          String attemptId, String half,
                                          Object localOwner,
                                          Object carriedScope) {
        initialize();
        String header;
        try {
            header = RuntimeTraceContext.outboundHeader(localOwner,
                    carriedScope);
        } catch (IllegalStateException noFlow) {
            // One rule for both halves of a message-carried context: the
            // refusal is a named row and the send goes out without a
            // header.
            RowRuntime.messageContextRefused("outbound "
                    + MapFields.safe(transport) + " "
                    + MapFields.safe(half), noFlow.getMessage());
            return "";
        }
        // The SEND of the schedule, before the producer is minted: a replay
        // held to a prefix lets this message leave when it is its turn.
        ScheduleLog.observe(
                edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.SEND,
                MapFields.safe(transport) + "#" + MapFields.safe(half));
        // IDENTITY-V3 §C: the message carries its producer's endpoint, so
        // the receiver can state the anchor it ran under.  Filed by
        // correlation because the endpoint is bigger than the header slot
        // this transport has; the pairing itself is the run's own fact.
        // One computation, called from the one place both passes reach it:
        // the recording files the same producer endpoint a replay does.
        Endpoint producer = Identity.messageSent(
                RuntimeTraceContext.activationSource(localOwner).key(),
                transport, correlationId, half);
        // The row states that endpoint's components and not only the digest
        // the anchor travels as, because they are what a planned-vs-ran
        // anchor has to be compared on.  Stated by the mint above: the
        // trace carries the endpoint Identity built, never a second reading
        // of the four inputs.
        refuseSharedProducer(transport, correlationId, half, producer);
        recordExchange("SEND", transport, correlationId, attemptId, half,
                localOwner, carriedScope, producer);
        return header;
    }

    /**
     * Names the refusal when two messages carry ONE producer endpoint.
     *
     * <p>A producer endpoint id is (occurrence, transport site, the k-th
     * event of that occurrence there, attempt), so two messages that share
     * one are two messages whose consumers state the SAME causal anchor:
     * every occurrence downstream of either carries the other's context too,
     * and no plan can address them apart.  It happens when two threads run
     * under one degraded role occurrence and neither could claim a start
     * frame -- a thread started before the recording began, or from JDK
     * code, files none -- and the consequence is already refused where it
     * is decidable (OCCURRENCE_ADDRESS_SHARED over the region activations,
     * and invariant 4 over the session's own endpoints).  This row names
     * the CAUSE, at the mint, in the one place both passes send from, and
     * states the endpoint's four components rather than the digest.</p>
     *
     * <p>DIAGNOSTIC, by the same ruling invariant 4 carries: an index that
     * cannot separate two events of one site is the identity's to fix and no
     * row can state it, so refusing the recording for it would fail every
     * campaign at IMPORT over something no stage can repair.</p>
     */
    private static void refuseSharedProducer(String transport,
                                             String correlationId,
                                             String half, Endpoint producer) {
        String shared = Interactions.sharedProducer(transport, correlationId,
                half, producer);
        if (shared.isEmpty()) return;
        String detail = "this message's producer endpoint was already minted "
                + "for " + shared + ", so both messages carry one causal "
                + "anchor and every occurrence downstream of either states "
                + "the same context; the endpoint is "
                + producer.render();
        RowRuntime.gap(edu.uva.liftlab.graphchecker.contract.GapKind
                        .LINEAGE_LOST,
                edu.uva.liftlab.graphchecker.contract.GapClass.DIAGNOSTIC,
                producer.id(), detail);
        writeLineageGap(producer.id(), detail);
    }

    /** Installs a received message context until {@link #endInboundExchange}. */
    public static long inboundExchange(String header, String transport,
                                       String correlationId,
                                       String attemptId, String half,
                                       Object localOwner) {
        initialize();
        long token;
        try {
            token = RuntimeTraceContext.enterInbound(header, transport,
                    correlationId, attemptId, half, localOwner);
        } catch (IllegalArgumentException refused) {
            // A header this side will not parse is the same refusal the
            // envelope half states, and 0 is already what "no scope was
            // installed" means to every caller.
            RowRuntime.messageContextRefused("inbound "
                    + MapFields.safe(transport) + " "
                    + MapFields.safe(half), refused.getMessage());
            return 0L;
        }
        // The RECV of the schedule, under the scope the message opened: its
        // context names the producer endpoint, which is WHICH message.
        ScheduleLog.observe(
                edu.uva.liftlab.graphchecker.contract.ScheduleEvent.Kind.RECV,
                MapFields.safe(transport) + "#" + MapFields.safe(half));
        // recordExchange's own refusal is not this rule: it names the
        // engine's argument contract, which every caller satisfies with
        // constants, so it stays an exception rather than a row.
        try {
            // No producer: a delivery states the endpoint it was SENT from
            // through the message, and the receiving leg mints none.
            recordExchange("RECEIVE", transport, correlationId, attemptId,
                    half, localOwner, null, null);
            return token;
        } catch (RuntimeException | Error failure) {
            RuntimeTraceContext.exitInbound(token);
            throw failure;
        }
    }

    public static void endInboundExchange(long scopeToken) {
        RuntimeTraceContext.exitInbound(scopeToken);
    }

    /**
     * Records one transport-neutral message boundary, attributed to the
     * scope the work carries, stating the producer endpoint a SEND minted.
     */
    public static void recordExchange(String direction, String transport,
                                      String correlationId, String attemptId,
                                      String half, Object localOwner,
                                      Object carriedScope,
                                      Endpoint producer) {
        String normalizedDirection = MapFields.safe(direction).toUpperCase();
        String normalizedTransport = MapFields.safe(transport).trim();
        String normalizedCorrelation = MapFields.safe(correlationId).trim();
        String normalizedHalf = MapFields.safe(half).toUpperCase();
        if (!("SEND".equals(normalizedDirection)
                || "RECEIVE".equals(normalizedDirection))
                || normalizedTransport.isEmpty()
                || normalizedCorrelation.isEmpty()
                || !("REQUEST".equals(normalizedHalf)
                || "RESPONSE".equals(normalizedHalf))) {
            throw new IllegalArgumentException(
                    "exchange requires direction, transport, correlation, and half");
        }
        initialize();
        String normalizedAttempt = MapFields.safe(attemptId).trim();
        RuntimeTraceContext.View context =
                RuntimeTraceContext.exchange(localOwner, carriedScope);
        if (contextOnlyConcolicReplay) return;
        long id = EVENT_COUNTER.incrementAndGet();
        Thread thread = Thread.currentThread();
        ActiveCall call = ACTIVE_CALLS.get().peek();
        ActiveCallSite site = ACTIVE_CALL_SITES.get().peek();
        String method = call == null ? "" : call.method;
        RuntimeRegionPlanner.ProtocolEvent event =
                new RuntimeRegionPlanner.ProtocolEvent(id,
                        normalizedDirection, normalizedTransport,
                        normalizedCorrelation, normalizedAttempt,
                        normalizedHalf,
                        thread.getName(),
                        thread.getId(), method,
                        call == null ? 0L : call.callId,
                        site == null ? 0L : site.invocationId,
                        site == null ? "" : site.declaredCallee,
                        context.laneId, context.spanId,
                        context.remoteParentSpanId,
                        context.source, context.requestKey,
                        context.requestApi,
                        producer == null ? "" : producer.id(),
                        producer == null ? "" : producer.render());
        synchronized (LOCK) {
            writeProtocolTraceLine(event);
        }
    }

    /** Registers one stable cluster/application source for trace discovery. */
    public static void registerSource(Object anchor, String kind,
                                      String role, String sourceId,
                                      long epoch) {
        initialize();
        SourceRef source = RuntimeTraceContext.registerSource(anchor,
                new SourceRef(kind, role, sourceId, epoch));
        writeSourceTraceLine("SOURCE_REGISTER", source, null, 0L, "",
                identity(anchor));
    }

    /** Binds a service/handler object to an already registered source. */
    public static void registerSourceAlias(Object alias, Object anchor) {
        initialize();
        SourceRef source = RuntimeTraceContext.registerSourceAlias(alias,
                anchor);
        writeSourceTraceLine("SOURCE_ALIAS", source, null, 0L,
                alias == null ? "" : alias.getClass().getName(),
                identity(alias));
    }

    /** Captures the submitting context for an application-owned task queue. */
    public static void captureAsync(Object carrier) {
        initialize();
        RuntimeTraceContext.captureAsync(carrier);
    }

    /**
     * Enters the scope a queued unit of work carried from where it was made.
     *
     * <p>The dequeue half of {@link #captureScope()}: the enqueueing thread
     * captures, the running thread enters here and leaves through {@link
     * #exitCarriedScope(long)}.  Hadoop's IPC {@code Server.Call} is the
     * case this exists for -- built on a reader thread, run on a handler of
     * a pool created at connection setup, which no inheritable context ever
     * reaches.</p>
     *
     * @param carriedScope the value {@link #captureScope()} returned
     * @param roleName     what the workload calls the scope kind serving
     *                     it; that name IS the role
     *                     ({@code contract.Role})
     * @param apiName      the api being served, or {@code null}
     * @return the token to hand {@link #exitCarriedScope(long)}, or 0
     */
    public static long enterCarriedScope(Object carriedScope,
                                         String roleName, String apiName) {
        initialize();
        return RuntimeTraceContext.enterCarriedScope(carriedScope, roleName,
                apiName);
    }

    /** Leaves the scope {@link #enterCarriedScope} entered. */
    public static void exitCarriedScope(long token) {
        RuntimeTraceContext.exitCarriedScope(token);
    }

    /**
     * Opens one daemon tick as a root of its own.
     *
     * <p>A timer thread serves no request and is created by none, so its
     * activations have no scope to inherit or repair.  Naming the tick --
     * role plus the k-th tick in the recording window -- is what makes the
     * NameNode's key rotation an addressable occurrence.</p>
     *
     * @param owner    an object whose registered source names the node, or
     *                 {@code null} to take the thread's own
     * @param roleName what the workload calls this timer's scope kind;
     *                 that name IS the role ({@code contract.Role}), and
     *                 the engine holds no catalog of them
     * @return the token to hand {@link #endDaemonTick(long)}
     */
    public static long beginDaemonTick(Object owner, String roleName) {
        initialize();
        return RuntimeTraceContext.beginTick(owner, roleName);
    }

    /** Closes the tick {@link #beginDaemonTick} opened. */
    public static void endDaemonTick(long token) {
        RuntimeTraceContext.endTick(token);
    }

    /** Starts an external API request without changing the application data. */
    public static long beginSourceRequest(Object sourceAnchor,
                                          String apiName) {
        initialize();
        long requestId = RuntimeTraceContext.beginRequest(sourceAnchor,
                apiName);
        writeSourceTraceLine("REQUEST_BEGIN",
                RuntimeTraceContext.currentSource(), null, requestId,
                MapFields.safe(apiName), 0);
        return requestId;
    }

    public static void endSourceRequest(long requestId, String apiName) {
        SourceRef source = RuntimeTraceContext.currentSource();
        writeSourceTraceLine("REQUEST_END", source, null, requestId,
                MapFields.safe(apiName), 0);
        RuntimeTraceContext.endRequest(requestId);
    }

    /** Advances a stable logical source slot to a new lifecycle epoch. */
    public static void restartSource(Object stableAnchor, String kind,
                                     String role, String sourceId,
                                     long epoch) {
        initialize();
        SourceRef before = RuntimeTraceContext.sourceFor(stableAnchor);
        SourceRef after = RuntimeTraceContext.restartSource(stableAnchor,
                new SourceRef(kind, role, sourceId, epoch));
        writeSourceTraceLine("SOURCE_RESTART", before, after, 0L, "",
                identity(stableAnchor));
    }

    private static ExecutionEvent newExecutionEvent(String kind, String method,
                                                    long callId) {
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        ExecutionEvent event = new ExecutionEvent();
        event.id = id;
        event.kind = MapFields.safe(kind);
        event.method = MapFields.safe(method);
        event.callId = callId;
        // No index and no context here.  Only the METHOD_ENTER and exchange
        // rows are read for them, and folding the index's hash and
        // rendering its path on every field read, branch and call site cost
        // the recording more than everything else it does: one sha256 per
        // frame per event, and a path string per event, for a member
        // nothing downstream reads.
        return event;
    }

    /**
     * The causal context of the scope this event ran in, as the RECORDING
     * can state it.
     *
     * <p>An anchored scope names the exchange that opened it rather than the
     * producer's endpoint id: which occurrence produced that message is
     * exactly what the offline pass computes, and stating a correlation the
     * trace also carries on both its {@code EXCHANGE_SEND} and {@code
     * EXCHANGE_RECEIVE} rows lets it be resolved without guessing.</p>
     */
    private static void emitExecutionEvent(ExecutionEvent event) {
        if (event == null || event.id <= 0L) {
            return;
        }
        if (contextOnlyConcolicReplay) {
            return;
        }
        synchronized (LOCK) {
            writeExecutionTraceLine(event);
        }
    }

    private static ActiveCall activeCall(long callId) {
        if (callId <= 0L) {
            return ACTIVE_CALLS.get().peek();
        }
        for (ActiveCall call : ACTIVE_CALLS.get()) {
            if (call.callId == callId) {
                return call;
            }
        }
        return null;
    }

    private static ActiveCallSite activeCallSite(long invocationId) {
        for (ActiveCallSite site : ACTIVE_CALL_SITES.get()) {
            if (site.invocationId == invocationId) {
                return site;
            }
        }
        return null;
    }

    /** Exact currently executing instrumented call site, or {@code null}. */
    public static ActiveCallSiteContext currentCallSiteContext() {
        ActiveCallSite site = ACTIVE_CALL_SITES.get().peek();
        return site == null ? null : new ActiveCallSiteContext(
                site.siteId, site.declaredCallee, site.ownerCallId,
                site.invocationId);
    }

    /**
     * Correlates a field hook inside an accessor body with the exact caller
     * callsite that selected that accessor.
     */
    public static boolean currentCallParentSiteMatches(
            String callerMethod, int callerUnitIndex, String callerSiteId,
            String declaredCallee) {
        ActiveCall call = ACTIVE_CALLS.get().peek();
        if (call == null || call.parentSiteId <= 0L
                || callerUnitIndex < 0) {
            return false;
        }
        ActiveCallSite site = activeCallSite(call.parentSiteId);
        String expectedSite = SiteId.render(callerMethod, callerUnitIndex);
        return site != null
                && MapFields.safe(callerMethod).equals(site.caller)
                && MapFields.safe(callerSiteId).equals(expectedSite)
                && expectedSite.equals(site.siteId)
                && MapFields.safe(declaredCallee).equals(site.declaredCallee);
    }

    private static void removeCall(long callId) {
        ActiveCall found = activeCall(callId);
        if (found != null) {
            ACTIVE_CALLS.get().remove(found);
        }
    }

    private static void removeCallSite(long invocationId) {
        ActiveCallSite found = activeCallSite(invocationId);
        if (found != null) {
            ACTIVE_CALL_SITES.get().remove(found);
        }
    }

    private static void closeStaleCallSite(long ownerCallId) {
        ActiveCallSite top = ACTIVE_CALL_SITES.get().peek();
        if (top != null && top.ownerCallId == ownerCallId) {
            closeCallSite(top, "CALL_SITE_INCOMPLETE");
        }
    }

    private static void closeCallSites(long ownerCallId, String kind) {
        List<ActiveCallSite> matches = new ArrayList<>();
        for (ActiveCallSite site : ACTIVE_CALL_SITES.get()) {
            if (site.ownerCallId == ownerCallId) {
                matches.add(site);
            }
        }
        for (ActiveCallSite site : matches) {
            closeCallSite(site, kind);
        }
    }

    /** One execution event attributed to an exact recorded call site. */
    private static ExecutionEvent callSiteEvent(String kind,
                                                ActiveCallSite site,
                                                long invocationId) {
        ExecutionEvent event = newExecutionEvent(kind,
                site == null ? "" : site.caller,
                site == null ? 0L : site.ownerCallId);
        event.invocationId = invocationId;
        event.siteId = site == null ? "" : site.siteId;
        event.declaredCallee = site == null ? "" : site.declaredCallee;
        return event;
    }

    private static void closeCallSite(ActiveCallSite site, String kind) {
        if (site == null) {
            return;
        }
        emitExecutionEvent(callSiteEvent(kind, site, site.invocationId));
        ACTIVE_CALL_SITES.get().remove(site);
    }

    private static String methodForCall(long callId) {
        ActiveCall call = activeCall(callId);
        return call == null ? "" : call.method;
    }

    private static int identity(Object value) {
        if (value == null) {
            return 0;
        }
        synchronized (LOCK) {
            Integer existing = OBJECT_IDS.get(value);
            if (existing != null) {
                return existing;
            }
            if (nextObjectId == Integer.MAX_VALUE) {
                throw new IllegalStateException(
                        "runtime object identity space exhausted");
            }
            int assigned = nextObjectId++;
            OBJECT_IDS.put(value, assigned);
            return assigned;
        }
    }

    private static String runtimeType(Object value) {
        return value == null ? "" : value.getClass().getName();
    }


    private static String sourceKind(SourceRef source) {
        return source == null ? "" : source.kind();
    }

    private static String sourceRole(SourceRef source) {
        return source == null ? "" : source.role();
    }

    private static String sourceId(SourceRef source) {
        return source == null ? "" : source.id();
    }

    private static Object sourceEpoch(SourceRef source) {
        return source == null ? null : source.epoch();
    }

    private static String sourceKey(SourceRef source) {
        return source == null ? "" : source.key();
    }

    private static SourceRef sourceRef(FlatJsonRow row) throws IOException {
        return sourceRef(row, "source");
    }

    private static SourceRef relatedSourceRef(FlatJsonRow row)
            throws IOException {
        return sourceRef(row, "relatedSource");
    }

    private static SourceRef sourceRef(FlatJsonRow row, String prefix)
            throws IOException {
        String key = row.stringValue(prefix + "Key");
        String kind = row.stringValue(prefix + "Kind");
        String role = row.stringValue(prefix + "Role");
        String id = row.stringValue(prefix + "Id");
        if (key.isEmpty() && kind.isEmpty() && role.isEmpty() && id.isEmpty()) {
            return null;
        }
        long epoch = row.longValue(prefix + "Epoch", -1L);
        try {
            SourceRef source = new SourceRef(kind, role, id, epoch);
            if (!key.isEmpty() && !source.key().equals(key)) {
                throw new IOException("sourceKey does not match source id/epoch: "
                        + key);
            }
            return source;
        } catch (IllegalArgumentException invalid) {
            throw new IOException("invalid source identity " + key, invalid);
        }
    }

    private static void initialize() {
        if (INITIALIZED.get()) {
            return;
        }
        synchronized (LOCK) {
            if (INITIALIZED.get()) {
                return;
            }

            String configuredTestName = firstNonBlank(
                    System.getProperty("causynth.trace.test"),
                    System.getenv("CAUSYNTH_TRACE_TEST"), "unknown-test");
            // Which pass this JVM is, DECLARED: one key, three values, and
            // the campaign sets it.  It used to be inferred from which of
            // two unrelated keys happened to be set -- results yes, trace
            // directory no -- so a lane whose shell exported a trace
            // directory turned a replay into a recording, and a replay
            // nothing exported at all wrote its trace over the seed's.
            boolean configuredContextOnly = RuntimeTraceMode.configured()
                    == RuntimeTraceMode.REPLAY_CONTEXT;
            recordingEnabled = !Boolean.getBoolean(
                    "causynth.trace.start.paused");
            File configuredOutputDir = configuredContextOnly ? null
                    : new File(firstNonBlank(
                    System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"),
                    "target/causynth-trace"));
            File configuredTraceFile = configuredOutputDir == null ? null
                    : new File(configuredOutputDir, "runtime_trace.jsonl");
            BufferedWriter configuredWriter = null;
            try {
                if (configuredContextOnly) {
                    // Keep the exact method/call-site TLS alive for every
                    // accessor invocation.
                    testName = configuredTestName;
                    traceWriteFailure = false;
                    outputDir = null;
                    traceWriter = null;
                    contextOnlyConcolicReplay = true;
                    INITIALIZED.set(true);
                    return;
                }
                if (configuredOutputDir.exists()) {
                    if (!configuredOutputDir.isDirectory()) {
                        throw new IOException("Trace output path is not a directory: "
                                + configuredOutputDir);
                    }
                } else if (!configuredOutputDir.mkdirs()
                        && !configuredOutputDir.isDirectory()) {
                    throw new IOException("Unable to create trace output directory: "
                            + configuredOutputDir);
                }
                // A killed replacement run must not inherit CLOSED evidence
                // from an older trace in the same directory.
                Files.deleteIfExists(new File(configuredOutputDir,
                        "streaming_trace_manifest.json").toPath());
                configuredWriter = new BufferedWriter(new FileWriter(
                        configuredTraceFile, false));
                ensureShutdownHookRegistered();

                // INITIALIZED is the release publication for every field
                // above.
                testName = configuredTestName;
                traceWriteFailure = false;
                outputDir = configuredOutputDir;
                traceWriter = configuredWriter;
                contextOnlyConcolicReplay = false;
                // The recording's schedule stands beside its trace, in the
                // same shape a replay session publishes it.
                ScheduleLog.installFile(configuredOutputDir);
                INITIALIZED.set(true);
            } catch (IOException | RuntimeException failure) {
                closeQuietly(configuredWriter);
                // A later recording call may retry after configuration or the
                // filesystem has been repaired.
                INITIALIZED.set(false);
                throw new IllegalStateException(
                        "Failed to initialize Causynth trace recorder at "
                                + configuredTraceFile, failure);
            }
        }
    }

    private static void ensureShutdownHookRegistered() {
        if (shutdownHookRegistered) {
            return;
        }
        Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
            @Override
            public void run() {
                shutdown();
            }
        }, "causynth-trace-shutdown"));
        shutdownHookRegistered = true;
    }

    private static void closeQuietly(BufferedWriter writer) {
        if (writer == null) {
            return;
        }
        try {
            writer.close();
        } catch (IOException ignored) {
        }
    }

    private static void shutdown() {
        synchronized (LOCK) {
            if (traceWriter != null) {
                try {
                    traceWriter.flush();
                    traceWriter.close();
                } catch (IOException failure) {
                    // A streaming trace is complete only after the buffered
                    // bytes have reached the underlying file and the writer
                    // has closed successfully.
                    traceWriteFailure = true;
                }
                traceWriter = null;
            }
            if (outputDir != null) {
                writeFileQuietly(new File(outputDir,
                                "streaming_trace_manifest.json"),
                        objectWithoutNulls(
                                "schemaVersion", 1,
                                "kind", "STREAMING_RUNTIME_TRACE",
                                // INCOMPLETE is a crash or a write that
                                // did not reach the file, and nothing else:
                                // a recorder that stopped at a count is a
                                // trace whose absence of events is silent.
                                "status", traceWriteFailure
                                        ? "INCOMPLETE" : "CLOSED"));
            }
        }
    }

    private static void aggregateStateTrace(
            File directory, File candidateGraph, File selectedSkeletons,
            File refinedGraph, String test, File planOutputDirectory,
            File recordingGaps, File staticScopeMap)
            throws IOException {
        synchronized (LOCK) {
            List<Map<String, Object>> earlierPassGaps =
                    readRecordingGaps(recordingGaps);
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, false);
            trace.sort();
            reattributeFramesToRegisteredOwners(trace);
            nameObservedObjectsFromContent(trace);
            Set<String> observedMethods = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                observedMethods.add(event.method);
            }
            // One decode of the selected skeletons for the whole bridge: the
            // activation planner, the graph refiner and the region finalizer
            // all take these rows, so the artifact is parsed and validated
            // once rather than once per stage.
            List<StaticProgram.RegionRow> skeletons =
                    StaticProgram.regionRows(
                            MapFields.readRows(selectedSkeletons),
                            RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                            selectedSkeletons);
            // One parse of the scope map for the whole bridge: the activation
            // planner joins its DECLARED_SITE rows with the recording, and
            // the region finalizer walks its WRITE_SITE rows.
            StaticScopeMap scopeMap = readScopeMap(staticScopeMap);
            RuntimeRegionPlanner.Result activationGraph =
                    RuntimeRegionPlanner.planSkeletonGraph(
                            skeletons, trace.methods,
                            trace.execution, trace.protocol,
                            declaredSites(scopeMap));
            RuntimeRefinedGraphBuilder.Result refinement =
                    RuntimeRefinedGraphBuilder.refine(candidateGraph,
                            skeletons,
                            activationGraph.runtimeInstances,
                            trace.methods, trace.execution,
                            trace.fields,
                            refinedGraph.toPath());
            // The refined rows returned by the builder are normalized to the
            // exact JSONL round-trip domain, so the finalizer sees precisely
            // what re-reading the artifact would produce, without parsing
            // the multi-hundred-MB file twice more.
            RuntimeSelectedRegionFinalizer.Result closure =
                    RuntimeSelectedRegionFinalizer.finalizeRegions(
                    refinement.rows, skeletons,
                    String.valueOf(selectedSkeletons),
                    observedMethods, activationGraph.runtimeInstances,
                    activationGraph.regionFolds,
                    runtimeObservations(trace.execution, trace.methods),
                    activationGraph.occurrenceLinks, scopeMap);
            for (Map<String, Object> row : closure.regions) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            // The plan's gaps are this pass's own plus the ones the
            // RECORDING stated: the recording has no session to hold a gap
            // row, and a gap it cannot state is one nobody hears about.
            List<Map<String, Object>> planGaps =
                    new ArrayList<>(closure.gaps);
            planGaps.addAll(trace.lineageGaps);
            // And the earlier recording pass's, which had no plan of its
            // own to carry them: one workload, one gap list.
            planGaps.addAll(earlierPassGaps);
            writeRuntimeRegionPlans(planOutputDirectory,
                    closure.regions, trace,
                    activationGraph.runtimeInstances, planGaps);
        }
    }

    /** Compact branch and primitive call-return rows used by the finalizer. */
    private static List<Map<String, Object>> runtimeObservations(
            Collection<RuntimeRegionPlanner.RuntimeEvent> events,
            Collection<RuntimeRegionPlanner.MethodEvent> methods) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (events == null) return result;
        Map<Long, RuntimeRegionPlanner.MethodEvent> contextByCall =
                new LinkedHashMap<>();
        if (methods != null) {
            for (RuntimeRegionPlanner.MethodEvent method : methods) {
                contextByCall.put(method.callId, method);
            }
        }
        for (RuntimeRegionPlanner.RuntimeEvent event : events) {
            boolean branch = "BRANCH".equals(event.kind)
                    && event.outcome != null;
            boolean callReturn = "CALL_SITE_RETURN".equals(event.kind)
                    && !event.primitiveValue.isEmpty();
            if ((!branch && !callReturn) || event.callId <= 0L
                    || event.siteId.isEmpty()) {
                continue;
            }
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("kind", event.kind);
            row.put("eventSeq", event.seq);
            row.put("method", event.method);
            row.put("callId", event.callId);
            row.put("siteId", event.siteId);
            if (branch) {
                row.put("outcome", event.outcome);
            } else {
                row.put("declaredCallee", event.declaredCallee);
                row.put("primitiveValue", event.primitiveValue);
            }
            RuntimeRegionPlanner.MethodEvent context =
                    contextByCall.get(event.callId);
            if (context != null && !context.sourceKey.isEmpty()) {
                row.put("callSourceKey", context.sourceKey);
                row.put("requestKey", context.requestKey);
                row.put("requestApi", context.requestApi);
            }
            if (branch && event.successorIndex != null) {
                row.put("successorIndex", event.successorIndex);
            }
            if (branch && !event.branchKind.isEmpty()) {
                row.put("branchKind", event.branchKind);
            }
            if (branch && !event.switchCaseKeys.isEmpty()) {
                row.put("switchCaseKeys", event.switchCaseKeys);
            }
            result.add(row);
        }
        return result;
    }

    /** Emits only static region skeletons and their concrete activation graph. */
    private static void aggregateSkeletonTrace(
            File directory, File candidateSkeletons,
            String test,
            File outputDirectory)
            throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, true);
            trace.sort();
            reattributeFramesToRegisteredOwners(trace);
            nameObservedObjectsFromContent(trace);
            File skeletons = new File(outputDirectory,
                    "region_skeletons.jsonl");
            if (candidateSkeletons == null) {
                throw new IOException("skeleton aggregation requires the "
                        + "schema-3 candidate skeleton artifact");
            }
            RuntimeRegionPlanner.Result graph =
                    RuntimeRegionPlanner.planSkeletonGraph(
                            StaticProgram.regionRows(
                                    MapFields.readRows(candidateSkeletons),
                                    RuntimeSelectedRegionFinalizer
                                            .SKELETON_KIND,
                                    candidateSkeletons),
                            trace.methods,
                            Collections.emptyList(),
                            Collections.emptyList(),
                            Collections.<String>emptySet());
            if (graph.staticRegionCount == 0) {
                throw new IOException(
                        "skeleton aggregation selected no static regions");
            }
            if (graph.runtimeInstances.isEmpty()) {
                throw new IOException(
                        "skeleton aggregation selected no runtime "
                                + "activations");
            }
            writeSelectedSkeletons(candidateSkeletons, skeletons,
                    graph.runtimeInstances);
            writeRecordingGaps(outputDirectory, trace.lineageGaps);
        }
    }

    /**
     * The name a recording pass publishes its own stated gaps under.
     *
     * <p>A pass with no plan artifact still states its refusals: the
     * REGION_SKELETON aggregation writes what it parsed here and the
     * REGION_STATE aggregation -- the pass that publishes the plan -- files
     * them with its own.  Before this channel existed, a gap pass 1 stated
     * lived only in a trace file nothing read again.</p>
     */
    static final String RECORDING_GAPS_FILE = "recording_gaps.jsonl";

    private static void writeRecordingGaps(
            File directory, List<Map<String, Object>> gaps)
            throws IOException {
        StringBuilder text = new StringBuilder();
        for (Map<String, Object> gap : gaps) {
            text.append(objectWithoutNulls(
                    "schemaVersion", gap.get("schemaVersion"),
                    "kind", gap.get("kind"),
                    "cls", gap.get("cls"),
                    "subject", gap.get("subject"),
                    "detail", gap.get("detail")));
            text.append('\n');
        }
        writeFile(new File(directory, RECORDING_GAPS_FILE), text.toString());
    }

    /**
     * The earlier recording pass's gap rows, in the plan-gap shape {@code
     * parseTraceLine} builds, refusing rather than defaulting: the file is
     * an artifact the earlier pass wrote, so its absence is a broken
     * pipeline and not an empty gap list.
     */
    private static List<Map<String, Object>> readRecordingGaps(File file)
            throws IOException {
        if (file == null || String.valueOf(file).trim().isEmpty()) {
            throw new IOException("--recording-gaps is required: the plan "
                    + "states the gaps of every recording pass");
        }
        if (!file.isFile()) {
            throw new IOException("no recording gap artifact at " + file
                    + "; the earlier recording pass must publish "
                    + RECORDING_GAPS_FILE + " before the plan is written");
        }
        List<Map<String, Object>> gaps = new ArrayList<>();
        ConcurrentHashMap<String, String> pool = new ConcurrentHashMap<>();
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                FlatJsonRow row = FlatJsonRow.parse(line, pool);
                if (row == null) {
                    throw new IOException("Malformed recording gap row in "
                            + file + ": " + line);
                }
                Map<String, Object> gap = new LinkedHashMap<>();
                gap.put("schemaVersion", row.intValue("schemaVersion", 1));
                gap.put("kind", row.stringValue("kind"));
                gap.put("cls", row.stringValue("cls"));
                gap.put("subject", row.stringValue("subject"));
                gap.put("detail", row.stringValue("detail"));
                gaps.add(gap);
            }
        }
        return gaps;
    }

    /**
     * The selected skeleton of a region a pass-1 activation entered is that
     * region's candidate skeleton with the anchor names the run observed.
     * Every other member is the candidate's own, so the two artifacts state
     * one static region and not two.
     *
     * <p>A region whose root the case declares symbolic is selected whether
     * or not pass 1 entered it, keeping its candidate anchors: roots are
     * manual, so PLAN instruments a declared method in pass 2 by declaration
     * (see {@code DeclaredSymbolicInputs}), and pass 2's own trace is then
     * the one authority on whether the site ran -- {@code
     * RuntimeSelectedRegionFinalizer} refuses {@code
     * DECLARED_INPUT_NEVER_ACTIVATED} there, with the recorded count.
     * Dropping it here instead would leave pass 2 blind to the site and turn
     * a workload that never reached it into an engine that never looked.</p>
     */
    private static void writeSelectedSkeletons(
            File candidates, File output,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        Map<String, String> anchorByRegion = new LinkedHashMap<>();
        Map<String, Set<String>> anchorsByRegion = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances) {
            String region = String.valueOf(instance.get("regionId"));
            // The first activation of a region names its anchor; every
            // activation of one region carries the same selection.
            anchorByRegion.putIfAbsent(region,
                    String.valueOf(instance.get("anchorMethod")));
            Set<String> anchors = anchorsByRegion.computeIfAbsent(
                    region, ignored -> new LinkedHashSet<>());
            Object encodedAnchors = instance.get("anchorMethods");
            if (encodedAnchors instanceof Collection<?>) {
                for (Object anchor : (Collection<?>) encodedAnchors) {
                    anchors.add(String.valueOf(anchor));
                }
            }
        }
        // The candidate rows are streamed straight through, so the one path
        // that would read what it is truncating fails before anything is
        // created.
        if (candidates.getCanonicalFile().equals(output.getCanonicalFile())) {
            throw new IOException("selected region skeletons must not "
                    + "overwrite the candidate skeletons: " + candidates);
        }
        // A row that fails the root check throws mid-stream, so the rows are
        // staged beside the artifact and moved onto it only once every row
        // has been written: a failed pass leaves the previous file intact
        // rather than a truncated one.  ArtifactIO owns that staging
        // envelope, including the non-atomic-move fallback.
        ArtifactIO.atomicReplace(output.toPath(), writer -> {
            try (BufferedReader reader = MapFields.rowReader(candidates)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.trim().isEmpty()) {
                        continue;
                    }
                    JsonObject row = JsonParser.parseString(line)
                            .getAsJsonObject();
                    String region = optionalString(row, "regionId");
                    String selectedAnchor = anchorByRegion.get(region);
                    boolean declaredRoot = optionalBool(row,
                            DeclaredSymbolicInputs.ROOT_FIELD, false);
                    if (selectedAnchor == null && !declaredRoot) {
                        continue;
                    }
                    String rootMethod = optionalString(row, "rootMethod");
                    boolean rooted = false;
                    for (JsonElement method : row.getAsJsonArray("methods")) {
                        rooted = rooted || rootMethod.equals(method.getAsString());
                    }
                    if (!rooted) {
                        throw new IOException("coalesced static region methods "
                                + "must contain the runtime root: " + region);
                    }
                    if (selectedAnchor != null) {
                        row.addProperty("anchorMethod", selectedAnchor);
                        JsonArray selectedAnchors = new JsonArray();
                        for (String anchor : anchorsByRegion.get(region)) {
                            selectedAnchors.add(anchor);
                        }
                        row.add("anchorMethods", selectedAnchors);
                    }
                    writer.write(row.toString());
                    writer.write('\n');
                }
            }
        });
    }

    private static void requireClosedTrace(File manifestFile)
            throws IOException {
        if (!manifestFile.isFile()) {
            throw new IOException("Runtime trace manifest not found: "
                    + manifestFile);
        }
        JsonElement parsed = JsonParser.parseString(new String(
                Files.readAllBytes(manifestFile.toPath()),
                StandardCharsets.UTF_8));
        JsonObject manifest = parsed.isJsonObject()
                ? parsed.getAsJsonObject() : new JsonObject();
        if (optionalInteger(manifest, "schemaVersion", -1) != 1
                || !"STREAMING_RUNTIME_TRACE".equals(
                optionalString(manifest, "kind"))
                || !"CLOSED".equals(optionalString(manifest, "status"))) {
            throw new IOException("Runtime trace is incomplete: "
                    + manifestFile);
        }
    }

    /**
     * Applies source registrations to frames entered after the registration.
     *
     * <p>A source row describes a lifecycle transition, not timeless object
     * metadata.  Applying the final owner table to earlier frames creates a
     * replay address that did not exist when those frames were entered: seed
     * planning then calls it {@code REGISTERED_SOURCE}, while replay quite
     * correctly observes the receiver before its alias has arrived.  Walk the
     * two already-sorted streams together so an owner becomes available only
     * after its durable source event.</p>
     */
    /**
     * Renames every object the recording observed from the content of its
     * first observation.
     *
     * <p>The recorder's {@code identity()} counter is exact inside one run
     * and arbitrary across two, so publishing it put a per-run number into
     * the plan's receiver anchors and into every id hashed from them.  This
     * replaces each recorded id with the content-addressed name
     * {@link RuntimeObjectIdentity} derives, which preserves "same object"
     * and "different object" within the recording while spelling the name
     * from the site that introduced the object.</p>
     *
     * <p>It runs after {@link #reattributeFramesToRegisteredOwners} so that
     * the source key in an address is the one the frame finally belongs to,
     * and before any planner or refiner reads the events, so no published
     * artifact can carry a recorded id.</p>
     */
    private static void nameObservedObjectsFromContent(TraceData trace) {
        RuntimeObjectIdentity identity = new RuntimeObjectIdentity();
        Map<Long, String> sourceKeyByCall = sourceKeyByCall(trace);
        for (TraceObservation observation : orderedObservations(trace)) {
            identity.observe(observation.objectId,
                    observation.address(sourceKeyByCall));
        }
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            event.objectId = identity.nameOf(event.objectId);
        }
        for (RuntimeRegionPlanner.RuntimeEvent event : trace.execution) {
            event.objectId = identity.nameOf(event.objectId);
        }
        for (RuntimeRegionPlanner.FieldAccessEvent event : trace.fields) {
            event.receiverObjectId = identity.nameOf(event.receiverObjectId);
            event.valueObjectId = identity.nameOf(event.valueObjectId);
        }
        for (SourceTraceEvent event : trace.sources) {
            event.objectId = identity.nameOf(event.objectId);
        }
    }

    /**
     * The logical source of each recorded frame, for the events that carry
     * only a call id.
     *
     * <p>An uninstrumented helper entered from an attributed frame has no
     * source of its own, so the parent chain is walked until one answers.</p>
     */
    private static Map<Long, String> sourceKeyByCall(TraceData trace) {
        Map<Long, String> own = new LinkedHashMap<>();
        Map<Long, Long> parents = new LinkedHashMap<>();
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            own.put(event.callId, MapFields.safe(event.sourceKey));
            parents.put(event.callId, event.parentCallId);
        }
        Map<Long, String> resolved = new LinkedHashMap<>();
        for (Long callId : own.keySet()) {
            Set<Long> walked = new LinkedHashSet<>();
            Long cursor = callId;
            String answer = "";
            while (cursor != null && walked.add(cursor)) {
                String candidate = own.get(cursor);
                if (candidate != null && !candidate.isEmpty()) {
                    answer = candidate;
                    break;
                }
                cursor = parents.get(cursor);
            }
            resolved.put(callId, answer);
        }
        return resolved;
    }

    /**
     * Every object slot of every recorded event, in recorded order.
     *
     * <p>The four event streams are each sorted by sequence; merging them on
     * sequence is what makes "first observation" mean the same thing however
     * the trace was batched across threads at load.</p>
     */
    private static List<TraceObservation> orderedObservations(
            TraceData trace) {
        List<TraceObservation> observations = new ArrayList<>();
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            observations.add(new TraceObservation(event.seq, event.objectId,
                    event.sourceKey, "METHOD_ENTER", event.method, "", -1,
                    "", event.receiverType, "objectId", event.callId));
        }
        for (RuntimeRegionPlanner.RuntimeEvent event : trace.execution) {
            observations.add(new TraceObservation(event.seq, event.objectId,
                    null, event.kind, event.method, event.siteId,
                    event.argumentIndex, "", event.runtimeType, "objectId",
                    event.callId));
        }
        for (RuntimeRegionPlanner.FieldAccessEvent event : trace.fields) {
            observations.add(new TraceObservation(event.seq,
                    event.receiverObjectId, null, event.kind, event.method,
                    event.siteId, -1, event.field, "",
                    "fieldReceiverObjectId", event.callId));
            observations.add(new TraceObservation(event.seq,
                    event.valueObjectId, null, event.kind, event.method,
                    event.siteId, -1, event.field, "", "valueObjectId",
                    event.callId));
        }
        for (SourceTraceEvent event : trace.sources) {
            observations.add(new TraceObservation(event.seq, event.objectId,
                    MapFields.safe(event.source == null ? ""
                            : event.source.key()), event.kind, "", "", -1,
                    "", "", "objectId", 0L));
        }
        // A stable order for the slots one event carries: the sequence alone
        // does not separate a field access's receiver from its value.
        observations.sort((left, right) -> {
            int bySeq = Long.compare(left.seq, right.seq);
            return bySeq != 0 ? bySeq : left.slot.compareTo(right.slot);
        });
        return observations;
    }

    /** One object slot of one recorded event. */
    private static final class TraceObservation {
        private final long seq;
        private final int objectId;
        private final String sourceKey;
        private final String eventKind;
        private final String method;
        private final String siteId;
        private final int argumentIndex;
        private final String field;
        private final String runtimeType;
        private final String slot;
        private final long callId;

        private TraceObservation(long seq, int objectId, String sourceKey,
                                 String eventKind, String method,
                                 String siteId, int argumentIndex,
                                 String field, String runtimeType,
                                 String slot, long callId) {
            this.seq = seq;
            this.objectId = objectId;
            this.sourceKey = sourceKey;
            this.eventKind = MapFields.safe(eventKind);
            this.method = MapFields.safe(method);
            this.siteId = MapFields.safe(siteId);
            this.argumentIndex = argumentIndex;
            this.field = MapFields.safe(field);
            this.runtimeType = MapFields.safe(runtimeType);
            this.slot = MapFields.safe(slot);
            this.callId = callId;
        }

        private String address(Map<Long, String> sourceKeyByCall) {
            String source = sourceKey != null ? sourceKey
                    : MapFields.safe(sourceKeyByCall.get(callId));
            return RuntimeObjectIdentity.address(source, eventKind, method,
                    siteId, argumentIndex, field, runtimeType, slot);
        }
    }

    private static void reattributeFramesToRegisteredOwners(TraceData trace) {
        Map<Integer, SourceRef> owners = new LinkedHashMap<>();
        Set<Integer> disputed = new LinkedHashSet<>();
        Map<Long, SourceRef> recordedSources = new LinkedHashMap<>();
        Map<Long, SourceRef> registeredContexts = new LinkedHashMap<>();
        int sourceIndex = 0;
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            while (sourceIndex < trace.sources.size()
                    && trace.sources.get(sourceIndex).seq < event.seq) {
                applySourceLifecycle(trace.sources.get(sourceIndex++),
                        owners, disputed);
            }
            SourceRef recorded = event.source;
            SourceRef owner = owners.get(event.objectId);
            // The receiver's own registration, and not the calling frame's.
            boolean receiverOwned = owner != null;
            if (owner == null) {
                SourceRef parentContext = registeredContexts.get(
                        event.parentCallId);
                SourceRef parentRecorded = recordedSources.get(
                        event.parentCallId);
                boolean sameRecordedContext = recorded == null
                        ? parentRecorded == null
                        : recorded.equals(parentRecorded);
                if (parentContext != null && sameRecordedContext) {
                    owner = parentContext;
                }
            }
            if (owner != null) {
                event.reattribute(owner, receiverOwned);
                registeredContexts.put(event.callId, owner);
            }
            recordedSources.put(event.callId, recorded);
        }
    }

    /** Advances one object's source binding at its recorded lifecycle point. */
    private static void applySourceLifecycle(
            SourceTraceEvent event, Map<Integer, SourceRef> owners,
            Set<Integer> disputed) {
        if (event.objectId <= 0) return;
        boolean restart = "SOURCE_RESTART".equals(event.kind);
        if (!restart && !"SOURCE_REGISTER".equals(event.kind)
                && !"SOURCE_ALIAS".equals(event.kind)) {
            return;
        }
        SourceRef owner = restart ? event.relatedSource : event.source;
        if (owner == null) return;
        if (restart) {
            owners.put(event.objectId, owner);
            disputed.remove(event.objectId);
            return;
        }
        if (disputed.contains(event.objectId)) return;
        SourceRef previous = owners.get(event.objectId);
        if (previous == null || previous.equals(owner)) {
            owners.put(event.objectId, owner);
        } else {
            owners.remove(event.objectId);
            disputed.add(event.objectId);
        }
    }

    private static void clearInMemoryTrace() {
        INITIALIZED.set(false);
        EVENT_COUNTER.set(0L);
        ACTIVE_CALLS.remove();
        ACTIVE_CALL_SITES.remove();
        RuntimeTraceContext.resetForTests();
        OBJECT_IDS.clear();
        nextObjectId = 1;
        contextOnlyConcolicReplay = false;
        recordingEnabled = true;
        traceWriteFailure = false;
        traceWriter = null;
    }

    /** Number of worker threads used by offline trace aggregation parsing. */
    private static int aggregationThreads() {
        return Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
    }

    private static TraceData loadExistingTrace(
            File file, String test, boolean skeletonOnly) throws IOException {
        if (file == null || !file.isFile()) {
            throw new IOException("Runtime trace not found: " + file);
        }
        int threads = aggregationThreads();
        ConcurrentHashMap<String, String> pool = new ConcurrentHashMap<>();
        TraceData trace = new TraceData();
        ExecutorService executor = Executors.newFixedThreadPool(threads,
                runnable -> {
                    Thread thread = new Thread(runnable,
                            "causynth-trace-parse");
                    thread.setDaemon(true);
                    return thread;
                });
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            // Batches are parsed concurrently but merged strictly in file
            // order, so the produced event lists are byte-for-byte the same
            // as a sequential parse.
            ArrayDeque<Future<TraceData>> pending = new ArrayDeque<>();
            int batchCapacity = 16384;
            List<String> batch = new ArrayList<>(batchCapacity);
            int firstLineNumber = 1;
            int lineNumber = 0;
            String line;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                batch.add(line);
                if (batch.size() >= batchCapacity) {
                    submitBatch(executor, pending, trace, batch,
                            firstLineNumber, file, test, skeletonOnly, pool,
                            threads);
                    firstLineNumber = lineNumber + 1;
                    batch = new ArrayList<>(batchCapacity);
                }
            }
            if (!batch.isEmpty()) {
                submitBatch(executor, pending, trace, batch,
                        firstLineNumber, file, test, skeletonOnly, pool,
                        threads);
            }
            while (!pending.isEmpty()) {
                mergeBatch(trace, pending.removeFirst());
            }
        } finally {
            executor.shutdownNow();
        }
        return trace;
    }

    private static void submitBatch(
            ExecutorService executor, ArrayDeque<Future<TraceData>> pending,
            TraceData trace, List<String> batch, int firstLineNumber,
            File file, String test, boolean skeletonOnly,
            ConcurrentHashMap<String, String> pool, int threads)
            throws IOException {
        pending.addLast(executor.submit(() -> parseTraceBatch(batch,
                firstLineNumber, file, test, skeletonOnly, pool)));
        // Bound the number of in-flight batches; the head of the queue is
        // always the oldest batch, so merging preserves file order.
        while (pending.size() > threads * 2) {
            mergeBatch(trace, pending.removeFirst());
        }
    }

    private static void mergeBatch(TraceData trace,
                                   Future<TraceData> future)
            throws IOException {
        try {
            TraceData part = future.get();
            trace.methods.addAll(part.methods);
            trace.fields.addAll(part.fields);
            trace.execution.addAll(part.execution);
            trace.protocol.addAll(part.protocol);
            trace.sources.addAll(part.sources);
            // Every list the parse fills: a gap the recording stated and
            // this merge dropped is a refusal nobody hears about.
            trace.lineageGaps.addAll(part.lineageGaps);
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("trace parse interrupted", interrupted);
        } catch (ExecutionException failure) {
            Throwable cause = failure.getCause();
            if (cause instanceof IOException) {
                throw (IOException) cause;
            }
            if (cause instanceof RuntimeException) {
                throw (RuntimeException) cause;
            }
            throw new IOException("trace parse failed", cause);
        }
    }

    private static TraceData parseTraceBatch(
            List<String> lines, int firstLineNumber, File file, String test,
            boolean skeletonOnly, ConcurrentHashMap<String, String> pool)
            throws IOException {
        TraceData trace = new TraceData();
        for (int index = 0; index < lines.size(); index++) {
            parseTraceLine(trace, lines.get(index),
                    firstLineNumber + index, file, test, skeletonOnly, pool);
        }
        return trace;
    }

    private static void parseTraceLine(
            TraceData trace, String line, int lineNumber, File file,
            String test, boolean skeletonOnly,
            ConcurrentHashMap<String, String> pool) throws IOException {
        FlatJsonRow row = FlatJsonRow.parse(line, pool);
        if (row == null) {
            throw new IOException("Malformed runtime trace row "
                    + lineNumber + " in " + file);
        }
        long schemaVersion = row.longValue("schemaVersion", -1L);
        if (schemaVersion != 3L) {
            throw new IOException("Unsupported runtime trace row: " + line);
        }
        String eventKind = row.stringValue("event");
        if ("METHOD_ENTER".equals(eventKind)) {
            long seq = row.longValue("seq", 0L);
            trace.methods.add(new RuntimeRegionPlanner.MethodEvent(
                    seq,
                    test,
                    row.stringValue("threadName"),
                    row.longValue("tid", 0L),
                    row.stringValue("method"),
                    row.intValue("objectId", 0),
                    row.stringValue("receiverType"),
                    row.longValue("callId", seq),
                    row.longValue("parentCallId", 0L),
                    row.longValue("parentSiteId", 0L),
                    row.longValue("laneId", 0L),
                    row.longValue("spanId", 0L),
                    row.longValue("remoteParentSpanId", 0L),
                    sourceRef(row),
                    row.longValue("receiverAttributed", 0L) != 0L,
                    row.stringValue("requestKey"),
                    row.stringValue("requestApi"),
                    row.stringValue("occurrenceAddress"),
                    row.longValue("regionFolded", 0L) != 0L));
        } else if (!skeletonOnly && ("FIELD_READ".equals(eventKind)
                || "FIELD_WRITE".equals(eventKind))) {
            trace.fields.add(
                    new RuntimeRegionPlanner.FieldAccessEvent(
                    row.longValue("seq", 0L),
                    eventKind,
                    row.stringValue("method"),
                    row.longValue("callId", 0L),
                    row.intValue("unitIndex", -1),
                    row.stringValue("siteId"),
                    row.stringValue("field"),
                    row.intValue("fieldReceiverObjectId", 0),
                    row.intValue("valueObjectId", 0),
                    row.stringValue("primitiveValue")));
        } else if ("EXCHANGE_SEND".equals(eventKind)
                || "EXCHANGE_RECEIVE".equals(eventKind)) {
            trace.protocol.add(new RuntimeRegionPlanner.ProtocolEvent(
                    row.longValue("seq", 0L),
                    "EXCHANGE_SEND".equals(eventKind) ? "SEND" : "RECEIVE",
                    row.stringValue("transport"),
                    row.stringValue("correlationId"),
                    row.stringValue("attemptId"),
                    row.stringValue("half"),
                    row.stringValue("threadName"),
                    row.longValue("tid", 0L),
                    row.stringValue("method"),
                    row.longValue("callId", 0L),
                    row.longValue("invocationId", 0L),
                    row.stringValue("declaredCallee"),
                    row.longValue("laneId", 0L),
                    row.longValue("spanId", 0L),
                    row.longValue("remoteParentSpanId", 0L),
                    sourceRef(row), row.stringValue("requestKey"),
                    row.stringValue("requestApi"),
                    row.stringValue("producerEndpointId"),
                    row.stringValue("producerEndpoint")));
        } else if (LINEAGE_GAP_EVENT.equals(eventKind)) {
            Map<String, Object> gap = new LinkedHashMap<>();
            gap.put("schemaVersion", 1);
            gap.put("kind", row.stringValue("kind"));
            gap.put("cls", row.stringValue("cls"));
            gap.put("subject", row.stringValue("subject"));
            gap.put("detail", row.stringValue("detail"));
            trace.lineageGaps.add(gap);
        } else if ("SOURCE_REGISTER".equals(eventKind)
                || "SOURCE_ALIAS".equals(eventKind)
                || "SOURCE_RESTART".equals(eventKind)) {
            trace.sources.add(new SourceTraceEvent(
                    row.longValue("seq", 0L), eventKind,
                    sourceRef(row), relatedSourceRef(row),
                    row.intValue("objectId", 0)));
        } else if ((!skeletonOnly || "CALL_SITE_ENTER".equals(eventKind))
                && isExecutionEventKind(eventKind)) {
            trace.execution.add(new RuntimeRegionPlanner.RuntimeEvent(
                    row.longValue("seq", 0L), eventKind,
                    row.stringValue("method"),
                    row.longValue("callId", 0L),
                    row.longValue("invocationId", 0L),
                    row.stringValue("siteId"),
                    row.stringValue("declaredCallee"),
                    row.intValue("argumentIndex", -1),
                    row.stringValue("runtimeType"),
                    row.intValue("objectId", 0),
                    row.stringValue("primitiveValue"),
                    row.has("outcome")
                            ? row.booleanValue("outcome", false) : null,
                    row.has("successorIndex")
                            ? row.intValue("successorIndex", -1)
                            : null,
                    row.stringValue("branchKind"),
                    row.stringValue("switchCaseKeys")));
        }
    }

    private static boolean isExecutionEventKind(String kind) {
        return "METHOD_ARGUMENT".equals(kind)
                || "METHOD_EXIT_NORMAL".equals(kind)
                || "METHOD_EXIT_THROW".equals(kind)
                || "CALL_SITE_ENTER".equals(kind)
                || "CALL_ARGUMENT".equals(kind)
                || "CALL_SITE_RETURN".equals(kind)
                || "CALL_SITE_THROW".equals(kind)
                || "CALL_SITE_INCOMPLETE".equals(kind)
                || "BRANCH".equals(kind);
    }

    private static void writeTraceLine(RuntimeRegionPlanner.MethodEvent event) {
        if (!recordingEnabled) return;
        writeTraceRow(
                "schemaVersion", 3,
                "event", "METHOD_ENTER",
                "seq", event.seq,
                "threadName", event.threadName,
                "tid", event.tid,
                "method", event.method,
                "objectId", event.objectId,
                "receiverType", event.receiverType,
                "callId", event.callId,
                "parentCallId", event.parentCallId,
                "parentSiteId", event.parentSiteId,
                "laneId", event.laneId,
                "spanId", event.spanId,
                "remoteParentSpanId", event.remoteParentSpanId,
                "sourceKind", sourceKind(event.source),
                "sourceRole", sourceRole(event.source),
                "sourceId", sourceId(event.source),
                "sourceEpoch", sourceEpoch(event.source),
                "sourceKey", sourceKey(event.source),
                // Absent rather than false: an activation the context named
                // is the ordinary case and the trace is written per call.
                "receiverAttributed", event.receiverAttributed ? 1 : null,
                "requestKey", event.requestKey,
                "requestApi", event.requestApi,
                // Identity v3, computed here, where the activation ran, by
                // the one function (Identity.occurrence).  Present only on
                // the entry of a region root; every other entry is a plain
                // frame of the trace.
                "occurrenceAddress", event.occurrenceAddress.isEmpty()
                        ? null : event.occurrenceAddress,
                // F1: this entry folded into the occurrence already running,
                // so it states no address and PLAN builds no activation for
                // it.  Absent rather than false, like every other flag here:
                // an entry that opens its own occurrence is the ordinary
                // case and the trace is written per call.
                "regionFolded", event.regionFolded ? 1 : null);
    }

    private static void writeFieldTraceLine(
            RuntimeRegionPlanner.FieldAccessEvent event) {
        if (!recordingEnabled) return;
        writeTraceRow(
                "schemaVersion", 3,
                "event", event.kind,
                "seq", event.seq,
                "method", event.method,
                "callId", event.callId,
                "siteId", event.siteId,
                "unitIndex", event.unitIndex,
                "field", event.field,
                "fieldReceiverObjectId", event.receiverObjectId,
                "valueObjectId", event.valueObjectId,
                "primitiveValue", event.primitiveValue);
    }

    /**
     * The row kind one recorded protocol leg is written under.  A leg is a
     * SEND or a RECEIVE and nothing else -- {@link #recordExchange} refuses
     * every other direction by name before an event exists -- so a third
     * spelling here would be a row kind no parse branch reads.
     */
    static String protocolEventKind(String direction) {
        if ("SEND".equals(direction)) return "EXCHANGE_SEND";
        if ("RECEIVE".equals(direction)) return "EXCHANGE_RECEIVE";
        throw new IllegalStateException("EXCHANGE_DIRECTION_UNSTATED: "
                + "a protocol leg states SEND or RECEIVE, not "
                + direction);
    }

    private static void writeProtocolTraceLine(
            RuntimeRegionPlanner.ProtocolEvent event) {
        if (!recordingEnabled) return;
        String kind = protocolEventKind(event.direction);
        writeTraceRow(
                "schemaVersion", 3,
                "event", kind,
                "seq", event.seq,
                "transport", event.transport,
                "correlationId", event.correlationId,
                "attemptId", event.attemptId,
                "half", event.half,
                "threadName", event.threadName,
                "tid", event.tid,
                "method", event.method,
                "callId", event.callId,
                "invocationId", event.invocationId,
                "declaredCallee", event.declaredCallee,
                "laneId", event.laneId,
                "spanId", event.spanId,
                "remoteParentSpanId", event.remoteParentSpanId,
                "sourceKind", sourceKind(event.source),
                "sourceRole", sourceRole(event.source),
                "sourceId", sourceId(event.source),
                "sourceEpoch", sourceEpoch(event.source),
                "sourceKey", sourceKey(event.source),
                "requestKey", event.requestKey,
                "requestApi", event.requestApi,
                // The endpoint this leg's sender minted, digest and
                // components both: an anchor downstream is the digest, and
                // the components are what tells two of them apart.  Absent
                // on a delivery, which mints none.
                "producerEndpointId", event.producerEndpointId.isEmpty()
                        ? null : event.producerEndpointId,
                "producerEndpoint", event.producerEndpoint.isEmpty()
                        ? null : event.producerEndpoint);
    }

    private static void writeSourceTraceLine(String event, SourceRef source,
                                             SourceRef related,
                                             long requestId, String detail,
                                             int objectId) {
        if (contextOnlyConcolicReplay || traceWriter == null) return;
        RuntimeTraceContext.View context = RuntimeTraceContext.current();
        long seq = EVENT_COUNTER.incrementAndGet();
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 3,
                    "event", event,
                    "seq", seq,
                    "sourceKind", sourceKind(source),
                    "sourceRole", sourceRole(source),
                    "sourceId", sourceId(source),
                    "sourceEpoch", sourceEpoch(source),
                    "sourceKey", sourceKey(source),
                    "relatedSourceKind", sourceKind(related),
                    "relatedSourceRole", sourceRole(related),
                    "relatedSourceId", sourceId(related),
                    "relatedSourceEpoch", sourceEpoch(related),
                    "relatedSourceKey", sourceKey(related),
                    "requestId", requestId <= 0L ? null : requestId,
                    "requestKey", context.requestKey,
                    "requestApi", context.requestApi,
                    // The identity that makes this row joinable to the
                    // activations of the object it names.
                    "objectId", objectId <= 0 ? null : objectId,
                    event.startsWith("REQUEST_") ? "apiName" : "aliasClass",
                    detail,
                    "laneId", context.laneId,
                    "spanId", context.spanId);
        }
    }

    private static void writeExecutionTraceLine(ExecutionEvent event) {
        if (event == null || !recordingEnabled) return;
        writeTraceRow(
                "schemaVersion", 3,
                "event", event.kind,
                "seq", event.id,
                "method", event.method,
                "callId", event.callId,
                "invocationId", event.invocationId,
                "siteId", event.siteId,
                "declaredCallee", event.declaredCallee,
                "argumentIndex", event.argumentIndex,
                "runtimeType", event.runtimeType,
                "objectId", event.objectId,
                "primitiveValue", event.primitiveValue,
                "outcome", event.outcome,
                "branchKind", event.branchKind,
                "successorIndex", event.successorIndex,
                "switchCaseKeys", event.switchCaseKeys);
    }

    private static void writeTraceRow(Object... fields) {
        if (traceWriter == null) return;
        try {
            traceWriter.write(objectWithoutNulls(fields));
            traceWriter.newLine();
        } catch (IOException ignored) {
            traceWriteFailure = true;
        }
    }

    private static Map<String, String> parseArgs(String[] args) {
        Map<String, String> params = new LinkedHashMap<>();
        if (args == null) {
            return params;
        }
        for (int i = 0; i < args.length; i++) {
            String arg = args[i];
            if (arg == null || !arg.startsWith("--")) {
                continue;
            }
            String key = arg.substring(2);
            String value = "true";
            if (i + 1 < args.length && args[i + 1] != null
                    && !args[i + 1].startsWith("--")) {
                value = args[++i];
            }
            params.put(key, value);
        }
        return params;
    }

    private static String requiredArg(Map<String, String> params,
                                      String name) {
        String value = params.get(name);
        if (value == null || value.trim().isEmpty()) {
            throw new IllegalArgumentException("--" + name + " is required");
        }
        return value.trim();
    }

    /** Binds frozen static regions to concrete same-thread invocations. */
    private static void writeRuntimeRegionPlans(
            File directory,
            List<Map<String, Object>> regions, TraceData trace,
            Collection<Map<String, Object>> runtimeSeeds,
            Collection<Map<String, Object>> planGaps) throws IOException {
        writeFile(new File(directory, "concolic_region_plan.jsonl"),
                RuntimeRegionPlanner.plan(regions,
                        "runtime region closure",
                        runtimeSeeds, trace.methods, trace.execution,
                        trace.fields, trace.protocol,
                        planGaps).runtimePlanJsonl());
    }

    /**
     * The sites the one scoping artifact names as places a declared value
     * enters, as {@code <siteId>\n<callee>}.
     *
     * <p>Scope, read from the map that publishes it, so the recording's own
     * side of a declared port is stated at exactly the sites the static pass
     * named -- not at every call the run made, and not at a set this stage
     * re-derives from the graph.  Admission is still the scheduler's.</p>
     */
    /** The epoch's scope map, refused when it states no site at all. */
    private static StaticScopeMap readScopeMap(File staticScopeMap)
            throws IOException {
        StaticScopeMap map = StaticScopeMap.read(staticScopeMap.toPath());
        if (!map.stated()) {
            throw new IOException("static scope map states no site: "
                    + staticScopeMap);
        }
        return map;
    }

    private static Set<String> declaredSites(StaticScopeMap map) {
        Set<String> sites = new LinkedHashSet<>();
        for (StaticScopeMap.Site site : map.declaredSites()) {
            sites.add(site.siteId + "\n" + site.declaredCallee);
        }
        return sites;
    }

    private static void writeFile(File file, String value) throws IOException {
        File parent = file.getParentFile();
        if (parent != null) {
            Files.createDirectories(parent.toPath());
        }
        Files.write(file.toPath(), value.getBytes(StandardCharsets.UTF_8));
    }

    private static void writeFileQuietly(File file, String value) {
        try {
            writeFile(file, value);
        } catch (IOException ignored) {
            // Shutdown diagnostics are best effort; offline aggregation uses
            // the throwing writer above and therefore fails closed.
        }
    }

    private static final class ExecutionEvent {
        private long id;
        private String kind = "";
        private String method = "";
        private long callId;
        private long invocationId;
        private String siteId = "";
        private String declaredCallee = "";
        private int argumentIndex = -1;
        private String runtimeType = "";
        private int objectId;
        private String primitiveValue = "";
        private Boolean outcome;
        private String branchKind = "";
        private Integer successorIndex;
        private String switchCaseKeys = "";
    }

    static final class TraceData {
        final List<RuntimeRegionPlanner.MethodEvent> methods =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.RuntimeEvent> execution =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.ProtocolEvent> protocol =
                new ArrayList<>();
        final List<SourceTraceEvent> sources = new ArrayList<>();
        /** Lineage gaps the recording stated, as plan-gap rows. */
        final List<Map<String, Object>> lineageGaps = new ArrayList<>();

        private void sort() {
            methods.sort((left, right) -> Long.compare(left.seq, right.seq));
            fields.sort((left, right) -> Long.compare(left.seq, right.seq));
            execution.sort((left, right) ->
                    Long.compare(left.seq, right.seq));
            protocol.sort((left, right) -> Long.compare(left.seq, right.seq));
            sources.sort((left, right) -> Long.compare(left.seq, right.seq));
        }
    }

    private static final class SourceTraceEvent {
        private final long seq;
        private final String kind;
        private final SourceRef source;
        private final SourceRef relatedSource;
        /** Identity of the object this row registered, or 0.  Not final:
         * renamed to its content-addressed name once the trace has
         * loaded. */
        private int objectId;

        private SourceTraceEvent(long seq, String kind, SourceRef source,
                                 SourceRef relatedSource, int objectId) {
            this.objectId = objectId;
            this.seq = seq;
            this.kind = MapFields.safe(kind);
            this.source = source;
            this.relatedSource = relatedSource;
        }
    }

    private static final class ActiveCall {
        private final long callId;
        private final long parentSiteId;
        private final String method;
        private final long spanId;
        private final boolean rootContext;
        /** Whether this activation pushed an execution-index frame. */
        private final boolean regionFrame;

        private ActiveCall(long callId, long parentSiteId, String method,
                           long spanId, boolean rootContext,
                           boolean regionFrame) {
            this.callId = callId;
            this.parentSiteId = parentSiteId;
            this.method = MapFields.safe(method);
            this.spanId = spanId;
            this.rootContext = rootContext;
            this.regionFrame = regionFrame;
        }
    }

    /**
     * One flat JSON trace row: an object whose values are only strings,
     * numbers, booleans, or null.
     */
    private static final class FlatJsonRow {
        private final JsonObject row;

        private FlatJsonRow(JsonObject row) {
            this.row = row;
        }

        private static FlatJsonRow parse(
                String line, ConcurrentHashMap<String, String> pool) {
            JsonElement parsed;
            try {
                parsed = JsonParser.parseString(line);
            } catch (RuntimeException malformed) {
                return null;
            }
            if (parsed == null || !parsed.isJsonObject()) return null;
            JsonObject interned = new JsonObject();
            for (Map.Entry<String, JsonElement> member
                    : parsed.getAsJsonObject().entrySet()) {
                JsonElement value = member.getValue();
                if (!value.isJsonPrimitive() && !value.isJsonNull()) {
                    return null;
                }
                if (value.isJsonPrimitive()
                        && value.getAsJsonPrimitive().isString()) {
                    value = new JsonPrimitive(
                            intern(pool, value.getAsString()));
                }
                // Later duplicate keys win, matching JsonObject.add.
                interned.add(intern(pool, member.getKey()), value);
            }
            return new FlatJsonRow(interned);
        }

        private static String intern(ConcurrentHashMap<String, String> pool,
                                     String value) {
            String existing = pool.putIfAbsent(value, value);
            return existing != null ? existing : value;
        }

        private boolean has(String key) {
            return row.has(key);
        }

        private String stringValue(String key) {
            JsonElement value = row.get(key);
            return value == null || value.isJsonNull()
                    ? "" : value.getAsString();
        }

        private long longValue(String key, long fallback) {
            JsonElement value = row.get(key);
            if (value == null || value.isJsonNull()) return fallback;
            try {
                return value.getAsLong();
            } catch (RuntimeException malformed) {
                return fallback;
            }
        }

        private int intValue(String key, int fallback) {
            JsonElement value = row.get(key);
            if (value == null || value.isJsonNull()) return fallback;
            try {
                return value.getAsInt();
            } catch (RuntimeException malformed) {
                return fallback;
            }
        }

        private boolean booleanValue(String key, boolean fallback) {
            JsonElement value = row.get(key);
            // JsonPrimitive.getAsBoolean parses any non-boolean primitive
            // with Boolean.parseBoolean.
            return value == null || value.isJsonNull()
                    ? fallback : value.getAsBoolean();
        }
    }

    private static final class ActiveCallSite {
        private final long invocationId;
        private final long ownerCallId;
        private final String siteId;
        private final String caller;
        private final String declaredCallee;

        private ActiveCallSite(long invocationId, long ownerCallId,
                               String siteId, String caller,
                               String declaredCallee) {
            this.invocationId = invocationId;
            this.ownerCallId = ownerCallId;
            this.siteId = MapFields.safe(siteId);
            this.caller = MapFields.safe(caller);
            this.declaredCallee = MapFields.safe(declaredCallee);
        }
    }

    /** Immutable public view of one exact active call-site invocation. */
    public static final class ActiveCallSiteContext {
        private final String siteId;
        private final String declaredCallee;
        private final long ownerCallId;
        private final long invocationId;

        private ActiveCallSiteContext(String siteId, String declaredCallee,
                                      long ownerCallId, long invocationId) {
            this.siteId = MapFields.safe(siteId);
            this.declaredCallee = MapFields.safe(declaredCallee);
            this.ownerCallId = ownerCallId;
            this.invocationId = invocationId;
        }

        public String siteId() { return siteId; }

        public String declaredCallee() { return declaredCallee; }

        public long ownerCallId() { return ownerCallId; }

        public long invocationId() { return invocationId; }
    }

}
