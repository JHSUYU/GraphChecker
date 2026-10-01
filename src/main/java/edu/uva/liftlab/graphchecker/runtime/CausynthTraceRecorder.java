package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import com.google.gson.JsonElement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.contract.Endpoint;
import edu.uva.liftlab.graphchecker.contract.GapClass;
import edu.uva.liftlab.graphchecker.contract.GapKind;
import edu.uva.liftlab.graphchecker.contract.OccurrenceAddress;
import edu.uva.liftlab.graphchecker.contract.ScheduleEvent;
import edu.uva.liftlab.graphchecker.contract.SessionDir;
import edu.uva.liftlab.graphchecker.contract.SessionReader;
import edu.uva.liftlab.graphchecker.option.LongOptions;
import edu.uva.liftlab.graphchecker.smt.ArtifactIO;
import edu.uva.liftlab.graphchecker.plan.RuntimeWorkflowDiscovery;
import edu.uva.liftlab.graphchecker.plan.SiteId;
import edu.uva.liftlab.graphchecker.plan.StaticScopeMap;
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

    private static volatile File outputDir;
    private static volatile String testName;
    /** Guarded by {@link #LOCK}; persisted in the streaming close manifest. */
    private static boolean traceWriteFailure;
    private static BufferedWriter traceWriter;
    /** Guarded by {@link #LOCK}; a reset must not install duplicate hooks. */
    private static boolean shutdownHookRegistered;

    /** {@code -Dcausynth.debug.producers=true}: print every send's producer. */
    private static final boolean DEBUG_PRODUCERS =
            Boolean.getBoolean("causynth.debug.producers");

    private CausynthTraceRecorder() {
    }

    /** Opens the workload-defined trace boundary after source initialization. */
    public static void startRecording() {
        initialize();
        RecordingWindow.open();
        // Enforced prefix: running timed waits convert to virtual time.
        if (ScheduleLog.enforcing()) TimedWaits.windowOpened();
    }

    /**
     * The workload's test is over: its teardown (a cluster shutting its
     * nodes down) is no part of what either run controls, and neither
     * records nor holds it.
     */
    public static void stopRecording() {
        if (!RecordingWindow.opened()) return;
        RecordingWindow.close();
        ScheduleLog.windowClosed();
    }

    /**
     * Whether this JVM runs a world the engine chose -- a concolic replay,
     * or a native reproduction planting one ({@link RecordingPlant}) --
     * rather than the recording or a native run; workload checks of the
     * recording's world do not hold here.
     */
    public static boolean replaying() {
        return RuntimeTraceMode.configured() == RuntimeTraceMode.REPLAY_CONTEXT
                || RecordingPlant.planting();
    }

    /**
     * Aggregates one recording for every target it was made for: {@code
     * --trace-dir --test}, one {@code --target <name>=<candidate-graph>,
     * <static-scope-map>,<region-skeletons>,<output-dir>} per target (its
     * static slice, and where its runtime region plan goes), optionally
     * {@code --target-occurrence} (the case's declaration, resolved here
     * against each target's observed occurrences; a sweep's {@code first}
     * when not stated) and {@code --summary <file>}, where each target's
     * {@link TargetOutcome} is written.  A target the recording does not serve fails alone,
     * named on stderr; the run exits 1 when no target was served, or when the
     * trace itself cannot be read.
     */
    public static void main(String[] args) {
        LongOptions options = LongOptions.parse(args);
        File directory = new File(required(options, "trace-dir"));
        String test = required(options, "test");
        String declared = options.value("target-occurrence",
                RuntimeWorkflowDiscovery.FIRST);
        List<AggregationTarget> targets = new ArrayList<>();
        for (String target : options.all("target")) {
            targets.add(AggregationTarget.parse(target));
        }
        if (targets.isEmpty()) {
            throw new IllegalArgumentException("--target is required");
        }
        Map<String, TargetOutcome> outcomes = new LinkedHashMap<>();
        Throwable unread = null;
        try {
            outcomes = aggregateTargets(readStateTrace(directory, test),
                    targets, declared);
        } catch (Throwable throwable) {
            // The trace itself: every target's outcome.
            unread = throwable;
            for (AggregationTarget target : targets) {
                outcomes.put(target.name,
                        TargetOutcome.refused(target.name, throwable));
            }
        }
        String summary = options.value("summary", null);
        if (summary != null) {
            JsonObject rows = new JsonObject();
            for (TargetOutcome outcome : outcomes.values()) {
                rows.add(outcome.name, outcome.json());
            }
            JsonObject json = new JsonObject();
            json.add("targets", rows);
            try {
                writeFile(new File(summary.trim()), json + "\n");
            } catch (IOException failure) {
                unread = unread == null ? failure : unread;
            }
        }
        if (unread != null) {
            System.err.println("Failed to aggregate Causynth runtime trace: "
                    + unread);
            unread.printStackTrace(System.err);
            System.exit(1);
            return;
        }
        boolean served = false;
        for (TargetOutcome outcome : outcomes.values()) {
            served |= outcome.activated();
            if (!outcome.activated()) {
                System.err.println("Failed to aggregate Causynth runtime "
                        + "trace: " + outcome.name + ": " + outcome.detail);
            }
        }
        if (!served) System.exit(1);
    }

    /** One target of an aggregation: its name, its static slice (candidate
     *  graph, scope map, candidate region skeletons) and where its runtime
     *  region plan goes. */
    static final class AggregationTarget {
        final String name;
        final File graph;
        final File scopeMap;
        final File skeletons;
        final File outputDir;

        AggregationTarget(String name, File graph, File scopeMap,
                          File skeletons, File outputDir) {
            this.name = name;
            this.graph = graph;
            this.scopeMap = scopeMap;
            this.skeletons = skeletons;
            this.outputDir = outputDir;
        }

        /** {@code <name>=<candidate-graph>,<static-scope-map>,
         *  <region-skeletons>,<output-dir>}. */
        static AggregationTarget parse(String spec) {
            int equals = spec.indexOf('=');
            String[] files = equals < 0 ? new String[0]
                    : spec.substring(equals + 1).split(",", -1);
            if (equals <= 0 || files.length != 4) {
                throw new IllegalArgumentException("--target must be "
                        + "<name>=<candidate-graph>,<static-scope-map>,"
                        + "<region-skeletons>,<output-dir>: " + spec);
            }
            return new AggregationTarget(spec.substring(0, equals).trim(),
                    new File(files[0].trim()), new File(files[1].trim()),
                    new File(files[2].trim()), new File(files[3].trim()));
        }
    }

    /**
     * What a recording holds for one target: {@code ACTIVATED} (its plan is
     * written), or the refusal that stopped it -- {@code NOT_IN_WINDOW} (no
     * region of the throw ran in the window), {@code
     * TARGET_BRANCH_NOT_OBSERVED} (one ran, and never decided the throw's
     * branch), {@code POLICY_ABSENT} (its region declares no fatal branch),
     * {@code NO_REGION} (no candidate region ran), {@code
     * DECLARATION_UNRESOLVED} (the case's declaration names none of the
     * observed target occurrences, or does not read) or {@code ERROR} -- with
     * the target occurrences of the question's {@code (r,c)}, those of them
     * that took the throw's fatal arm (the TARGET_SITE guards' outcomes), and
     * the refusal's words.
     */
    static final class TargetOutcome {
        /** A finalizer refusal's code -> the state it is. */
        private static final Map<String, String> REFUSALS;
        static {
            Map<String, String> refusals = new LinkedHashMap<>();
            refusals.put("FATAL_TARGET_NOT_IN_WINDOW", "NOT_IN_WINDOW");
            refusals.put("FATAL_TARGET_OBSERVATION_GAP",
                    "TARGET_BRANCH_NOT_OBSERVED");
            refusals.put("FATAL_TARGET_POLICY_ABSENT", "POLICY_ABSENT");
            refusals.put("NO_REGION_ACTIVATION", "NO_REGION");
            refusals.put("DECLARED_TARGET_OCCURRENCE_UNOBSERVED",
                    "DECLARATION_UNRESOLVED");
            refusals.put("DECLARED_TARGET_OCCURRENCE_UNREADABLE",
                    "DECLARATION_UNRESOLVED");
            REFUSALS = Collections.unmodifiableMap(refusals);
        }

        final String name;
        final String state;
        final List<String> occurrences;
        final List<String> fatalOccurrences;
        final String detail;

        private TargetOutcome(String name, String state,
                              List<String> occurrences,
                              List<String> fatalOccurrences, String detail) {
            this.name = name;
            this.state = state;
            this.occurrences = occurrences;
            this.fatalOccurrences = fatalOccurrences;
            this.detail = detail;
        }

        static TargetOutcome activated(String name, List<String> occurrences,
                                       List<String> fatalOccurrences) {
            return new TargetOutcome(name, "ACTIVATED", occurrences,
                    fatalOccurrences, "");
        }

        /** A refusal: its state by the code its message starts with. */
        static TargetOutcome refused(String name, Throwable refusal) {
            String message = String.valueOf(refusal.getMessage());
            int colon = message.indexOf(':');
            String state = colon < 0 ? null
                    : REFUSALS.get(message.substring(0, colon));
            return new TargetOutcome(name, state == null ? "ERROR" : state,
                    Collections.<String>emptyList(),
                    Collections.<String>emptyList(),
                    state == null ? refusal.toString() : message);
        }

        boolean activated() {
            return "ACTIVATED".equals(state);
        }

        JsonObject json() {
            JsonObject json = new JsonObject();
            json.addProperty("state", state);
            json.add("occurrences", addresses(occurrences));
            json.add("fatalOccurrences", addresses(fatalOccurrences));
            json.addProperty("detail", detail);
            return json;
        }

        private static JsonArray addresses(List<String> occurrences) {
            JsonArray addresses = new JsonArray();
            for (String occurrence : occurrences) addresses.add(occurrence);
            return addresses;
        }
    }

    /**
     * Rich method-entry event used by graph-directed symbolic
     * instrumentation.
     *
     * @param openedRegionId the region this method is the ROOT of, or
     *                       {@code ""}; the row states an occurrence address
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
        // No frame push here: #enterMethodFrame already opened this level
        // (IDENTITY §3); a second push would shift every address below it.
        String address = "";
        boolean folded = false;
        if (!region.isEmpty()) {
            // No start claim here: #claimStart is the one claim point.
            String node = RuntimeTraceContext.activationSource(receiver).key();
            address = occurrenceAddress(node, region);
            // IDENTITY §1: an entry that opened no occurrence (a fold, or
            // unnamed work's) is no activation; the trace states it as
            // regionFolded.  Asked of the identity, not read off the empty
            // address: a node-less entry is a hole PLAN refuses, not a fold
            // it skips.
            folded = Identity.openedNone();
        }
        calls.push(new ActiveCall(id, parentSiteId, method,
                context.spanId, parent == null, !region.isEmpty(), address));
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
     * The address of the activation entering here, by {@code
     * Identity.occurrence} -- the same function a replay calls -- so both
     * passes take the same fold ({@code Identity#fold}, paper SS3.1.2).
     */
    private static String occurrenceAddress(String nodeKey, String regionId) {
        OccurrenceAddress address =
                Identity.occurrence(nodeKey, regionId, true);
        // IDENTITY §1: an entry that opened no occurrence states no address
        // (a fold's would be a second activation of one occurrence, unnamed
        // work's one its siblings share); the call above must still run to
        // push the marker.
        if (Identity.openedNone()) return "";
        return address == null ? "" : address.render();
    }

    /** The recording's half of {@link RowRuntime#claimStart}. */
    public static void claimStart(Object carrier) {
        RowRuntime.claimStart(carrier);
    }

    /** The recording's half of {@link RowRuntime#startWork}. */
    public static void startWork(String startSiteId, Object carrier) {
        RowRuntime.startWork(startSiteId, carrier);
    }

    /** {@code event} of one gap the RECORDING states. */
    static final String GAP_EVENT = "GAP";

    /**
     * A gap row's subject: {@code named}, else this thread's source key, else
     * the thread itself -- never a blank the row door would replace with the
     * session.
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
     * States one gap of the recording as a trace row; {@code RowRuntime.gap}
     * routes here while no session is open, and {@link #readStateTrace}
     * hands it to the plan's gap list.
     */
    static void recordingGap(
            GapKind kind,
            GapClass cls,
            String subject, String detail) {
        if (!RecordingWindow.opened()) return;
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 3,
                    "event", GAP_EVENT,
                    "seq", EVENT_COUNTER.incrementAndGet(),
                    "kind", kind.name(),
                    "cls", cls.name(),
                    "subject", lineageSubject(subject),
                    "detail", MapFields.safe(detail));
        }
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
        // No scope capture here: Identity.startWork owns it in both passes.
        ACTIVE_CALL_SITES.get().push(new ActiveCallSite(event.id, ownerCallId,
                event.siteId, event.method, event.declaredCallee));
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
        emitExecutionEvent(event);
    }

    /**
     * Enters the execution-index level of ONE application-scope method.
     *
     * <p>The one frame rule: every application-scope method opens a level at
     * entry and closes it at every exit, in both passes ({@code
     * CausynthPipeline.instrumentApplicationScope}, IDENTITY §3).  Counts
     * are keyed by (level, root hop, site), never by node ({@code
     * Identity.State#nextSiteEvent}).</p>
     *
     * @return the token that closes exactly the level this opened
     */
    public static long enterMethodFrame(String callSiteId, Object receiver) {
        return Identity.enterFrame(MapFields.safe(callSiteId), receiver);
    }

    /** Leaves the level {@link #enterMethodFrame} opened. */
    public static void exitMethodFrame(long token) {
        Identity.exitFrame(token);
    }

    /** The exceptional edge of {@link #enterMethodFrame}. */
    public static void throwMethodFrame(long token, Throwable thrown) {
        Identity.exitFrame(token);
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
        RecordingPlant.decided(event.siteId, event.outcome);
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
        RecordingPlant.decided(event.siteId, event.outcome);
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
        closeCall(call, resolvedCallId);
    }

    /** Ends one activation: its region and root context close with it. */
    private static void closeCall(ActiveCall call, long resolvedCallId) {
        removeCall(resolvedCallId);
        if (call != null && call.regionFrame) {
            Identity.regionExit();
        }
        if (call != null && call.rootContext) {
            RuntimeTraceContext.exitRoot(call.spanId);
        }
    }

    /**
     * Exceptional-exit hook that resolves the call id from the thread-local
     * stack; the handler cannot read the synthetic long local, which some
     * JVM/Soot stack maps do not keep live there.
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
        closeCall(call, resolvedCallId);
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
     * The request scope of the calling thread, to travel with the work it
     * creates (e.g. a Hadoop {@code Call} written by a pooled sender
     * thread).
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
            // Refusal is a named row; the send goes out without a header.
            RowRuntime.messageContextRefused("outbound "
                    + MapFields.safe(transport) + " "
                    + MapFields.safe(half), noFlow.getMessage());
            return "";
        }
        // IDENTITY §4: the message's producer endpoint is filed in-JVM by
        // correlation (the header does not carry it); one mint for
        // both passes.  A response was given its endpoint and its stance
        // where its request was received, whichever thread sends it.
        Receipt receipt = RESPONSE.equals(half) ? RECEIPTS.remove(
                receiptKey(transport, correlationId, attemptId)) : null;
        Endpoint producer = Identity.messageSent(
                RuntimeTraceContext.ownedSource(localOwner).key(),
                transport, correlationId, half,
                receipt == null ? null : receipt.response);
        // The schedule's SEND, naming the minted producer.
        ScheduleLog.observe(ScheduleEvent.Kind.SEND,
                MapFields.safe(transport) + "#" + MapFields.safe(half),
                producer == null ? "" : producer.id(),
                receipt == null ? null : receipt.stance);
        if (DEBUG_PRODUCERS && producer != null) {
            System.err.println("CAUSYNTH-PRODUCER " + transport + "#" + half
                    + " " + correlationId + " " + producer.id() + " "
                    + producer.render());
        }
        // The row states the endpoint's components, not only its digest.
        refuseSharedProducer(transport, correlationId, half, producer);
        recordExchange("SEND", transport, correlationId, attemptId, half,
                localOwner, carriedScope, producer);
        return header;
    }

    /**
     * Names the cause when two messages carry ONE producer endpoint (so their
     * consumers share one causal anchor), typically two unclaimed threads
     * under one degraded occurrence.  DIAGNOSTIC, like invariant 4: no stage
     * can repair an index that cannot separate two events.
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
        RowRuntime.gap(GapKind
                        .LINEAGE_LOST,
                GapClass.DIAGNOSTIC,
                producer.id(), detail);
    }

    /** Installs a received message context until {@link #endInboundExchange}. */
    public static long inboundExchange(String header, String transport,
                                       String correlationId,
                                       String attemptId, String half,
                                       Object localOwner) {
        return inboundExchange(header, transport, correlationId, attemptId,
                half, localOwner, true, "");
    }

    /**
     * @param awaited whether the schedule holds this receipt: a read of a
     *                shared store is not, since how many times a reader
     *                reads one version is the store's timing
     *                ({@link MessageDoors#fetched})
     * @param via     the receiving side's own name for where it arrived (a
     *                store notification's watcher), "" for none
     */
    public static long inboundExchange(String header, String transport,
                                       String correlationId,
                                       String attemptId, String half,
                                       Object localOwner, boolean awaited,
                                       String via) {
        initialize();
        long token;
        try {
            token = RuntimeTraceContext.enterInbound(header, transport,
                    correlationId, attemptId, half, localOwner, via);
        } catch (IllegalArgumentException refused) {
            // Same refusal as outbound; 0 means no scope installed.
            RowRuntime.messageContextRefused("inbound "
                    + MapFields.safe(transport) + " "
                    + MapFields.safe(half), refused.getMessage());
            return 0L;
        }
        // The schedule's RECV, under the scope the message opened; an
        // unawaited receipt's work is no part of the order.
        if (awaited) {
            ScheduleLog.observe(ScheduleEvent.Kind.RECV,
                    MapFields.safe(transport) + "#" + MapFields.safe(half));
        } else {
            ScheduleLog.unawaited(Text.safe(via).isEmpty() ? transport
                    : transport + "." + via);
        }
        if (awaited && REQUEST.equals(half)) {
            RECEIPTS.put(receiptKey(transport, correlationId, attemptId),
                    new Receipt(ScheduleLog.stanceHere(),
                            Identity.responseEndpoint(RuntimeTraceContext
                                    .ownedSource(localOwner).key(),
                                    transport, RESPONSE)));
        }
        // recordExchange's argument refusal stays an exception, not a row.
        try {
            // The receiving leg mints no producer.
            recordExchange("RECEIVE", transport, correlationId, attemptId,
                    half, localOwner, null, null);
            return token;
        } catch (RuntimeException | Error failure) {
            RuntimeTraceContext.exitInbound(token);
            throw failure;
        }
    }

    private static final String REQUEST = "REQUEST";
    private static final String RESPONSE = "RESPONSE";

    /**
     * A request's receipt: the endpoint and schedule stance of its response.
     * A response belongs to the call it answers, not to the thread that
     * happens to send it: a deferred RPC response is sent by whichever of
     * the handler and the thread it handed the call to finishes last (the
     * NameNode's edit-log sync thread), a race the recording and a replay
     * decide differently.  Minted where the request was received, it is the
     * same in both.
     */
    private static final class Receipt {
        private final ScheduleLog.Stance stance;
        private final Endpoint response;

        private Receipt(ScheduleLog.Stance stance, Endpoint response) {
            this.stance = stance;
            this.response = response;
        }
    }

    private static final Map<String, Receipt> RECEIPTS =
            new ConcurrentHashMap<String, Receipt>();

    private static String receiptKey(String transport, String correlationId,
                                     String attemptId) {
        return MapFields.safe(transport) + "|" + MapFields.safe(correlationId)
                + "|" + MapFields.safe(attemptId);
    }

    public static void endInboundExchange(long scopeToken) {
        RuntimeTraceContext.exitInbound(scopeToken);
    }

    /**
     * Records one transport-neutral message boundary, attributed to the
     * scope the work carries, stating the producer endpoint a SEND minted.
     */
    private static void recordExchange(String direction, String transport,
                                      String correlationId, String attemptId,
                                      String half, Object localOwner,
                                      Object carriedScope,
                                      Endpoint producer) {
        String normalizedDirection = MapFields.safe(direction).toUpperCase();
        String normalizedTransport = Text.safe(transport);
        String normalizedCorrelation = Text.safe(correlationId);
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
        String normalizedAttempt = Text.safe(attemptId);
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
     * Enters the scope a queued unit of work carried: the dequeue half of
     * {@link #captureScope()} (e.g. Hadoop IPC {@code Server.Call}, which no
     * inheritable context reaches).
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
     * Opens one daemon tick as a root of its own, named by role plus the
     * k-th tick in the recording window, so timer work is addressable.
     *
     * @param owner    an object whose registered source names the node, or
     *                 {@code null} to take the thread's own
     * @param roleName what the workload calls this timer's scope kind;
     *                 that name IS the role ({@code contract.Role})
     * @return the token to hand {@link #endDaemonTick(long)}
     */
    public static long beginDaemonTick(Object owner, String roleName) {
        initialize();
        return RuntimeTraceContext.beginTick(owner, roleName);
    }

    /** Whether the tick {@link #beginDaemonTick} opened is a vacant turn. */
    public static boolean vacantDaemonTick(long token) {
        return RuntimeTraceContext.vacantTick(token);
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

    /**
     * One call the workload itself makes -- a client operation of the test
     * thread, or of a thread it started -- as a request root of its own,
     * named by its api: {@code Root(CLIENT/api, k)} counts that api's calls
     * only.  A test that polls (a status request until an async task
     * completes, a query until a replica caught up) sends as many polls as
     * the run's timing gives it; under one request for the whole test every
     * later call's index moved with them, and so did every occurrence it
     * caused on the nodes.
     *
     * @return the request to end, or 0 when the thread runs no workload
     *         scope (a node's own thread, or before the window)
     */
    public static long beginWorkloadCall(String apiName) {
        initialize();
        SourceRef source = RuntimeTraceContext.explicitSource();
        if (source == null || !WORKLOAD_KIND.equals(source.kind())) return 0L;
        long requestId = RuntimeTraceContext.beginRequest(source, apiName,
                true);
        writeSourceTraceLine("REQUEST_BEGIN", source, null, requestId,
                MapFields.safe(apiName), 0);
        return requestId;
    }

    /** The kind a workload registers its own clients under. */
    public static final String WORKLOAD_KIND = "EXTERNAL_APP";

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
        // No index or context: only METHOD_ENTER and exchange rows are read
        // for them, and computing them per event dominated recording cost.
        return event;
    }

    /** Writes one execution row unless this JVM is a context-only replay. */
    private static void emitExecutionEvent(ExecutionEvent event) {
        if (contextOnlyConcolicReplay) return;
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
                site.siteId, site.declaredCallee);
    }

    /** The occurrences this thread's region entries opened, rendered,
     *  innermost first. */
    static List<String> enclosingOccurrences() {
        List<String> occurrences = new ArrayList<>();
        for (ActiveCall call : ACTIVE_CALLS.get()) {
            if (!call.occurrence.isEmpty()) occurrences.add(call.occurrence);
        }
        return occurrences;
    }

    /** One marker answer a plant gave ({@link RecordingPlant}), as a trace
     *  row. */
    static void plantApplied(String marker, String siteId, String occurrence,
                             boolean value) {
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 3,
                    "event", RecordingPlant.APPLIED,
                    "seq", EVENT_COUNTER.incrementAndGet(),
                    "marker", MapFields.safe(marker),
                    "siteId", siteId,
                    "occurrenceAddress", occurrence,
                    "value", value);
        }
    }

    /** One decision of the planted world's fatal arm at a target guard
     *  ({@link RecordingPlant#decided}), as a trace row: the occurrence it
     *  was decided in -- the anchor's when {@code atAnchor} -- or "". */
    static void plantFatal(String siteId, String occurrence,
                           boolean atAnchor) {
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 3,
                    "event", RecordingPlant.FATAL,
                    "seq", EVENT_COUNTER.incrementAndGet(),
                    "siteId", siteId,
                    "occurrenceAddress", occurrence,
                    "atAnchor", atAnchor);
        }
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
            // Which pass this JVM is is DECLARED by the campaign, never
            // inferred from which output keys happen to be set.
            boolean configuredContextOnly = RuntimeTraceMode.configured()
                    == RuntimeTraceMode.REPLAY_CONTEXT;
            File configuredOutputDir = configuredContextOnly ? null
                    : new File(firstNonBlank(
                    System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"),
                    "target/causynth-trace"));
            File configuredTraceFile = configuredOutputDir == null ? null
                    : new File(configuredOutputDir, "runtime_trace.jsonl");
            BufferedWriter configuredWriter = null;
            try {
                if (configuredContextOnly) {
                    // Keep the method/call-site TLS alive; publish nothing.
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
                // The recording's schedule, in the replay's shape.
                ScheduleLog.installFile(configuredOutputDir);
                INITIALIZED.set(true);
            } catch (IOException | RuntimeException failure) {
                closeQuietly(configuredWriter);
                // A later call may retry once the cause is repaired.
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
                    // Complete only once flushed and closed.
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
                                // INCOMPLETE means a crash or a failed
                                // write, nothing else.
                                "status", traceWriteFailure
                                        ? "INCOMPLETE" : "CLOSED"));
            }
        }
    }

    /** The trace, read once for every target it is aggregated for. */
    private static TraceData readStateTrace(File directory, String test)
            throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test);
            trace.schedule.addAll(SessionReader.readSchedule(new File(
                    directory, SessionDir.SCHEDULE).toPath()));
            trace.sort();
            // No offline reattribution: runtime.Attribution stamped every
            // METHOD_ENTER live, as the replay does.
            nameObservedObjectsFromContent(trace);
            return trace;
        }
    }

    /**
     * Each target aggregated over one trace on its own static slice and its
     * own skeletons ({@link #aggregateTarget}).  A target the finalizer
     * refuses is that target's outcome, never the others'.
     */
    static Map<String, TargetOutcome> aggregateTargets(
            TraceData trace, List<AggregationTarget> targets,
            String declaredOccurrence) {
        Map<String, TargetOutcome> outcomes = new LinkedHashMap<>();
        for (AggregationTarget target : targets) {
            try {
                outcomes.put(target.name, aggregateTarget(trace, target,
                        declaredOccurrence));
            } catch (IOException | RuntimeException refusal) {
                TargetOutcome outcome =
                        TargetOutcome.refused(target.name, refusal);
                // An unnamed failure is a defect: its stack says where.
                if ("ERROR".equals(outcome.state)) {
                    refusal.printStackTrace(System.err);
                }
                outcomes.put(target.name, outcome);
            }
        }
        return outcomes;
    }

    /**
     * One target's runtime region plan, written to its output directory: the
     * regions of its own skeletons the recording exercised, then its
     * activations, closure and plan over its own slice.  A recording woven
     * for several targets opens every target's regions; asked of this
     * target's skeletons alone, no other target's exception context is
     * taken for its own.
     */
    private static TargetOutcome aggregateTarget(
            TraceData trace, AggregationTarget target,
            String declaredOccurrence) throws IOException {
        // Regions exercised: root entered and an anchor reached, anchors
        // narrowed to those reached.  Asked of entries folded or not: a fold
        // is about occurrences, this is about the region having run.
        List<RuntimeRegionPlanner.MethodEvent> entries =
                new ArrayList<>(trace.methods.size());
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            entries.add(event.unfolded());
        }
        RuntimeRegionPlanner.Result exercised =
                RuntimeRegionPlanner.planSkeletonGraph(
                        StaticProgram.regionRows(
                                MapFields.readRows(target.skeletons),
                                RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                                target.skeletons),
                        entries, Collections.emptyList(),
                        Collections.emptyList(),
                        Collections.<String>emptySet());
        if (exercised.staticRegionCount == 0
                || exercised.runtimeInstances.isEmpty()) {
            throw new IOException("NO_REGION_ACTIVATION: the recording "
                    + "exercised no candidate region: "
                    + exercised.staticRegionCount + " region(s), "
                    + exercised.runtimeInstances.size() + " activation(s)");
        }
        Files.createDirectories(target.outputDir.toPath());
        File selectedSkeletons = new File(target.outputDir,
                "region_skeletons.jsonl");
        writeSelectedSkeletons(target.skeletons, selectedSkeletons,
                exercised.runtimeInstances);
        // Decoded once for planner and finalizer.
        List<StaticProgram.RegionRow> skeletons =
                StaticProgram.regionRows(
                        MapFields.readRows(selectedSkeletons),
                        RuntimeSelectedRegionFinalizer.SKELETON_KIND,
                        selectedSkeletons);
        // Parsed once: planner reads DECLARED_SITE, finalizer WRITE_SITE.
        StaticScopeMap scopeMap = readScopeMap(target.scopeMap);
        RuntimeRegionPlanner.Result activationGraph =
                RuntimeRegionPlanner.planSkeletonGraph(
                        skeletons, trace.methods,
                        trace.execution, trace.protocol,
                        declaredSites(scopeMap));
        Set<String> observedMethods = new LinkedHashSet<>();
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            observedMethods.add(event.method);
        }
        // The finalizer reads the candidate graph itself
        // (StaticProgram#skeletonRegionsHolding).  It marks the target
        // occurrences and binds their fatal-branch evidence on these
        // activations, which the plan below reads.
        RuntimeSelectedRegionFinalizer.Result closure =
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        MapFields.readRows(target.graph), skeletons,
                        String.valueOf(selectedSkeletons),
                        observedMethods, activationGraph.runtimeInstances,
                        runtimeObservations(trace.execution, trace.methods),
                        scopeMap, declaredOccurrence, trace.schedule);
        // Plan gaps = this pass's plus those the recording stated.
        List<Map<String, Object>> planGaps = new ArrayList<>(closure.gaps);
        planGaps.addAll(trace.lineageGaps);
        writeRuntimeRegionPlans(target.outputDir, closure.regions, trace,
                activationGraph.runtimeInstances, planGaps);
        List<String> occurrences = new ArrayList<>();
        List<String> fatal = new ArrayList<>();
        for (Map<String, Object> activation
                : activationGraph.runtimeInstances) {
            if (!Boolean.TRUE.equals(MapFields.booleanValue(activation.get(
                    RuntimeSelectedRegionFinalizer
                            .FAILURE_TARGET_OCCURRENCE)))) {
                continue;
            }
            String occurrence = String.valueOf(activation.get("occurrenceId"));
            occurrences.add(occurrence);
            for (Map<String, Object> evidence
                    : MapFields.rows(activation.get("observedFatalTargets"))) {
                if (tookFatalArm(scopeMap, evidence)) {
                    fatal.add(occurrence);
                    break;
                }
            }
        }
        return TargetOutcome.activated(target.name, occurrences, fatal);
    }

    /** Whether one observed decision of a TARGET_SITE guard took the arm
     *  that reaches the throw. */
    private static boolean tookFatalArm(StaticScopeMap scopeMap,
                                        Map<String, Object> evidence) {
        String site = String.valueOf(evidence.get("siteId"));
        for (StaticScopeMap.Site target : scopeMap.targetSites()) {
            Boolean arm = target.outcomeOf(site);
            if (arm != null && arm.equals(evidence.get("observedOutcome"))) {
                return true;
            }
        }
        return false;
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

    /**
     * The selected skeleton of an entered region is its candidate skeleton
     * with the observed anchor names; every other member is the candidate's.
     */
    private static void writeSelectedSkeletons(
            File candidates, File output,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        Map<String, String> anchorByRegion = new LinkedHashMap<>();
        Map<String, Set<String>> anchorsByRegion = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances) {
            String region = String.valueOf(instance.get("regionId"));
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
        // Streamed through: reading what we truncate must fail first.
        if (candidates.getCanonicalFile().equals(output.getCanonicalFile())) {
            throw new IOException("selected region skeletons must not "
                    + "overwrite the candidate skeletons: " + candidates);
        }
        // Staged and moved atomically: a mid-stream throw leaves the old
        // file intact.
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
                    if (selectedAnchor == null) {
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
                    row.addProperty("anchorMethod", selectedAnchor);
                    JsonArray selectedAnchors = new JsonArray();
                    for (String anchor : anchorsByRegion.get(region)) {
                        selectedAnchors.add(anchor);
                    }
                    row.add("anchorMethods", selectedAnchors);
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
     * Renames every observed object by the content of its first observation
     * ({@link RuntimeObjectIdentity}): the {@code identity()} counter is
     * per-run, so no published artifact may carry it.  Runs before any
     * planner reads the events.
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
     * The logical source of each recorded frame, walking the parent chain
     * for frames with none of their own.
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
     * Every object slot of every recorded event, merged on sequence so
     * "first observation" is load-order independent.
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
        // Slot breaks seq ties (a field access's receiver vs value).
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


    private static void clearInMemoryTrace() {
        INITIALIZED.set(false);
        EVENT_COUNTER.set(0L);
        ACTIVE_CALLS.remove();
        ACTIVE_CALL_SITES.remove();
        RuntimeTraceContext.resetForTests();
        OBJECT_IDS.clear();
        nextObjectId = 1;
        contextOnlyConcolicReplay = false;
        traceWriteFailure = false;
        traceWriter = null;
    }

    /** Number of worker threads used by offline trace aggregation parsing. */
    private static int aggregationThreads() {
        return Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
    }

    private static TraceData loadExistingTrace(
            File file, String test) throws IOException {
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
            // Parsed concurrently, merged in file order.
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
                            firstLineNumber, file, test, pool,
                            threads);
                    firstLineNumber = lineNumber + 1;
                    batch = new ArrayList<>(batchCapacity);
                }
            }
            if (!batch.isEmpty()) {
                submitBatch(executor, pending, trace, batch,
                        firstLineNumber, file, test, pool,
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
            File file, String test,
            ConcurrentHashMap<String, String> pool, int threads)
            throws IOException {
        pending.addLast(executor.submit(() -> parseTraceBatch(batch,
                firstLineNumber, file, test, pool)));
        // Bound in-flight batches; merging the head keeps file order.
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
            // Every list the parse fills, gaps included.
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
            ConcurrentHashMap<String, String> pool)
            throws IOException {
        TraceData trace = new TraceData();
        for (int index = 0; index < lines.size(); index++) {
            parseTraceLine(trace, lines.get(index),
                    firstLineNumber + index, file, test, pool);
        }
        return trace;
    }

    private static void parseTraceLine(
            TraceData trace, String line, int lineNumber, File file,
            String test,
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
                    sourceRef(row, "source"),
                    row.longValue("receiverAttributed", 0L) != 0L,
                    row.stringValue("requestKey"),
                    row.stringValue("requestApi"),
                    row.stringValue("occurrenceAddress"),
                    row.longValue("regionFolded", 0L) != 0L));
        } else if (("FIELD_READ".equals(eventKind)
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
                    sourceRef(row, "source"), row.stringValue("requestKey"),
                    row.stringValue("requestApi"),
                    row.stringValue("producerEndpointId"),
                    row.stringValue("producerEndpoint")));
        } else if (GAP_EVENT.equals(eventKind)) {
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
            SourceRef source = sourceRef(row, "source");
            // The related source is refused like the source, and not kept.
            sourceRef(row, "relatedSource");
            trace.sources.add(new SourceTraceEvent(row.longValue("seq", 0L),
                    eventKind, source, row.intValue("objectId", 0)));
        } else if (isExecutionEventKind(eventKind)) {
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
        // The trace states the window only: nothing before it opens.
        if (!RecordingWindow.opened()) return;
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
                // Flags are absent rather than false (per-call row size).
                "receiverAttributed", event.receiverAttributed ? 1 : null,
                "requestKey", event.requestKey,
                "requestApi", event.requestApi,
                // Identity v3 (Identity.occurrence); region-root entries
                // only.
                "occurrenceAddress", event.occurrenceAddress.isEmpty()
                        ? null : event.occurrenceAddress,
                // IDENTITY §1: folded entry, no activation.
                "regionFolded", event.regionFolded ? 1 : null);
    }

    private static void writeFieldTraceLine(
            RuntimeRegionPlanner.FieldAccessEvent event) {
        // The trace states the window only: nothing before it opens.
        if (!RecordingWindow.opened()) return;
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

    private static void writeProtocolTraceLine(
            RuntimeRegionPlanner.ProtocolEvent event) {
        // The trace states the window only: nothing before it opens.
        if (!RecordingWindow.opened()) return;
        writeTraceRow(
                "schemaVersion", 3,
                // SEND or RECEIVE: #recordExchange refuses any other.
                "event", "EXCHANGE_" + event.direction,
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
                // Sender's minted endpoint, digest and components; absent
                // on a delivery.
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
                    "objectId", objectId <= 0 ? null : objectId,
                    event.startsWith("REQUEST_") ? "apiName" : "aliasClass",
                    detail,
                    "laneId", context.laneId,
                    "spanId", context.spanId);
        }
    }

    private static void writeExecutionTraceLine(ExecutionEvent event) {
        // The trace states the window only: nothing before it opens.
        if (!RecordingWindow.opened()) return;
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

    private static String required(LongOptions options, String name) {
        String value = options.value(name, null);
        if (value == null) {
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

    /**
     * The scope map's declared-value sites, as {@code <siteId>\n<callee>}:
     * exactly the static pass's, never re-derived here.
     */
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
            // Best effort at shutdown; aggregation uses the throwing writer.
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
        /** The recording's schedule ({@code schedule.jsonl} beside the
         *  trace): where each message was sent and taken in. */
        final List<ScheduleEvent> schedule = new ArrayList<>();
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
        /** Registered object's identity, or 0; renamed after load. */
        private int objectId;

        private SourceTraceEvent(long seq, String kind, SourceRef source,
                                 int objectId) {
            this.seq = seq;
            this.kind = MapFields.safe(kind);
            this.source = source;
            this.objectId = objectId;
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
        /** The occurrence this entry opened, rendered; "" for none. */
        private final String occurrence;

        private ActiveCall(long callId, long parentSiteId, String method,
                           long spanId, boolean rootContext,
                           boolean regionFrame, String occurrence) {
            this.callId = callId;
            this.parentSiteId = parentSiteId;
            this.method = MapFields.safe(method);
            this.spanId = spanId;
            this.rootContext = rootContext;
            this.regionFrame = regionFrame;
            this.occurrence = occurrence;
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

        private ActiveCallSiteContext(String siteId, String declaredCallee) {
            this.siteId = MapFields.safe(siteId);
            this.declaredCallee = MapFields.safe(declaredCallee);
        }

        public String siteId() { return siteId; }

        public String declaredCallee() { return declaredCallee; }
    }

}
