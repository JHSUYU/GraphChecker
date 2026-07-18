package edu.uva.liftlab.graphchecker.runtime;

import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public final class CausynthTraceRecorder {
    private static final Object LOCK = new Object();
    private static final AtomicBoolean INITIALIZED = new AtomicBoolean();
    private static final AtomicLong EVENT_COUNTER = new AtomicLong();
    private static final Map<String, MethodContext> CONTEXTS = new LinkedHashMap<>();
    private static final Map<String, FieldEvent> FIELD_EVENTS_BY_CONTEXT_UNIT =
            new LinkedHashMap<>();
    private static final List<TraceEvent> EVENTS = new ArrayList<>();
    private static final List<FieldEvent> FIELD_EVENTS = new ArrayList<>();
    private static final List<ExecutionEvent> EXECUTION_EVENTS = new ArrayList<>();
    private static final ThreadLocal<Deque<ActiveCall>> ACTIVE_CALLS =
            new ThreadLocal<Deque<ActiveCall>>() {
                @Override
                protected Deque<ActiveCall> initialValue() {
                    return new ArrayDeque<>();
                }
            };
    private static final ThreadLocal<Deque<ActiveCallSite>> ACTIVE_CALL_SITES =
            new ThreadLocal<Deque<ActiveCallSite>>() {
                @Override
                protected Deque<ActiveCallSite> initialValue() {
                    return new ArrayDeque<>();
                }
            };
    private static final int DEFAULT_MAX_EVENTS = 200000;
    private static final int DEFAULT_MAX_GRAPH_EDGES = 50000;
    private static final int DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE = 2000;
    /**
     * A plain concolic replay uses the rich-trace call stacks only as exact
     * accessor-site context.  It does not publish a runtime trace, so hashing
     * every HDFS packet/argument is both semantically unused and prohibitively
     * expensive on the interpreted custom JVM.  Campaign discovery supplies
     * an explicit trace output directory and therefore keeps fingerprints.
     * The system property is an auditable override for either mode.
     */
    private static volatile boolean valueFingerprintsEnabled = true;
    private static volatile boolean contextOnlyConcolicReplay;

    private static volatile File outputDir;
    private static volatile File traceFile;
    private static volatile String testName;
    private static volatile int maxEvents;
    private static volatile int maxGraphEdges;
    private static volatile int maxContextPairsPerEdge;
    /**
     * Rich campaign replays may emit hundreds of thousands of events.  When
     * aggregation is performed by a fresh host JVM, retaining the same rows
     * in the MiniDFSCluster JVM only doubles memory and can make shutdown
     * aggregation fail.  Streaming-only mode keeps the call-stack TLS needed
     * by instrumentation, but writes event rows directly to disk without
     * building the offline graph inputs in this JVM.
     */
    private static volatile boolean retainRecordedEventsInMemory = true;
    /** Guarded by {@link #LOCK}; persisted in the streaming close manifest. */
    private static boolean traceWriteFailure;
    private static BufferedWriter traceWriter;
    /** Guarded by {@link #LOCK}; a reset must not install duplicate hooks. */
    private static boolean shutdownHookRegistered;

    private CausynthTraceRecorder() {
    }

    private static boolean configuredValueFingerprintsEnabled() {
        String explicit = firstNonBlank(System.getProperty(
                        "causynth.trace.value.fingerprints"),
                System.getenv("CAUSYNTH_TRACE_VALUE_FINGERPRINTS"));
        if (explicit != null && !explicit.trim().isEmpty()) {
            return Boolean.parseBoolean(explicit.trim());
        }
        String concolicResults = firstNonBlank(System.getProperty(
                        "causynth.concolic.results"),
                System.getenv("CAUSYNTH_CONCOLIC_RESULTS"));
        String traceOutput = firstNonBlank(System.getProperty(
                        "causynth.trace.output.dir"),
                System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"));
        return concolicResults == null || concolicResults.trim().isEmpty()
                || traceOutput != null && !traceOutput.trim().isEmpty();
    }

    private static boolean configuredContextOnlyConcolicReplay() {
        String concolicResults = firstNonBlank(System.getProperty(
                        "causynth.concolic.results"),
                System.getenv("CAUSYNTH_CONCOLIC_RESULTS"));
        String traceOutput = firstNonBlank(System.getProperty(
                        "causynth.trace.output.dir"),
                System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"));
        return concolicResults != null && !concolicResults.trim().isEmpty()
                && (traceOutput == null || traceOutput.trim().isEmpty());
    }

    public static void main(String[] args) {
        Map<String, String> params = parseArgs(args);
        File directory = new File(firstNonBlank(params.get("trace-dir"),
                params.get("output-dir"),
                System.getProperty("causynth.trace.output.dir"),
                System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"),
                "target/causynth-trace"));
        File graph = new File(firstNonBlank(params.get("static-graph"),
                System.getProperty("causynth.static.graph"),
                System.getenv("CAUSYNTH_STATIC_GRAPH"),
                new File(directory, "static_dataflow_edges.jsonl").getPath()));
        String regions = firstNonBlank(params.get("regions"),
                System.getProperty("causynth.symbolic.regions"),
                System.getenv("CAUSYNTH_SYMBOLIC_REGIONS"));
        String regionEdges = firstNonBlank(params.get("region-edges"),
                System.getProperty("causynth.symbolic.region.edges"),
                System.getenv("CAUSYNTH_SYMBOLIC_REGION_EDGES"));
        if (regions != null && !regions.isEmpty()) {
            System.setProperty("causynth.symbolic.regions", regions);
        }
        if (regionEdges != null && !regionEdges.isEmpty()) {
            System.setProperty("causynth.symbolic.region.edges", regionEdges);
        }
        String test = firstNonBlank(params.get("test"),
                System.getProperty("causynth.trace.test"),
                System.getenv("CAUSYNTH_TRACE_TEST"),
                "unknown-test");
        int graphEdges = parseInt(firstNonBlank(params.get("max-graph-edges"),
                System.getProperty("causynth.trace.max.graph.edges"),
                System.getenv("CAUSYNTH_TRACE_MAX_GRAPH_EDGES"),
                String.valueOf(DEFAULT_MAX_GRAPH_EDGES)), DEFAULT_MAX_GRAPH_EDGES);
        int contextPairs = parseInt(firstNonBlank(params.get("max-context-pairs-per-edge"),
                System.getProperty("causynth.trace.max.context.pairs.per.edge"),
                System.getenv("CAUSYNTH_TRACE_MAX_CONTEXT_PAIRS_PER_EDGE"),
                String.valueOf(DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE)),
                DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE);
        try {
            aggregateExistingTrace(directory, graph, test, graphEdges, contextPairs);
        } catch (Throwable throwable) {
            outputDir = directory;
            traceFile = new File(directory, "runtime_trace.jsonl");
            testName = test;
            maxEvents = DEFAULT_MAX_EVENTS;
            maxGraphEdges = graphEdges;
            maxContextPairsPerEdge = contextPairs;
            writeShutdownFailure(throwable);
            System.err.println("Failed to aggregate Causynth runtime trace: "
                    + throwable);
            throwable.printStackTrace(System.err);
            System.exit(1);
        }
    }

    public static void record(String method, Object receiver) {
        if (method == null) {
            return;
        }
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) {
            return;
        }
        if (contextOnlyConcolicReplay) {
            return;
        }
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        long tid = thread.getId();
        int objectId = receiver == null ? 0 : System.identityHashCode(receiver);
        String process = inferProcessName(method, threadName);
        long timeNanos = System.nanoTime();
        TraceEvent event = new TraceEvent(id, testName, process, threadName, tid,
                method, objectId, timeNanos);
        synchronized (LOCK) {
            if (retainRecordedEventsInMemory) {
                EVENTS.add(event);
                MethodContext context = CONTEXTS.get(event.contextKey());
                if (context == null) {
                    context = new MethodContext(event);
                    CONTEXTS.put(event.contextKey(), context);
                }
                context.observe(event);
            }
            writeTraceLine(event);
        }
    }

    /** Rich method-entry event used by graph-directed symbolic instrumentation. */
    public static long enterMethod(String method, Object receiver) {
        if (method == null) {
            return 0L;
        }
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) {
            return 0L;
        }
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        long tid = thread.getId();
        int objectId = identity(receiver);
        String process = inferProcessName(method, threadName);
        long timeNanos = System.nanoTime();
        Deque<ActiveCall> calls = ACTIVE_CALLS.get();
        ActiveCall parent = calls.peek();
        Deque<ActiveCallSite> sites = ACTIVE_CALL_SITES.get();
        ActiveCallSite parentSite = sites.peek();
        long parentCallId = parent == null ? 0L : parent.callId;
        long parentSiteId = parentSite == null ? 0L : parentSite.invocationId;
        TraceEvent event = new TraceEvent(id, testName, process, threadName, tid,
                method, objectId, timeNanos, id, parentCallId, parentSiteId,
                method + "#entry", runtimeType(receiver));
        calls.push(new ActiveCall(id, parentCallId, parentSiteId, method));
        if (contextOnlyConcolicReplay) {
            return id;
        }
        synchronized (LOCK) {
            if (retainRecordedEventsInMemory) {
                EVENTS.add(event);
                MethodContext context = CONTEXTS.get(event.contextKey());
                if (context == null) {
                    context = new MethodContext(event);
                    CONTEXTS.put(event.contextKey(), context);
                }
                context.observe(event);
            }
            writeTraceLine(event);
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
        event.declaredType = safe(declaredType);
        event.runtimeType = runtimeType(value);
        event.objectId = identity(value);
        event.primitiveValue = safe(primitiveValue);
        event.captureValueFingerprint(value, primitiveValue);
        emitExecutionEvent(event);
    }

    public static long beginCall(long ownerCallId, String caller, int unitIndex,
                                 String declaredCallee, Object receiver) {
        ActiveCall owner = activeCall(ownerCallId);
        closeStaleCallSite(ownerCallId);
        ExecutionEvent event = newExecutionEvent("CALL_SITE_ENTER",
                firstNonBlank(caller, owner == null ? "" : owner.method), ownerCallId);
        event.unitIndex = unitIndex;
        event.siteId = siteId(event.method, unitIndex);
        event.declaredCallee = safe(declaredCallee);
        event.runtimeType = runtimeType(receiver);
        event.objectId = identity(receiver);
        event.parentCallId = owner == null ? 0L : owner.parentCallId;
        event.invocationId = event.id;
        emitExecutionEvent(event);
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
        ExecutionEvent event = newExecutionEvent("CALL_ARGUMENT",
                site == null ? "" : site.caller,
                site == null ? 0L : site.ownerCallId);
        event.invocationId = invocationId;
        event.siteId = site == null ? "" : site.siteId;
        event.declaredCallee = site == null ? "" : site.declaredCallee;
        event.argumentIndex = argumentIndex;
        event.declaredType = safe(declaredType);
        event.runtimeType = runtimeType(value);
        event.objectId = identity(value);
        event.primitiveValue = safe(primitiveValue);
        event.captureValueFingerprint(value, primitiveValue);
        emitExecutionEvent(event);
    }

    public static void endCall(long invocationId, Object returnValue,
                               String primitiveValue) {
        ActiveCallSite site = activeCallSite(invocationId);
        ExecutionEvent event = newExecutionEvent("CALL_SITE_RETURN",
                site == null ? "" : site.caller,
                site == null ? 0L : site.ownerCallId);
        event.invocationId = invocationId;
        event.siteId = site == null ? "" : site.siteId;
        event.declaredCallee = site == null ? "" : site.declaredCallee;
        event.runtimeType = runtimeType(returnValue);
        event.objectId = identity(returnValue);
        event.primitiveValue = safe(primitiveValue);
        event.captureValueFingerprint(returnValue, primitiveValue);
        emitExecutionEvent(event);
        removeCallSite(invocationId);
    }

    public static void recordBranch(long callId, String method, int unitIndex,
                                    String expression, boolean outcome) {
        ExecutionEvent event = newExecutionEvent("BRANCH",
                firstNonBlank(method, methodForCall(callId)), callId);
        event.unitIndex = unitIndex;
        event.siteId = siteId(event.method, unitIndex);
        event.expression = safe(expression);
        event.outcome = outcome;
        event.hasOutcome = true;
        emitExecutionEvent(event);
    }

    public static void exitMethod(long callId, Object returnValue,
                                  String primitiveValue) {
        ActiveCall call = activeCall(callId);
        long resolvedCallId = call == null ? callId : call.callId;
        closeCallSites(resolvedCallId, "CALL_SITE_INCOMPLETE",
                "method exited without call return");
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_NORMAL",
                call == null ? "" : call.method, resolvedCallId);
        event.parentCallId = call == null ? 0L : call.parentCallId;
        event.parentSiteId = call == null ? 0L : call.parentSiteId;
        event.runtimeType = runtimeType(returnValue);
        event.objectId = identity(returnValue);
        event.primitiveValue = safe(primitiveValue);
        event.captureValueFingerprint(returnValue, primitiveValue);
        emitExecutionEvent(event);
        removeCall(resolvedCallId);
    }

    /** Normal exit resolved from the current thread-local call stack. */
    public static void exitActiveMethod(Object returnValue,
                                        String primitiveValue) {
        exitMethod(0L, returnValue, primitiveValue);
    }

    public static void throwMethod(long callId, Throwable throwable) {
        ActiveCall call = activeCall(callId);
        long resolvedCallId = call == null ? callId : call.callId;
        String exceptionType = throwable == null ? "" : throwable.getClass().getName();
        closeCallSites(resolvedCallId, "CALL_SITE_THROW", exceptionType);
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_THROW",
                call == null ? "" : call.method, resolvedCallId);
        event.parentCallId = call == null ? 0L : call.parentCallId;
        event.parentSiteId = call == null ? 0L : call.parentSiteId;
        event.exceptionType = exceptionType;
        event.runtimeType = exceptionType;
        event.objectId = identity(throwable);
        emitExecutionEvent(event);
        if (call != null && call.parentSiteId > 0L) {
            ActiveCallSite parentSite = activeCallSite(call.parentSiteId);
            if (parentSite != null) {
                closeCallSite(parentSite, "CALL_SITE_THROW", exceptionType);
            }
        }
        removeCall(resolvedCallId);
    }

    /**
     * Exceptional-exit hook that resolves the call id from the thread-local
     * call stack.  The injected catch-all handler deliberately does not read
     * the synthetic long local: some JVM/Soot stack-map combinations do not
     * keep that local live at an exceptional handler entry.
     */
    public static void throwActiveMethod(Throwable throwable) {
        throwMethod(0L, throwable);
    }

    public static void recordField(String kind, String method, int unitIndex,
                                   String field, Object methodReceiver,
                                   Object fieldReceiver, Object valueObject,
                                   String primitiveValue) {
        if (method == null || field == null) {
            return;
        }
        // Keep this before trace truncation: concolic soundness must not turn
        // a max-events diagnostic limit into a false no-write proof.
        ConcolicRegionRuntime.observeRuntimeFieldEvent(kind, fieldReceiver,
                field);
        initialize();
        if (contextOnlyConcolicReplay) {
            return;
        }
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) {
            return;
        }
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        long tid = thread.getId();
        int methodObjectId = methodReceiver == null ? 0 : System.identityHashCode(methodReceiver);
        int receiverObjectId = fieldReceiver == null ? 0 : System.identityHashCode(fieldReceiver);
        int valueObjectId = valueObject == null ? 0 : System.identityHashCode(valueObject);
        ValueFingerprint fingerprint = valueFingerprintsEnabled
                ? ValueFingerprint.capture(valueObject, primitiveValue)
                : ValueFingerprint.disabled();
        String process = inferProcessName(method, threadName);
        long timeNanos = System.nanoTime();
        ActiveCall activeCall = ACTIVE_CALLS.get().peek();
        FieldEvent event = new FieldEvent(id, testName, process, threadName, tid,
                method, methodObjectId, unitIndex, kind, field, receiverObjectId,
                valueObjectId, primitiveValue, timeNanos,
                activeCall == null ? 0L : activeCall.callId,
                siteId(method, unitIndex), fingerprint.digest,
                fingerprint.complete, fingerprint.nodes,
                fingerprint.reason);
        synchronized (LOCK) {
            if (retainRecordedEventsInMemory) {
                FIELD_EVENTS.add(event);
                String key = fieldEventKey(event.process, event.threadName,
                        event.tid, event.method, event.methodObjectId,
                        event.unitIndex, event.field);
                FIELD_EVENTS_BY_CONTEXT_UNIT.put(key, event);
            }
            writeFieldTraceLine(event);
        }
    }

    private static ExecutionEvent newExecutionEvent(String kind, String method,
                                                    long callId) {
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) {
            return new ExecutionEvent();
        }
        Thread thread = Thread.currentThread();
        ExecutionEvent event = new ExecutionEvent();
        event.id = id;
        event.kind = safe(kind);
        event.testName = testName;
        event.threadName = thread.getName();
        event.tid = thread.getId();
        event.method = safe(method);
        event.process = inferProcessName(event.method, event.threadName);
        event.callId = callId;
        event.timeNanos = System.nanoTime();
        return event;
    }

    private static void emitExecutionEvent(ExecutionEvent event) {
        if (event == null || event.id <= 0L) {
            return;
        }
        if (contextOnlyConcolicReplay) {
            return;
        }
        synchronized (LOCK) {
            if (retainRecordedEventsInMemory) {
                EXECUTION_EVENTS.add(event);
            }
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

    /**
     * Correlates a field hook inside an accessor body with the exact caller
     * callsite that selected that accessor.  The static dependency edge names
     * the invoke site, whereas the actual getfield hook executes in the
     * callee; comparing the two code positions directly would reject the
     * correct runtime event.
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
        String expectedSite = siteId(callerMethod, callerUnitIndex);
        return site != null
                && safe(callerMethod).equals(site.caller)
                && safe(callerSiteId).equals(expectedSite)
                && expectedSite.equals(site.siteId)
                && safe(declaredCallee).equals(site.declaredCallee);
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
            closeCallSite(top, "CALL_SITE_INCOMPLETE",
                    "next callsite reached before a normal return event");
        }
    }

    private static void closeCallSites(long ownerCallId, String kind,
                                       String detail) {
        List<ActiveCallSite> matches = new ArrayList<>();
        for (ActiveCallSite site : ACTIVE_CALL_SITES.get()) {
            if (site.ownerCallId == ownerCallId) {
                matches.add(site);
            }
        }
        for (ActiveCallSite site : matches) {
            closeCallSite(site, kind, detail);
        }
    }

    private static void closeCallSite(ActiveCallSite site, String kind,
                                      String detail) {
        if (site == null) {
            return;
        }
        ExecutionEvent event = newExecutionEvent(kind, site.caller,
                site.ownerCallId);
        event.invocationId = site.invocationId;
        event.siteId = site.siteId;
        event.declaredCallee = site.declaredCallee;
        event.exceptionType = safe(detail);
        emitExecutionEvent(event);
        ACTIVE_CALL_SITES.get().remove(site);
    }

    private static String methodForCall(long callId) {
        ActiveCall call = activeCall(callId);
        return call == null ? "" : call.method;
    }

    private static String siteId(String method, int unitIndex) {
        return safe(method) + "#u" + unitIndex;
    }

    private static int identity(Object value) {
        return value == null ? 0 : System.identityHashCode(value);
    }

    private static String runtimeType(Object value) {
        return value == null ? "" : value.getClass().getName();
    }

    private static String safe(String value) {
        return value == null ? "" : value;
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
            int configuredMaxEvents = parseInt(firstNonBlank(
                    System.getProperty("causynth.trace.max.events"),
                    System.getenv("CAUSYNTH_TRACE_MAX_EVENTS"),
                    String.valueOf(DEFAULT_MAX_EVENTS)), DEFAULT_MAX_EVENTS);
            int configuredMaxGraphEdges = parseInt(firstNonBlank(
                    System.getProperty("causynth.trace.max.graph.edges"),
                    System.getenv("CAUSYNTH_TRACE_MAX_GRAPH_EDGES"),
                    String.valueOf(DEFAULT_MAX_GRAPH_EDGES)),
                    DEFAULT_MAX_GRAPH_EDGES);
            int configuredMaxContextPairsPerEdge = parseInt(firstNonBlank(
                    System.getProperty("causynth.trace.max.context.pairs.per.edge"),
                    System.getenv("CAUSYNTH_TRACE_MAX_CONTEXT_PAIRS_PER_EDGE"),
                    String.valueOf(DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE)),
                    DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE);
            boolean configuredStreamingOnly = Boolean.parseBoolean(
                    firstNonBlank(System.getProperty(
                                    "causynth.trace.streaming.only"),
                            System.getenv(
                                    "CAUSYNTH_TRACE_STREAMING_ONLY"),
                            "false"));
            boolean configuredContextOnly =
                    configuredContextOnlyConcolicReplay();
            boolean configuredFingerprints =
                    configuredValueFingerprintsEnabled();
            File configuredOutputDir = configuredContextOnly ? null
                    : new File(firstNonBlank(
                    System.getProperty("causynth.trace.output.dir"),
                    System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"),
                    "target/causynth-trace"));
            File configuredTraceFile = configuredOutputDir == null ? null
                    : new File(configuredOutputDir, "runtime_trace.jsonl");
            BufferedWriter configuredWriter = null;
            try {
                if (configuredContextOnly) {
                    // Keep the exact method/call-site TLS alive for every
                    // accessor invocation.  Applying the ordinary trace event
                    // cap here would silently erase context before a late
                    // selected region executes.
                    testName = configuredTestName;
                    maxEvents = Integer.MAX_VALUE;
                    maxGraphEdges = configuredMaxGraphEdges;
                    maxContextPairsPerEdge =
                            configuredMaxContextPairsPerEdge;
                    retainRecordedEventsInMemory = false;
                    traceWriteFailure = false;
                    outputDir = null;
                    traceFile = null;
                    traceWriter = null;
                    contextOnlyConcolicReplay = true;
                    valueFingerprintsEnabled = configuredFingerprints;
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
                configuredWriter = new BufferedWriter(new FileWriter(
                        configuredTraceFile, false));
                ensureShutdownHookRegistered();

                // INITIALIZED is the release publication for every field above.
                // No recording thread can observe a partially initialized writer
                // or the JVM default value of an event limit.
                testName = configuredTestName;
                maxEvents = configuredMaxEvents;
                maxGraphEdges = configuredMaxGraphEdges;
                maxContextPairsPerEdge = configuredMaxContextPairsPerEdge;
                retainRecordedEventsInMemory = !configuredStreamingOnly;
                traceWriteFailure = false;
                outputDir = configuredOutputDir;
                traceFile = configuredTraceFile;
                traceWriter = configuredWriter;
                contextOnlyConcolicReplay = false;
                valueFingerprintsEnabled = configuredFingerprints;
                INITIALIZED.set(true);
            } catch (IOException | RuntimeException failure) {
                closeQuietly(configuredWriter);
                // A later recording call may retry after configuration or the
                // filesystem has been repaired.  Never publish a disabled
                // recorder as successfully initialized.
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
                    // has closed successfully.  Preserve that failure in the
                    // close manifest so the campaign never feeds a partial
                    // execution to the offline aggregator.
                    traceWriteFailure = true;
                }
                traceWriter = null;
            }
            if (!retainRecordedEventsInMemory && outputDir != null) {
                long attempted = EVENT_COUNTER.get();
                boolean truncated = attempted > maxEvents;
                writeFile(new File(outputDir,
                                "streaming_trace_manifest.json"),
                        jsonObject(
                                "schemaVersion", 1,
                                "kind", "STREAMING_RUNTIME_TRACE",
                                "status", "CLOSED",
                                "traceFile", traceFile == null ? ""
                                        : traceFile.getPath(),
                                "attemptedEventCount", attempted,
                                "maxEvents", maxEvents,
                                "truncated", truncated,
                                "writeFailure", traceWriteFailure,
                                "complete", !truncated
                                        && !traceWriteFailure));
            }
            try {
                if (aggregateOnShutdown()) {
                    if (!retainRecordedEventsInMemory) {
                        throw new IllegalStateException(
                                "streaming-only trace requires offline "
                                        + "aggregation in a fresh JVM");
                    }
                    writeInstantiatedGraph();
                }
            } catch (Throwable throwable) {
                writeShutdownFailure(throwable);
            }
        }
    }

    private static boolean aggregateOnShutdown() {
        return Boolean.parseBoolean(firstNonBlank(
                System.getProperty("causynth.trace.aggregate.on.shutdown"),
                System.getenv("CAUSYNTH_TRACE_AGGREGATE_ON_SHUTDOWN"),
                "false"));
    }

    private static void aggregateExistingTrace(File directory, File staticGraph,
                                               String test, int graphEdges,
                                               int contextPairs) throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            outputDir = directory;
            traceFile = new File(directory, "runtime_trace.jsonl");
            testName = test;
            maxEvents = Integer.MAX_VALUE;
            maxGraphEdges = graphEdges;
            maxContextPairsPerEdge = contextPairs;
            // This JVM is the offline aggregator.  Rows loaded below must be
            // retained regardless of the recording-mode property inherited
            // from a caller.
            retainRecordedEventsInMemory = true;
            traceWriter = null;
            System.setProperty("causynth.static.graph", staticGraph.getPath());
            loadExistingTrace(traceFile);
            writeInstantiatedGraph();
        }
    }

    private static void clearInMemoryTrace() {
        INITIALIZED.set(false);
        EVENT_COUNTER.set(0L);
        CONTEXTS.clear();
        FIELD_EVENTS_BY_CONTEXT_UNIT.clear();
        EVENTS.clear();
        FIELD_EVENTS.clear();
        EXECUTION_EVENTS.clear();
        ACTIVE_CALLS.remove();
        ACTIVE_CALL_SITES.remove();
        retainRecordedEventsInMemory = true;
        contextOnlyConcolicReplay = false;
        valueFingerprintsEnabled = true;
        traceWriteFailure = false;
        traceWriter = null;
    }

    private static void loadExistingTrace(File file) throws IOException {
        if (file == null || !file.isFile()) {
            throw new IOException("Runtime trace not found: " + file);
        }
        try (BufferedReader reader = Files.newBufferedReader(file.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String eventKind = jsonField(line, "event");
                if ("METHOD_ENTER".equals(eventKind)) {
                    String method = jsonField(line, "method");
                    String threadName = jsonField(line, "threadName");
                    addTraceEvent(new TraceEvent(
                            jsonLongField(line, "seq", 0L),
                            firstNonBlank(jsonField(line, "test"), testName),
                            normalizeRecordedProcess(jsonField(line, "process"),
                                    method, threadName),
                            threadName,
                            jsonLongField(line, "tid", 0L),
                            method,
                            jsonIntField(line, "objectId", 0),
                            jsonLongField(line, "timeNanos", 0L),
                            jsonLongField(line, "callId",
                                    jsonLongField(line, "seq", 0L)),
                            jsonLongField(line, "parentCallId", 0L),
                            jsonLongField(line, "parentSiteId", 0L),
                            jsonField(line, "siteId"),
                            jsonField(line, "receiverType")));
                } else if ("FIELD_READ".equals(eventKind)
                        || "FIELD_WRITE".equals(eventKind)) {
                    String method = jsonField(line, "method");
                    String threadName = jsonField(line, "threadName");
                    addFieldEvent(new FieldEvent(
                            jsonLongField(line, "seq", 0L),
                            firstNonBlank(jsonField(line, "test"), testName),
                            normalizeRecordedProcess(jsonField(line, "process"),
                                    method, threadName),
                            threadName,
                            jsonLongField(line, "tid", 0L),
                            method,
                            jsonIntField(line, "objectId", 0),
                            jsonIntField(line, "unitIndex", -1),
                            eventKind,
                            jsonField(line, "field"),
                            jsonIntField(line, "fieldReceiverObjectId", 0),
                            jsonIntField(line, "valueObjectId", 0),
                            jsonField(line, "primitiveValue"),
                            jsonLongField(line, "timeNanos", 0L),
                            jsonLongField(line, "callId", 0L),
                            jsonField(line, "siteId"),
                            jsonField(line, "valueFingerprint"),
                            jsonBooleanField(line,
                                    "valueFingerprintComplete", false),
                            jsonIntField(line, "valueFingerprintNodes", 0),
                            jsonField(line, "valueFingerprintReason")));
                } else if (isExecutionEventKind(eventKind)) {
                    addExecutionEvent(ExecutionEvent.fromJson(line, eventKind));
                }
            }
        }
        normalizeRecordedEventOrderAndRebuildIndexes();
    }

    /**
     * A recorder sequence is allocated before a thread acquires the streaming
     * writer lock.  Consequently a valid multi-threaded trace can contain
     * rows in a different file order from their sequence order.  Every
     * offline consumer uses the recorder sequence as its observation-order
     * authority, so rebuild all order-sensitive indexes after loading instead
     * of accidentally treating writer-lock acquisition order as execution
     * order.
     */
    private static void normalizeRecordedEventOrderAndRebuildIndexes() {
        EVENTS.sort((left, right) -> Long.compare(left.id, right.id));
        FIELD_EVENTS.sort((left, right) -> Long.compare(left.id, right.id));
        EXECUTION_EVENTS.sort((left, right) -> Long.compare(left.id, right.id));

        CONTEXTS.clear();
        for (TraceEvent event : EVENTS) {
            MethodContext context = CONTEXTS.get(event.contextKey());
            if (context == null) {
                context = new MethodContext(event);
                CONTEXTS.put(event.contextKey(), context);
            }
            context.observe(event);
        }

        FIELD_EVENTS_BY_CONTEXT_UNIT.clear();
        for (FieldEvent event : FIELD_EVENTS) {
            String key = fieldEventKey(event.process, event.threadName,
                    event.tid, event.method, event.methodObjectId,
                    event.unitIndex, event.field);
            // FIELD_EVENTS is sequence ordered, therefore the retained value
            // is the latest observation for this exact runtime field site.
            FIELD_EVENTS_BY_CONTEXT_UNIT.put(key, event);
        }
    }

    private static void addTraceEvent(TraceEvent event) {
        if (event == null || event.method == null || event.method.isEmpty()) {
            return;
        }
        EVENTS.add(event);
        MethodContext context = CONTEXTS.get(event.contextKey());
        if (context == null) {
            context = new MethodContext(event);
            CONTEXTS.put(event.contextKey(), context);
        }
        context.observe(event);
        EVENT_COUNTER.set(Math.max(EVENT_COUNTER.get(), event.id));
    }

    private static void addFieldEvent(FieldEvent event) {
        if (event == null || event.method == null || event.method.isEmpty()
                || event.field == null || event.field.isEmpty()) {
            return;
        }
        FIELD_EVENTS.add(event);
        String key = fieldEventKey(event.process, event.threadName, event.tid,
                event.method, event.methodObjectId, event.unitIndex, event.field);
        FIELD_EVENTS_BY_CONTEXT_UNIT.put(key, event);
        EVENT_COUNTER.set(Math.max(EVENT_COUNTER.get(), event.id));
    }

    private static void addExecutionEvent(ExecutionEvent event) {
        if (event == null || event.id <= 0L || event.kind == null
                || event.kind.isEmpty()) {
            return;
        }
        EXECUTION_EVENTS.add(event);
        EVENT_COUNTER.set(Math.max(EVENT_COUNTER.get(), event.id));
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

    private static void writeTraceLine(TraceEvent event) {
        if (traceWriter == null) {
            return;
        }
        try {
            traceWriter.write(jsonObject(
                    "event", "METHOD_ENTER",
                    "seq", event.id,
                    "test", event.testName,
                    "process", event.process,
                    "threadName", event.threadName,
                    "tid", event.tid,
                    "method", event.method,
                    "objectId", event.objectId,
                    "receiverType", event.receiverType,
                    "callId", event.callId,
                    "parentCallId", event.parentCallId,
                    "parentSiteId", event.parentSiteId,
                    "siteId", event.siteId,
                    "timeNanos", event.timeNanos));
            traceWriter.newLine();
        } catch (IOException ignored) {
            traceWriteFailure = true;
        }
    }

    private static void writeFieldTraceLine(FieldEvent event) {
        if (traceWriter == null) {
            return;
        }
        try {
            traceWriter.write(jsonObject(
                    "event", event.kind,
                    "seq", event.id,
                    "test", event.testName,
                    "process", event.process,
                    "threadName", event.threadName,
                    "tid", event.tid,
                    "method", event.method,
                    "objectId", event.methodObjectId,
                    "callId", event.callId,
                    "siteId", event.siteId,
                    "unitIndex", event.unitIndex,
                    "field", event.field,
                    "fieldReceiverObjectId", event.receiverObjectId,
                    "valueObjectId", event.valueObjectId,
                    "primitiveValue", event.primitiveValue,
                    "valueFingerprint", event.valueFingerprint,
                    "valueFingerprintComplete", event.valueFingerprintComplete,
                    "valueFingerprintNodes", event.valueFingerprintNodes,
                    "valueFingerprintReason", event.valueFingerprintReason,
                    "timeNanos", event.timeNanos));
            traceWriter.newLine();
        } catch (IOException ignored) {
            traceWriteFailure = true;
        }
    }

    private static void writeExecutionTraceLine(ExecutionEvent event) {
        if (traceWriter == null || event == null) {
            return;
        }
        try {
            traceWriter.write(jsonObject(
                    "event", event.kind,
                    "seq", event.id,
                    "test", event.testName,
                    "process", event.process,
                    "threadName", event.threadName,
                    "tid", event.tid,
                    "method", event.method,
                    "callId", event.callId,
                    "parentCallId", event.parentCallId,
                    "parentSiteId", event.parentSiteId,
                    "invocationId", event.invocationId,
                    "siteId", event.siteId,
                    "unitIndex", event.unitIndex,
                    "declaredCallee", event.declaredCallee,
                    "argumentIndex", event.argumentIndex,
                    "declaredType", event.declaredType,
                    "runtimeType", event.runtimeType,
                    "objectId", event.objectId,
                    "primitiveValue", event.primitiveValue,
                    "valueFingerprint", event.valueFingerprint,
                    "valueFingerprintComplete", event.valueFingerprintComplete,
                    "valueFingerprintNodes", event.valueFingerprintNodes,
                    "valueFingerprintReason", event.valueFingerprintReason,
                    "expression", event.expression,
                    "hasOutcome", event.hasOutcome,
                    "outcome", event.hasOutcome ? event.outcome : null,
                    "exceptionType", event.exceptionType,
                    "timeNanos", event.timeNanos));
            traceWriter.newLine();
        } catch (IOException ignored) {
            traceWriteFailure = true;
        }
    }

    private static void writeInstantiatedGraph() {
        // In-memory aggregation has the same cross-thread row-order property
        // as an offline-loaded stream.  Normalize centrally before any graph,
        // latest-write, or region-planning consumer observes the collections.
        normalizeRecordedEventOrderAndRebuildIndexes();
        File staticGraph = new File(firstNonBlank(System.getProperty("causynth.static.graph"),
                System.getenv("CAUSYNTH_STATIC_GRAPH"),
                new File(outputDir, "static_dataflow_edges.jsonl").getPath()));
        List<StaticEdge> staticEdges = readStaticEdges(staticGraph);
        Map<String, List<MethodContext>> contextsByMethod = new LinkedHashMap<>();
        for (MethodContext context : CONTEXTS.values()) {
            List<MethodContext> contexts = contextsByMethod.get(context.method);
            if (contexts == null) {
                contexts = new ArrayList<>();
                contextsByMethod.put(context.method, contexts);
            }
            contexts.add(context);
        }

        List<String> nodeJson = new ArrayList<>();
        Set<String> emittedNodes = new LinkedHashSet<>();
        Map<String, EdgeAccumulator> emittedEdges = new LinkedHashMap<>();
        List<String> roleNodeJson = new ArrayList<>();
        Set<String> emittedRoleNodes = new LinkedHashSet<>();
        Map<String, EdgeAccumulator> emittedRoleEdges = new LinkedHashMap<>();
        int mergedEdgeInputCount = 0;
        int mergedRoleEdgeInputCount = 0;
        int skippedGraphEdgeInstances = 0;
        int skippedRoleGraphEdgeInstances = 0;
        long skippedContextPairInstances = 0L;
        boolean truncated = false;
        boolean roleTruncated = false;
        boolean contextPairTruncated = false;
        for (StaticEdge edge : staticEdges) {
            ContextPairSelection contextSelection = contextsForGraphEdge(edge,
                    contextsByMethod);
            if (contextSelection.truncated) {
                contextPairTruncated = true;
                truncated = true;
                roleTruncated = true;
                skippedContextPairInstances += contextSelection.skipped;
            }
            for (InstantiatedContextPair context : contextSelection.pairs) {
                String fromCell = instantiateCell(context.fromContext, edge, edge.fromCell);
                String toCell = instantiateCell(context.toContext, edge, edge.toCell);
                String fromId = nodeId(context.fromContext, fromCell);
                String toId = nodeId(context.toContext, toCell);
                if (emittedNodes.add(fromId)) {
                    nodeJson.add(nodeJson(context.fromContext, fromId, fromCell));
                }
                if (emittedNodes.add(toId)) {
                    nodeJson.add(nodeJson(context.toContext, toId, toCell));
                }
                String edgeKey = edgeKey(edge, fromId, toId);
                EdgeAccumulator accumulator = emittedEdges.get(edgeKey);
                if (accumulator == null) {
                    if (emittedEdges.size() >= maxGraphEdges) {
                        truncated = true;
                        skippedGraphEdgeInstances++;
                    } else {
                        accumulator = new EdgeAccumulator(edge, fromId, toId,
                                context.fromContext, context.toContext);
                        emittedEdges.put(edgeKey, accumulator);
                    }
                } else {
                    accumulator.observe(edge, context.fromContext, context.toContext);
                    mergedEdgeInputCount++;
                }

                String roleFromCell = roleCell(fromCell);
                String roleToCell = roleCell(toCell);
                String roleFromId = roleNodeId(context.fromContext, roleFromCell);
                String roleToId = roleNodeId(context.toContext, roleToCell);
                if (emittedRoleNodes.add(roleFromId)) {
                    roleNodeJson.add(roleNodeJson(context.fromContext, roleFromId,
                            roleFromCell));
                }
                if (emittedRoleNodes.add(roleToId)) {
                    roleNodeJson.add(roleNodeJson(context.toContext, roleToId,
                            roleToCell));
                }
                String roleEdgeKey = roleEdgeKey(edge, roleFromId, roleToId);
                EdgeAccumulator roleAccumulator = emittedRoleEdges.get(roleEdgeKey);
                if (roleAccumulator == null) {
                    if (emittedRoleEdges.size() >= maxGraphEdges) {
                        roleTruncated = true;
                        skippedRoleGraphEdgeInstances++;
                        continue;
                    }
                    roleAccumulator = new EdgeAccumulator(edge, roleFromId, roleToId,
                            context.fromContext, context.toContext);
                    emittedRoleEdges.put(roleEdgeKey, roleAccumulator);
                } else {
                    roleAccumulator.observe(edge, context.fromContext, context.toContext);
                    mergedRoleEdgeInputCount++;
                }
            }
        }
        RuntimeFieldBridgeStats runtimeFieldBridgeStats = addRuntimeFieldBridges(
                emittedNodes, nodeJson, emittedEdges,
                emittedRoleNodes, roleNodeJson, emittedRoleEdges);
        truncated = truncated || runtimeFieldBridgeStats.truncated;
        roleTruncated = roleTruncated || runtimeFieldBridgeStats.roleTruncated;

        String summary = jsonObject(
                "test", testName,
                "traceFile", traceFile == null ? "" : traceFile.getPath(),
                "staticGraph", staticGraph.getPath(),
                "traceEventCount", EVENTS.size(),
                "fieldEventCount", FIELD_EVENTS.size(),
                "executionEventCount", EXECUTION_EVENTS.size(),
                "observedMethodContextCount", CONTEXTS.size(),
                "observedMethodCount", contextsByMethod.size(),
                "staticEdgeCount", staticEdges.size(),
                "instantiatedNodeCount", nodeJson.size(),
                "instantiatedEdgeCount", emittedEdges.size(),
                "mergedEdgeInputCount", mergedEdgeInputCount,
                "roleMergedNodeCount", roleNodeJson.size(),
                "roleMergedEdgeCount", emittedRoleEdges.size(),
                "mergedRoleEdgeInputCount", mergedRoleEdgeInputCount,
                "runtimeFieldBridgeInputCount", runtimeFieldBridgeStats.inputCount,
                "runtimeFieldBridgeMergedInputCount", runtimeFieldBridgeStats.mergedInputCount,
                "runtimeRoleFieldBridgeMergedInputCount", runtimeFieldBridgeStats.roleMergedInputCount,
                "skippedGraphEdgeInstances", skippedGraphEdgeInstances,
                "skippedRoleGraphEdgeInstances", skippedRoleGraphEdgeInstances,
                "skippedRuntimeFieldBridgeInstances", runtimeFieldBridgeStats.skippedGraphEdgeInstances,
                "skippedRuntimeRoleFieldBridgeInstances", runtimeFieldBridgeStats.skippedRoleGraphEdgeInstances,
                "skippedContextPairInstances", skippedContextPairInstances,
                "contextPairTruncated", contextPairTruncated,
                "truncated", truncated,
                "roleTruncated", roleTruncated,
                "maxEvents", maxEvents,
                "maxGraphEdges", maxGraphEdges,
                "maxContextPairsPerEdge", maxContextPairsPerEdge);
        // HDFS traces can legitimately instantiate graphs beyond Java's
        // maximum String/byte[] size.  Stream the already bounded collections
        // instead of constructing one multi-gigabyte intermediate String.
        writeGraphFile(new File(outputDir, "unit_test_instantiated_graph.json"),
                summary, nodeJson, emittedEdges, false);
        writeGraphFile(new File(outputDir, "unit_test_role_merged_graph.json"),
                summary, roleNodeJson, emittedRoleEdges, true);
        writeFile(new File(outputDir, "summary.json"), summary);
        writeSymbolicGuidanceDag(emittedEdges, emittedRoleEdges,
                contextsByMethod, truncated, roleTruncated);
        writeSeedChainSummary(staticEdges);
        writeRuntimeValidationSummary(staticEdges, contextsByMethod);
        writeRuntimeRefinedSymbolicPlan(staticGraph);
        writeRuntimeRegionPlans(staticGraph);
    }

    private static void writeSymbolicGuidanceDag(
            Map<String, EdgeAccumulator> objectEdges,
            Map<String, EdgeAccumulator> roleEdges,
            Map<String, List<MethodContext>> contextsByMethod,
            boolean objectGraphTruncated,
            boolean roleGraphTruncated) {
        List<String> guidanceEdges = new ArrayList<>();
        Map<String, Integer> modelCounts = new LinkedHashMap<>();
        int emitted = 0;
        int index = 0;
        for (EdgeAccumulator edge : roleEdges.values()) {
            String model = guidanceModel(edge);
            increment(modelCounts, model);
            if (!shouldEmitGuidanceEdge(edge)) {
                continue;
            }
            if (emitted++ >= 1500) {
                continue;
            }
            guidanceEdges.add(guidanceEdgeJson("GUIDE." + index++, edge, model));
        }

        List<String> modelRequirements = new ArrayList<>();
        for (Map.Entry<String, Integer> entry : modelCounts.entrySet()) {
            modelRequirements.add(modelRequirementJson(entry.getKey(),
                    entry.getValue()));
        }

        // The generic trace layer deliberately does not synthesize
        // project-specific relationships.  Concrete edge evidence and merge
        // points remain available; symbolic expressions come only from
        // imported region summaries later in the concolic campaign.
        List<String> evidence = new ArrayList<>();
        List<String> symbolicExpressions = new ArrayList<>();
        List<String> mergePoints = symbolicMergePoints(roleEdges);
        List<String> limitations = symbolicGuidanceLimitations();

        String summary = jsonObject(
                "test", testName,
                "purpose", "symbolic_execution_guidance",
                "objectEdgeCount", objectEdges.size(),
                "roleEdgeCount", roleEdges.size(),
                "observedMethodCount", contextsByMethod.size(),
                "objectGraphTruncated", objectGraphTruncated,
                "roleGraphTruncated", roleGraphTruncated,
                "guidanceEdgeCount", guidanceEdges.size(),
                "symbolicExpressionCount", symbolicExpressions.size(),
                "mergePointCount", mergePoints.size(),
                "precision", "over_approx_static_graph_plus_runtime_context");
        String dag = "{"
                + "\"summary\":" + summary
                + ",\"symbolicExpressions\":[" + join(symbolicExpressions) + "]"
                + ",\"evidence\":[" + join(evidence) + "]"
                + ",\"modelRequirements\":[" + join(modelRequirements) + "]"
                + ",\"mergePoints\":[" + join(mergePoints) + "]"
                + ",\"guidanceEdges\":[" + join(guidanceEdges) + "]"
                + ",\"limitations\":[" + join(limitations) + "]"
                + "}";
        writeFile(new File(outputDir, "symbolic_guidance_dag.json"), dag);
    }

    private static void increment(Map<String, Integer> counts, String key) {
        Integer value = counts.get(key);
        counts.put(key, value == null ? 1 : value + 1);
    }

    private static boolean shouldEmitGuidanceEdge(EdgeAccumulator edge) {
        return edge != null;
    }

    private static String guidanceModel(EdgeAccumulator edge) {
        String kind = lower(edge == null ? "" : edge.kind);
        String text = edgeText(edge);
        if (kind.contains("rpc") || kind.contains("protocol")
                || kind.contains("transfer")) {
            return "port_mapping_candidate";
        }
        if (kind.contains("runtime_field_state")) {
            return "heap_latest_write";
        }
        if (text.contains("<java.util.map:")) {
            return "symbolic_map_state";
        }
        if (kind.contains("field_write") || kind.contains("field_mutation")) {
            return "heap_write";
        }
        if (kind.contains("field_read")) {
            return "heap_read";
        }
        if (kind.contains("constructor")) {
            return "constructor_summary";
        }
        if (kind.contains("call_return") || kind.contains("caller_return")) {
            return "method_return_summary";
        }
        if (kind.contains("argument")) {
            return "argument_binding";
        }
        if (kind.contains("seed")) {
            return "target_seed";
        }
        if (kind.contains("guard")) {
            return "path_condition";
        }
        if (kind.contains("throw")) {
            return "exception_condition";
        }
        return "local_dataflow";
    }

    private static String guidanceEdgeJson(String id, EdgeAccumulator edge,
                                           String model) {
        return jsonObject(
                "id", id,
                "kind", edge.kind,
                "model", model,
                "summary", guidanceSummary(model),
                "expressionHint", guidanceExpressionHint(model),
                "precision", guidancePrecision(model),
                "from", edge.from,
                "to", edge.to,
                "fromProcess", edge.firstFromContext.process,
                "fromThreadRole", threadRole(edge.firstFromContext.threadName),
                "toProcess", edge.firstToContext.process,
                "toThreadRole", threadRole(edge.firstToContext.threadName),
                "method", edge.method,
                "occurrences", edge.occurrences,
                "mergedInstances", edge.mergedInstances,
                "fromContextCount", edge.fromContexts.size(),
                "toContextCount", edge.toContexts.size(),
                "firstSeq", edge.firstSeq == Long.MAX_VALUE ? 0 : edge.firstSeq,
                "lastSeq", edge.lastSeq == Long.MIN_VALUE ? 0 : edge.lastSeq,
                "staticEdgeIds", join(edge.staticEdgeIds, ";"));
    }

    private static String guidanceSummary(String model) {
        if ("port_mapping_candidate".equals(model)) {
            return "Use only to locate endpoint ports; it is not a symbolic equality until runtime value evidence or region summaries prove one.";
        }
        if ("heap_latest_write".equals(model)) {
            return "Model read as latest observed write to the same process, receiver object, and field.";
        }
        if ("symbolic_map_state".equals(model)) {
            return "Model as symbolic map state; precise entry lookup requires Map put/get/remove summaries.";
        }
        if ("heap_write".equals(model)) {
            return "Model as heap field update.";
        }
        if ("heap_read".equals(model)) {
            return "Model as heap field read.";
        }
        if ("constructor_summary".equals(model)) {
            return "Model constructor as object creation with argument-to-field summaries.";
        }
        if ("method_return_summary".equals(model)) {
            return "Obtain the return expression from a captured region summary; otherwise leave it uninterpreted.";
        }
        if ("argument_binding".equals(model)) {
            return "Bind caller actual to callee formal in the symbolic environment.";
        }
        if ("target_seed".equals(model)) {
            return "Target seed dependency that should be preserved in the symbolic slice.";
        }
        if ("path_condition".equals(model)) {
            return "Model as path condition or ITE guard.";
        }
        if ("exception_condition".equals(model)) {
            return "Model as exception feasibility condition.";
        }
        return "Local def-use dependency inside an observed method context.";
    }

    private static String guidanceExpressionHint(String model) {
        if ("port_mapping_candidate".equals(model)) {
            return "no assertion; await runtime fingerprint equality or captured transformation summaries";
        }
        if ("heap_latest_write".equals(model)) {
            return "read(field) := latestWrite(field, readSeq)";
        }
        if ("symbolic_map_state".equals(model)) {
            return "mapValue := symbolicMapGet(mapState, key); mapState' := symbolicMapPut(mapState, key, value)";
        }
        if ("heap_write".equals(model)) {
            return "Heap(receiver, field) := sourceExpr";
        }
        if ("heap_read".equals(model)) {
            return "local := Field(receiver, field)";
        }
        if ("constructor_summary".equals(model)) {
            return "object := ConstructorSummary(args)";
        }
        if ("method_return_summary".equals(model)) {
            return "lhs := MethodSummary(receiver, args)";
        }
        if ("argument_binding".equals(model)) {
            return "formal := actual";
        }
        if ("target_seed".equals(model)) {
            return "target := seedExpression(operands)";
        }
        if ("path_condition".equals(model)) {
            return "path := path && guardExpr";
        }
        if ("exception_condition".equals(model)) {
            return "exceptionFeasible := condition";
        }
        return "to := from";
    }

    private static String guidancePrecision(String model) {
        if ("heap_latest_write".equals(model) || "heap_read".equals(model)
                || "heap_write".equals(model)) {
            return "runtime_object_field_level";
        }
        if ("port_mapping_candidate".equals(model)) {
            return "mapping_only_not_eligible_for_automatic_smt";
        }
        if ("symbolic_map_state".equals(model)) {
            return "map_object_level_without_entry_equality";
        }
        if ("method_return_summary".equals(model)
                || "constructor_summary".equals(model)) {
            return "static_context_instantiated";
        }
        return "static_context_instantiated";
    }

    private static String modelRequirementJson(String model, int count) {
        return jsonObject(
                "model", model,
                "edgeCount", count,
                "summary", guidanceSummary(model),
                "expressionHint", guidanceExpressionHint(model),
                "precision", guidancePrecision(model));
    }

    private static List<String> symbolicMergePoints(
            Map<String, EdgeAccumulator> roleEdges) {
        Map<String, List<EdgeAccumulator>> incoming = new LinkedHashMap<>();
        for (EdgeAccumulator edge : roleEdges.values()) {
            if (!shouldEmitGuidanceEdge(edge)) {
                continue;
            }
            List<EdgeAccumulator> edges = incoming.get(edge.to);
            if (edges == null) {
                edges = new ArrayList<>();
                incoming.put(edge.to, edges);
            }
            edges.add(edge);
        }
        List<String> result = new ArrayList<>();
        int index = 0;
        for (Map.Entry<String, List<EdgeAccumulator>> entry : incoming.entrySet()) {
            List<EdgeAccumulator> edges = entry.getValue();
            if (edges.size() < 2 || !interestingMergeTarget(entry.getKey(), edges)) {
                continue;
            }
            result.add(jsonObject(
                    "id", "MERGE." + index++,
                    "target", entry.getKey(),
                    "incomingCount", edges.size(),
                    "incomingKinds", incomingKinds(edges),
                    "suggestedModel", suggestedMergeModel(entry.getKey(), edges),
                    "guidance", "Use Merge(...) for role-level summaries; use runtime sequence/latest-write when a concrete occurrence is selected."));
            if (result.size() >= 200) {
                break;
            }
        }
        return result;
    }

    private static boolean interestingMergeTarget(String target,
                                                  List<EdgeAccumulator> edges) {
        String text = lower(target);
        if (text.contains("keyid") || text.contains("currentkey")
                || text.contains("allkeys") || text.contains("exportedblockkeys")
                || text.contains("dataencryptionkey")
                || text.contains("getblockkeys")
                || text.contains("retrievepassword")
                || text.contains("retrievedataencryptionkey")
                || text.contains("sasl")) {
            return true;
        }
        for (EdgeAccumulator edge : edges) {
            String model = guidanceModel(edge);
            if ("rpc_transfer_summary".equals(model)
                    || "protocol_sasl_transfer".equals(model)
                    || "heap_latest_write".equals(model)
                    || "symbolic_map_state".equals(model)) {
                return true;
            }
        }
        return false;
    }

    private static String incomingKinds(List<EdgeAccumulator> edges) {
        Set<String> kinds = new LinkedHashSet<>();
        for (EdgeAccumulator edge : edges) {
            kinds.add(edge.kind);
        }
        return join(kinds, ";");
    }

    private static String suggestedMergeModel(String target,
                                              List<EdgeAccumulator> edges) {
        String text = lower(target);
        if (text.contains("allkeys") || text.contains("<java.util.map:")) {
            return "SymbolicMapState/MergeMapUpdates";
        }
        if (text.contains("currentkey") || text.contains("encryptionkey")) {
            return "merge_latest(fieldWrites)";
        }
        if (text.contains(".return")) {
            return "Merge(MethodSummary alternatives)";
        }
        return "Merge(incomingExpressions)";
    }

    private static List<String> symbolicGuidanceLimitations() {
        List<String> limitations = new ArrayList<>();
        limitations.add(jsonObject(
                "id", "lim.method_return_values",
                "summary", "A method return becomes a relation only after its region is captured; a runtime digest proves concrete equality, not a general transformer.",
                "impact", "Keep uncaptured return transformers uninterpreted."));
        limitations.add(jsonObject(
                "id", "lim.role_merge",
                "summary", "Role graph merges multiple runtime occurrences.",
                "impact", "Use object-level graph and runtime seq for a concrete occurrence; use Merge(...) for role-level guidance."));
        limitations.add(jsonObject(
                "id", "lim.latest_write",
                "summary", "runtime_field_state is latest observed write by process, receiver object, and field signature.",
                "impact", "Treat as execution guidance, not a full Java happens-before proof."));
        limitations.add(jsonObject(
                "id", "lim.map_entries",
                "summary", "Map put/get/remove entry equality is not dynamically validated.",
                "impact", "Keep the map as symbolic state unless entry-level region summaries are captured."));
        limitations.add(jsonObject(
                "id", "lim.rpc_correlation",
                "summary", "Static RPC/protocol edges are format and port mappings only.",
                "impact", "Exclude them from automatic SMT until complete endpoint fingerprints or captured encode/decode regions establish the relation."));
        return limitations;
    }

    private static StaticEdge findStaticEdge(Collection<StaticEdge> edges,
                                             String kindNeedle,
                                             String... needles) {
        String kind = lower(kindNeedle);
        for (StaticEdge edge : edges) {
            if (edge == null) {
                continue;
            }
            if (!kind.isEmpty() && !lower(edge.kind).contains(kind)) {
                continue;
            }
            String text = staticEdgeText(edge);
            boolean matches = true;
            if (needles != null) {
                for (String needle : needles) {
                    String value = lower(needle);
                    if (!value.isEmpty() && !text.contains(value)) {
                        matches = false;
                        break;
                    }
                }
            }
            if (matches) {
                return edge;
            }
        }
        return null;
    }

    private static String staticEdgeText(StaticEdge edge) {
        if (edge == null) {
            return "";
        }
        return lower(edge.kind + "\n" + edge.fromCell + "\n" + edge.toCell
                + "\n" + edge.method + "\n" + edge.id);
    }

    private static EdgeAccumulator findRoleEdge(Collection<EdgeAccumulator> edges,
                                                String kindNeedle,
                                                String... needles) {
        String kind = lower(kindNeedle);
        for (EdgeAccumulator edge : edges) {
            if (!kind.isEmpty() && !lower(edge.kind).contains(kind)) {
                continue;
            }
            String text = edgeText(edge);
            boolean matches = true;
            if (needles != null) {
                for (String needle : needles) {
                    String value = lower(needle);
                    if (!value.isEmpty() && !text.contains(value)) {
                        matches = false;
                        break;
                    }
                }
            }
            if (matches) {
                return edge;
            }
        }
        return null;
    }

    private static String edgeText(EdgeAccumulator edge) {
        if (edge == null) {
            return "";
        }
        return lower(edge.kind + "\n" + edge.from + "\n" + edge.to + "\n"
                + edge.method + "\n" + edge.firstFromContext.process + "\n"
                + edge.firstToContext.process);
    }

    private static String lower(String value) {
        return value == null ? "" : value.toLowerCase(Locale.ROOT);
    }

    private static RuntimeFieldBridgeStats addRuntimeFieldBridges(
            Set<String> emittedNodes, List<String> nodeJson,
            Map<String, EdgeAccumulator> emittedEdges,
            Set<String> emittedRoleNodes, List<String> roleNodeJson,
            Map<String, EdgeAccumulator> emittedRoleEdges) {
        RuntimeFieldBridgeStats stats = new RuntimeFieldBridgeStats();
        Map<String, FieldEvent> latestWrites = new LinkedHashMap<>();
        int bridgeId = 0;
        for (FieldEvent event : FIELD_EVENTS) {
            if (event.receiverObjectId == 0 || event.field == null
                    || event.field.isEmpty()) {
                continue;
            }
            String fieldObjectKey = event.process + "|" + event.receiverObjectId
                    + "|" + event.field;
            if ("FIELD_WRITE".equals(event.kind)) {
                latestWrites.put(fieldObjectKey, event);
                continue;
            }
            if (!"FIELD_READ".equals(event.kind)) {
                continue;
            }
            FieldEvent write = latestWrites.get(fieldObjectKey);
            if (write == null) {
                continue;
            }
            MethodContext writeContext = CONTEXTS.get(fieldEventContextKey(write));
            MethodContext readContext = CONTEXTS.get(fieldEventContextKey(event));
            if (writeContext == null || readContext == null) {
                continue;
            }
            String fromCell = runtimeFieldCell(write);
            String toCell = runtimeFieldCell(event);
            StaticEdge edge = new StaticEdge("RTFIELD." + bridgeId++,
                    "runtime_field_state",
                    fromCell,
                    toCell,
                    write.method + " -> " + event.method,
                    -1);
            stats.inputCount++;

            String fromId = nodeId(writeContext, fromCell);
            String toId = nodeId(readContext, toCell);
            if (emittedNodes.add(fromId)) {
                nodeJson.add(nodeJson(writeContext, fromId, fromCell));
            }
            if (emittedNodes.add(toId)) {
                nodeJson.add(nodeJson(readContext, toId, toCell));
            }
            String edgeKey = edgeKey(edge, fromId, toId);
            EdgeAccumulator accumulator = emittedEdges.get(edgeKey);
            if (accumulator == null) {
                if (emittedEdges.size() >= maxGraphEdges) {
                    stats.truncated = true;
                    stats.skippedGraphEdgeInstances++;
                } else {
                    accumulator = new EdgeAccumulator(edge, fromId, toId,
                            writeContext, readContext);
                    emittedEdges.put(edgeKey, accumulator);
                }
            } else {
                accumulator.observe(edge, writeContext, readContext);
                stats.mergedInputCount++;
            }

            String roleFromCell = roleCell(fromCell);
            String roleToCell = roleCell(toCell);
            String roleFromId = roleNodeId(writeContext, roleFromCell);
            String roleToId = roleNodeId(readContext, roleToCell);
            if (emittedRoleNodes.add(roleFromId)) {
                roleNodeJson.add(roleNodeJson(writeContext, roleFromId,
                        roleFromCell));
            }
            if (emittedRoleNodes.add(roleToId)) {
                roleNodeJson.add(roleNodeJson(readContext, roleToId,
                        roleToCell));
            }
            String roleEdgeKey = roleEdgeKey(edge, roleFromId, roleToId);
            EdgeAccumulator roleAccumulator = emittedRoleEdges.get(roleEdgeKey);
            if (roleAccumulator == null) {
                if (emittedRoleEdges.size() >= maxGraphEdges) {
                    stats.roleTruncated = true;
                    stats.skippedRoleGraphEdgeInstances++;
                } else {
                    roleAccumulator = new EdgeAccumulator(edge, roleFromId,
                            roleToId, writeContext, readContext);
                    emittedRoleEdges.put(roleEdgeKey, roleAccumulator);
                }
            } else {
                roleAccumulator.observe(edge, writeContext, readContext);
                stats.roleMergedInputCount++;
            }
        }
        return stats;
    }

    private static ContextPairSelection contextsForGraphEdge(StaticEdge edge,
            Map<String, List<MethodContext>> contextsByMethod) {
        if (isCrossBoundaryMappingEdge(edge)) {
            String fromEndpointMethod = embeddedMethodSignature(edge.fromCell);
            String toEndpointMethod = embeddedMethodSignature(edge.toCell);
            if (toEndpointMethod.isEmpty()) {
                toEndpointMethod = edge.method;
            }
            List<MethodContext> fromContexts = contextsByMethod.get(fromEndpointMethod);
            List<MethodContext> toContexts = contextsByMethod.get(toEndpointMethod);
            if (fromContexts != null && !fromContexts.isEmpty()
                    && toContexts != null && !toContexts.isEmpty()) {
                return pairContexts(fromContexts, toContexts);
            }
        }
        List<MethodContext> contexts = contextsByMethod.get(edge.method);
        if (contexts == null || contexts.isEmpty()) {
            return ContextPairSelection.empty();
        }
        List<InstantiatedContextPair> pairs = new ArrayList<>();
        int limit = Math.max(1, maxContextPairsPerEdge);
        int emitted = Math.min(contexts.size(), limit);
        for (int index = 0; index < emitted; index++) {
            MethodContext context = contexts.get(index);
            pairs.add(new InstantiatedContextPair(context, context));
        }
        long skipped = Math.max(0L, (long) contexts.size() - emitted);
        return new ContextPairSelection(pairs, skipped > 0L, skipped);
    }

    private static ContextPairSelection pairContexts(
            List<MethodContext> fromContexts, List<MethodContext> toContexts) {
        List<InstantiatedContextPair> pairs = new ArrayList<>();
        int limit = Math.max(1, maxContextPairsPerEdge);
        long total = saturatedProduct(fromContexts.size(), toContexts.size());
        for (MethodContext fromContext : fromContexts) {
            for (MethodContext toContext : toContexts) {
                pairs.add(new InstantiatedContextPair(fromContext, toContext));
                if (pairs.size() >= limit) {
                    long skipped = Math.max(0L, total - pairs.size());
                    return new ContextPairSelection(pairs, skipped > 0L,
                            skipped);
                }
            }
        }
        return new ContextPairSelection(pairs, false, 0L);
    }

    private static long saturatedProduct(int left, int right) {
        if (left <= 0 || right <= 0) {
            return 0L;
        }
        long result = (long) left * (long) right;
        return result < 0L ? Long.MAX_VALUE : result;
    }

    private static String edgeKey(StaticEdge edge, String fromId, String toId) {
        return edge.kind + "\n" + edge.method + "\n" + fromId + "\n" + toId;
    }

    private static String roleEdgeKey(StaticEdge edge, String fromId, String toId) {
        return edge.kind + "\n" + edge.method + "\n" + fromId + "\n" + toId;
    }

    private static List<StaticEdge> readStaticEdges(File file) {
        List<StaticEdge> edges = new ArrayList<>();
        if (file == null || !file.isFile()) {
            return edges;
        }
        try {
            List<String> lines = Files.readAllLines(file.toPath(), StandardCharsets.UTF_8);
            for (String line : lines) {
                String id = jsonField(line, "id");
                String kind = jsonField(line, "kind");
                String fromCell = jsonField(line, "fromCell");
                String toCell = jsonField(line, "toCell");
                String method = jsonField(line, "method");
                int unitIndex = jsonIntField(line, "unitIndex", -1);
                if (!method.isEmpty() && !fromCell.isEmpty() && !toCell.isEmpty()) {
                    edges.add(new StaticEdge(id, kind, fromCell, toCell, method, unitIndex));
                }
            }
        } catch (IOException ignored) {
        }
        return edges;
    }

    private static String nodeJson(MethodContext context, String id, String cell) {
        return jsonObject(
                "id", id,
                "process", context.process,
                "threadName", context.threadName,
                "tid", context.tid,
                "objectId", context.objectId,
                "method", context.method,
                "cell", cell,
                "label", "[" + context.process + ", " + context.threadName
                        + "#" + context.tid + "] " + cell);
    }

    private static String nodeId(MethodContext context, String cell) {
        return context.process + "|" + context.threadName + "|" + context.tid
                + "|" + context.objectId + "|" + context.method + "|" + cell;
    }

    private static String roleNodeJson(MethodContext context, String id, String cell) {
        String threadRole = threadRole(context.threadName);
        return jsonObject(
                "id", id,
                "process", context.process,
                "threadRole", threadRole,
                "method", context.method,
                "cell", cell,
                "label", "[" + context.process + ", " + threadRole + "] " + cell);
    }

    private static String roleNodeId(MethodContext context, String cell) {
        return context.process + "|" + threadRole(context.threadName)
                + "|" + context.method + "|" + cell;
    }

    private static String roleCell(String cell) {
        if (cell == null) {
            return "";
        }
        int cut = -1;
        String[] markers = new String[]{
                "@methodObject:", "@fieldObject:", "@valueObject:", "@value:"};
        for (String marker : markers) {
            int index = cell.indexOf(marker);
            if (index >= 0 && (cut < 0 || index < cut)) {
                cut = index;
            }
        }
        return cut < 0 ? cell : cell.substring(0, cut);
    }

    private static String instantiateCell(MethodContext context, StaticEdge edge, String cell) {
        if (!isFieldCell(cell)) {
            return cell;
        }
        FieldEvent event = FIELD_EVENTS_BY_CONTEXT_UNIT.get(fieldEventKey(
                context.process, context.threadName, context.tid, context.method,
                context.objectId, edge.unitIndex, cell));
        if (event == null) {
            return cell + "@methodObject:" + context.objectId;
        }
        StringBuilder builder = new StringBuilder(cell)
                .append("@fieldObject:").append(event.receiverObjectId);
        if (event.valueObjectId != 0) {
            builder.append("@valueObject:").append(event.valueObjectId);
        }
        if (event.primitiveValue != null && !event.primitiveValue.isEmpty()) {
            builder.append("@value:").append(event.primitiveValue);
        }
        return builder.toString();
    }

    private static boolean isFieldCell(String cell) {
        return cell != null
                && cell.startsWith("<")
                && cell.contains(":")
                && !cell.contains(">(")
                && !cell.endsWith(".return")
                && !cell.contains(".param");
    }

    private static String fieldEventKey(String process, String threadName, long tid,
                                        String method, int methodObjectId,
                                        int unitIndex, String field) {
        return process + "|" + threadName + "|" + tid + "|" + methodObjectId
                + "|" + method + "|" + unitIndex + "|" + field;
    }

    private static String fieldEventContextKey(FieldEvent event) {
        return event.process + "|" + event.threadName + "|" + event.tid
                + "|" + event.methodObjectId + "|" + event.method;
    }

    private static String runtimeFieldCell(FieldEvent event) {
        StringBuilder builder = new StringBuilder(event.field)
                .append("@fieldObject:").append(event.receiverObjectId);
        if (event.valueObjectId != 0) {
            builder.append("@valueObject:").append(event.valueObjectId);
        }
        if (event.primitiveValue != null && !event.primitiveValue.isEmpty()) {
            builder.append("@value:").append(event.primitiveValue);
        }
        return builder.toString();
    }

    private static String inferProcessName(String method, String threadName) {
        String methodProcess = processForMethod(method);
        if (!methodProcess.isEmpty()) {
            return methodProcess;
        }
        StringBuilder evidence = new StringBuilder();
        evidence.append(method == null ? "" : method).append(' ')
                .append(threadName == null ? "" : threadName);
        StackTraceElement[] stack = Thread.currentThread().getStackTrace();
        int limit = Math.min(stack.length, 48);
        for (int i = 0; i < limit; i++) {
            evidence.append(' ').append(stack[i].getClassName())
                    .append('.').append(stack[i].getMethodName());
        }
        String evidenceText = evidence.toString();
        String configuredProcess = matchConfiguredRole(
                "causynth.trace.process.patterns",
                "CAUSYNTH_TRACE_PROCESS_PATTERNS",
                evidenceText);
        if (!configuredProcess.isEmpty()) {
            return configuredProcess;
        }
        String lower = evidenceText.toLowerCase(Locale.ROOT);
        if (lower.contains("balancer") || lower.contains("keymanager")
                || lower.contains("namenodeconnector")) {
            return "balancer";
        }
        if (lower.contains("datanode") || lower.contains("dataxceiver")
                || lower.contains("bpserviceactor")
                || lower.contains("sasldatatransferserver")) {
            return "datanode";
        }
        if (lower.contains("namenode") || lower.contains("fsnamesystem")
                || lower.contains("blockmanager")
                || lower.contains("namesystem")) {
            return "namenode";
        }
        if (lower.contains("sasldatatransferclient") || lower.contains("dfsclient")
                || lower.contains("client")) {
            return "client";
        }
        return "unknown";
    }

    private static String normalizeRecordedProcess(String recorded, String method,
                                                   String threadName) {
        String methodProcess = processForMethod(method);
        if (!methodProcess.isEmpty()) {
            return methodProcess;
        }
        return firstNonBlank(recorded, inferProcessName(method, threadName), "unknown");
    }

    /**
     * Returns a role only when the method itself is unambiguous.  This must run
     * before stack/thread heuristics: an in-process MiniDFSCluster RPC handler
     * can have DataNode-originated frames while executing NameNode code.
     */
    private static String processForMethod(String method) {
        String lower = lower(method);
        if (lower.isEmpty()) {
            return "";
        }
        if (lower.contains("server.balancer")
                || lower.contains("keymanager")) {
            return "balancer";
        }
        if (lower.contains("server.namenode")
                || lower.contains("server.blockmanagement")
                || lower.contains("namenodeprotocolserversidetranslatorpb")
                || lower.contains("namenoderpcserver")) {
            return "namenode";
        }
        if (lower.contains("server.datanode")
                || lower.contains("sasldatatransferserver")) {
            return "datanode";
        }
        if (lower.contains("blocktokensecretmanager: boolean updatekeys(")
                || lower.contains("blocktokensecretmanager: void generatekeys(")
                || lower.contains("blocktokensecretmanager: org.apache.hadoop.hdfs.security.token.block.exportedblockkeys exportkeys(")) {
            return "namenode";
        }
        return "";
    }

    private static String threadRole(String threadName) {
        if (threadName == null || threadName.trim().isEmpty()) {
            return "unknown-thread";
        }
        String value = threadName.trim();
        String configuredRole = matchConfiguredRole(
                "causynth.trace.thread.roles",
                "CAUSYNTH_TRACE_THREAD_ROLES",
                value);
        if (!configuredRole.isEmpty()) {
            return configuredRole;
        }
        String lower = value.toLowerCase(Locale.ROOT);
        if (lower.contains("keymanager$blockkeyupdater")) {
            return "KeyManager$BlockKeyUpdater";
        }
        if (lower.contains("heartbeatmanager$monitor")) {
            return "HeartbeatManager$Monitor";
        }
        if (lower.contains("dataxceiver")) {
            return "DataXceiver";
        }
        if (lower.contains("heartbeating to")) {
            return "BPServiceActor heartbeating";
        }
        if (lower.contains("datastreamer")) {
            return "DataStreamer";
        }
        if (lower.contains("ipc server handler")) {
            return "IPC Server handler";
        }
        if (lower.contains("sasldatatransfer")) {
            return "SaslDataTransfer";
        }
        if ("main".equals(lower)) {
            return "main";
        }
        if (value.matches("Thread-\\d+")) {
            return "Thread";
        }
        return value.replaceAll("@[0-9a-fA-F]+", "@*")
                .replaceAll("\\d+", "#");
    }

    private static String matchConfiguredRole(String propertyName, String envName,
                                              String evidence) {
        String spec = firstNonBlank(System.getProperty(propertyName),
                System.getenv(envName), "");
        if (spec.isEmpty() || evidence == null) {
            return "";
        }
        for (String rawEntry : spec.split(";")) {
            String entry = rawEntry.trim();
            if (entry.isEmpty()) {
                continue;
            }
            int equals = entry.indexOf('=');
            if (equals <= 0 || equals == entry.length() - 1) {
                continue;
            }
            String role = entry.substring(0, equals).trim();
            String regex = entry.substring(equals + 1).trim();
            if (role.isEmpty() || regex.isEmpty()) {
                continue;
            }
            try {
                if (Pattern.compile(regex, Pattern.CASE_INSENSITIVE)
                        .matcher(evidence).find()) {
                    return role;
                }
            } catch (RuntimeException ignored) {
            }
        }
        return "";
    }

    private static String jsonField(String json, String field) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(field)
                + "\"\\s*:\\s*\"((?:\\\\.|[^\"])*)\"").matcher(json);
        if (!matcher.find()) {
            return "";
        }
        return unescape(matcher.group(1));
    }

    private static int jsonIntField(String json, String field, int fallback) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(field)
                + "\"\\s*:\\s*(-?\\d+)").matcher(json);
        if (!matcher.find()) {
            return fallback;
        }
        try {
            return Integer.parseInt(matcher.group(1));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static long jsonLongField(String json, String field, long fallback) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(field)
                + "\"\\s*:\\s*(-?\\d+)").matcher(json);
        if (!matcher.find()) {
            return fallback;
        }
        try {
            return Long.parseLong(matcher.group(1));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static boolean jsonBooleanField(String json, String field,
                                            boolean fallback) {
        Matcher matcher = Pattern.compile("\"" + Pattern.quote(field)
                + "\"\\s*:\\s*(true|false)", Pattern.CASE_INSENSITIVE)
                .matcher(json);
        return matcher.find() ? Boolean.parseBoolean(matcher.group(1)) : fallback;
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
            int equals = key.indexOf('=');
            if (equals >= 0) {
                value = key.substring(equals + 1);
                key = key.substring(0, equals);
            } else if (i + 1 < args.length && args[i + 1] != null
                    && !args[i + 1].startsWith("--")) {
                value = args[++i];
            }
            params.put(key, value);
        }
        return params;
    }

    private static void writeSeedChainSummary(List<StaticEdge> staticEdges) {
        File file = new File(outputDir, "seed_chain_summary.jsonl");
        SummarySelection selection = summarySelection(staticEdges);
        TreeMap<Long, String> lines = new TreeMap<>();
        for (TraceEvent event : EVENTS) {
            if (selection.methods.contains(event.method)) {
                lines.put(event.id, jsonObject(
                        "event", "METHOD_ENTER",
                        "seq", event.id,
                        "process", event.process,
                        "threadName", event.threadName,
                        "tid", event.tid,
                        "objectId", event.objectId,
                        "method", event.method,
                        "timeNanos", event.timeNanos));
            }
        }
        for (FieldEvent event : FIELD_EVENTS) {
            if (summaryFieldRelevant(selection, event)) {
                lines.put(event.id, jsonObject(
                        "event", event.kind,
                        "seq", event.id,
                        "process", event.process,
                        "threadName", event.threadName,
                        "tid", event.tid,
                        "objectId", event.methodObjectId,
                        "unitIndex", event.unitIndex,
                        "field", event.field,
                        "fieldReceiverObjectId", event.receiverObjectId,
                        "valueObjectId", event.valueObjectId,
                        "primitiveValue", event.primitiveValue,
                        "method", event.method,
                        "timeNanos", event.timeNanos));
            }
        }
        StringBuilder builder = new StringBuilder();
        int count = 0;
        for (String line : lines.values()) {
            if (count++ >= 5000) {
                break;
            }
            builder.append(line).append('\n');
        }
        writeFile(file, builder.toString());
    }

    private static SummarySelection summarySelection(List<StaticEdge> staticEdges) {
        SummarySelection selection = new SummarySelection();
        if (staticEdges == null) {
            return selection;
        }
        for (StaticEdge edge : staticEdges) {
            if (edge == null) {
                continue;
            }
            if (edge.method != null && !edge.method.isEmpty()) {
                selection.methods.add(edge.method);
            }
            collectSummaryCell(selection, edge.fromCell);
            collectSummaryCell(selection, edge.toCell);
        }
        return selection;
    }

    private static void collectSummaryCell(SummarySelection selection, String cell) {
        if (cell == null || cell.isEmpty()) {
            return;
        }
        String method = embeddedMethodSignature(cell);
        if (!method.isEmpty()) {
            selection.methods.add(method);
        }
        Matcher field = Pattern.compile("<[^:]+:\\s+[^()<>]+\\s+[^\\s()>]+>")
                .matcher(cell);
        while (field.find()) {
            String signature = field.group();
            if (signature.contains("(")) {
                continue;
            }
            selection.fieldSignatures.add(signature);
            String name = fieldNameFromSignature(signature);
            if (!name.isEmpty()) {
                selection.fieldNames.add(name);
            }
        }
        Matcher projected = Pattern.compile("#field:([^#@]+)").matcher(cell);
        while (projected.find()) {
            String name = projected.group(1).trim();
            if (!name.isEmpty()) {
                selection.fieldNames.add(name);
            }
        }
    }

    private static boolean summaryFieldRelevant(SummarySelection selection,
                                                FieldEvent event) {
        if (event == null || !selection.methods.contains(event.method)) {
            return false;
        }
        if (selection.fieldSignatures.contains(event.field)) {
            return true;
        }
        String name = fieldNameFromSignature(event.field);
        return !name.isEmpty() && selection.fieldNames.contains(name);
    }

    private static void writeRuntimeRefinedSymbolicPlan(File staticGraph) {
        File configured = new File(firstNonBlank(
                System.getProperty("causynth.symbolic.plan"),
                System.getenv("CAUSYNTH_SYMBOLIC_PLAN"),
                staticGraph == null || staticGraph.getParentFile() == null
                        ? "symbolic_execution_plan.jsonl"
                        : new File(staticGraph.getParentFile(),
                        "symbolic_execution_plan.jsonl").getPath()));
        if (!configured.isFile()) {
            return;
        }

        Map<String, MethodRuntimeEvidence> evidenceByMethod = new LinkedHashMap<>();
        Map<Long, ExecutionEvent> callSitesByInvocation = new LinkedHashMap<>();
        for (TraceEvent event : EVENTS) {
            MethodRuntimeEvidence evidence = runtimeEvidence(evidenceByMethod,
                    event.method);
            evidence.methodEnterCount++;
            if (!event.receiverType.isEmpty()) {
                evidence.receiverTypes.add(event.receiverType);
            }
            evidence.processes.add(event.process);
            evidence.threadRoles.add(threadRole(event.threadName));
        }
        for (ExecutionEvent event : EXECUTION_EVENTS) {
            MethodRuntimeEvidence evidence = runtimeEvidence(evidenceByMethod,
                    event.method);
            evidence.observe(event);
            if ("CALL_SITE_ENTER".equals(event.kind)) {
                callSitesByInvocation.put(event.invocationId, event);
            }
        }

        Map<String, RuntimeCallEdgeEvidence> callEdges = new LinkedHashMap<>();
        for (TraceEvent event : EVENTS) {
            if (event.parentSiteId <= 0L) {
                continue;
            }
            ExecutionEvent site = callSitesByInvocation.get(event.parentSiteId);
            if (site == null) {
                continue;
            }
            MethodRuntimeEvidence callerEvidence = runtimeEvidence(evidenceByMethod,
                    site.method);
            callerEvidence.observedCallees.add(event.method);
            callerEvidence.actualCalleesBySite.add(site.siteId + "=>" + event.method);
            String key = site.method + "\n" + site.siteId + "\n"
                    + site.declaredCallee + "\n" + event.method + "\n"
                    + event.process + "\n" + threadRole(event.threadName);
            RuntimeCallEdgeEvidence edge = callEdges.get(key);
            if (edge == null) {
                edge = new RuntimeCallEdgeEvidence(site.method, site.siteId,
                        site.declaredCallee, event.method, event.process,
                        threadRole(event.threadName), event.receiverType);
                callEdges.put(key, edge);
            }
            edge.occurrences++;
        }

        StringBuilder refined = new StringBuilder();
        try (BufferedReader reader = Files.newBufferedReader(configured.toPath(),
                StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                String trimmed = line.trim();
                if (trimmed.isEmpty()) {
                    continue;
                }
                String method = jsonField(trimmed, "method");
                MethodRuntimeEvidence evidence = evidenceByMethod.get(method);
                if (evidence == null) {
                    evidence = new MethodRuntimeEvidence(method);
                }
                refined.append('{')
                        .append("\"staticPlan\":").append(trimmed).append(',')
                        .append("\"runtimeEvidence\":")
                        .append(evidence.toJson())
                        .append("}\n");
            }
        } catch (IOException ignored) {
            return;
        }
        writeFile(new File(outputDir, "runtime_refined_symbolic_plan.jsonl"),
                refined.toString());

        StringBuilder callEdgeRows = new StringBuilder();
        int emitted = 0;
        for (RuntimeCallEdgeEvidence edge : callEdges.values()) {
            if (emitted++ >= 10000) {
                break;
            }
            callEdgeRows.append(edge.toJson()).append('\n');
        }
        writeFile(new File(outputDir, "runtime_call_edges.jsonl"),
                callEdgeRows.toString());
    }

    /**
     * Binds static same-thread regions to concrete unit-test invocations.  The
     * resulting activation plan is consumed by the concolic replay runner; it
     * is intentionally separate from the descriptive runtime graph.
     */
    private static void writeRuntimeRegionPlans(File staticGraph) {
        File parent = staticGraph == null ? null : staticGraph.getParentFile();
        File regionFile = new File(firstNonBlank(
                System.getProperty("causynth.symbolic.regions"),
                System.getenv("CAUSYNTH_SYMBOLIC_REGIONS"),
                parent == null ? "symbolic_regions.jsonl"
                        : new File(parent, "symbolic_regions.jsonl").getPath()));
        File regionEdgeFile = new File(firstNonBlank(
                System.getProperty("causynth.symbolic.region.edges"),
                System.getenv("CAUSYNTH_SYMBOLIC_REGION_EDGES"),
                parent == null ? "symbolic_region_edges.jsonl"
                        : new File(parent, "symbolic_region_edges.jsonl").getPath()));

        List<RuntimeRegionPlanner.MethodEvent> methods = new ArrayList<>();
        for (TraceEvent event : EVENTS) {
            methods.add(new RuntimeRegionPlanner.MethodEvent(
                    event.id, event.testName, event.process, event.threadName,
                    event.tid, event.method, event.objectId, event.receiverType,
                    event.callId, event.parentCallId, event.parentSiteId,
                    event.timeNanos));
        }
        List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents = new ArrayList<>();
        for (ExecutionEvent event : EXECUTION_EVENTS) {
            runtimeEvents.add(new RuntimeRegionPlanner.RuntimeEvent(
                    event.id, event.kind, event.method, event.callId,
                    event.invocationId, event.parentSiteId, event.siteId,
                    event.declaredCallee, event.argumentIndex,
                    event.runtimeType, event.objectId,
                    event.primitiveValue, event.hasOutcome, event.outcome,
                    event.valueFingerprint,
                    event.valueFingerprintComplete,
                    event.valueFingerprintNodes,
                    event.valueFingerprintReason));
        }
        List<RuntimeRegionPlanner.FieldAccessEvent> fields = new ArrayList<>();
        for (FieldEvent event : FIELD_EVENTS) {
            fields.add(new RuntimeRegionPlanner.FieldAccessEvent(
                    event.id, event.kind, event.method, event.callId,
                    event.unitIndex, event.siteId, event.field,
                    event.receiverObjectId, event.valueObjectId,
                    event.primitiveValue, event.valueFingerprint,
                    event.valueFingerprintComplete,
                    event.valueFingerprintNodes,
                    event.valueFingerprintReason));
        }

        RuntimeRegionPlanner.Result planned = RuntimeRegionPlanner.plan(
                regionFile, regionEdgeFile, methods, runtimeEvents, fields);
        writeFile(new File(outputDir, "runtime_region_instances.jsonl"),
                planned.instancesJsonl());
        writeFile(new File(outputDir, "runtime_region_validation.jsonl"),
                planned.regionValidationsJsonl());
        writeFile(new File(outputDir, "runtime_region_edge_validation.jsonl"),
                planned.edgeValidationsJsonl());
        writeFile(new File(outputDir, "concolic_activation_plan.jsonl"),
                planned.activationsJsonl());
        writeFile(new File(outputDir, "runtime_region_summary.json"),
                planned.summaryJson());
    }

    private static MethodRuntimeEvidence runtimeEvidence(
            Map<String, MethodRuntimeEvidence> evidenceByMethod, String method) {
        String key = safe(method);
        MethodRuntimeEvidence evidence = evidenceByMethod.get(key);
        if (evidence == null) {
            evidence = new MethodRuntimeEvidence(key);
            evidenceByMethod.put(key, evidence);
        }
        return evidence;
    }

    private static void writeRuntimeValidationSummary(List<StaticEdge> staticEdges,
                                                      Map<String, List<MethodContext>> contextsByMethod) {
        File file = new File(outputDir, "runtime_validation_summary.jsonl");
        StringBuilder builder = new StringBuilder();
        int count = 0;
        for (StaticEdge edge : staticEdges) {
            if (!isCrossBoundaryMappingEdge(edge)) {
                continue;
            }
            String fromEndpointMethod = embeddedMethodSignature(edge.fromCell);
            String toEndpointMethod = embeddedMethodSignature(edge.toCell);
            List<MethodContext> contexts = contextsForEdge(edge, fromEndpointMethod,
                    toEndpointMethod, contextsByMethod);
            if (contexts == null || contexts.isEmpty()) {
                continue;
            }
            for (MethodContext context : contexts) {
                builder.append(jsonObject(
                        "event", "CROSS_BOUNDARY_MAPPING",
                        "relation", crossBoundaryRelation(edge.kind),
                        "kind", edge.kind,
                        "staticEdgeId", edge.id,
                        "validated", true,
                        "validationSource", "static_mapping_plus_runtime_method_coverage",
                        "valueCompared", false,
                        "method", edge.method,
                        "process", context.process,
                        "threadName", context.threadName,
                        "tid", context.tid,
                        "objectId", context.objectId,
                        "occurrences", context.occurrences,
                        "firstSeq", context.firstSeq,
                        "lastSeq", context.lastSeq,
                        "fromCell", edge.fromCell,
                        "toCell", edge.toCell,
                        "fromEndpointMethod", fromEndpointMethod,
                        "fromEndpointObserved", fromEndpointMethod.isEmpty()
                                || contextsByMethod.containsKey(fromEndpointMethod),
                        "toEndpointMethod", toEndpointMethod,
                        "toEndpointObserved", toEndpointMethod.isEmpty()
                                || contextsByMethod.containsKey(toEndpointMethod)))
                        .append('\n');
                if (++count >= 2000) {
                    writeFile(file, builder.toString());
                    return;
                }
            }
        }
        writeFile(file, builder.toString());
    }

    private static List<MethodContext> contextsForEdge(StaticEdge edge,
                                                       String fromEndpointMethod,
                                                       String toEndpointMethod,
                                                       Map<String, List<MethodContext>> contextsByMethod) {
        List<MethodContext> contexts = contextsByMethod.get(edge.method);
        if (contexts != null && !contexts.isEmpty()) {
            return contexts;
        }
        if (fromEndpointMethod != null && !fromEndpointMethod.isEmpty()) {
            contexts = contextsByMethod.get(fromEndpointMethod);
            if (contexts != null && !contexts.isEmpty()) {
                return contexts;
            }
        }
        if (toEndpointMethod != null && !toEndpointMethod.isEmpty()) {
            contexts = contextsByMethod.get(toEndpointMethod);
            if (contexts != null && !contexts.isEmpty()) {
                return contexts;
            }
        }
        return Collections.emptyList();
    }

    private static boolean isCrossBoundaryMappingEdge(StaticEdge edge) {
        if (edge == null || edge.kind == null) {
            return false;
        }
        String kind = edge.kind.toLowerCase(Locale.ROOT);
        return kind.contains("rpc") || kind.contains("protocol")
                || kind.contains("sasl") || kind.contains("transfer");
    }

    private static String crossBoundaryRelation(String kind) {
        if (kind == null) {
            return "cross_boundary_mapping";
        }
        String lower = kind.toLowerCase(Locale.ROOT);
        if (lower.contains("rpc")) {
            return "rpc_field_mapping";
        }
        if (lower.contains("protocol") || lower.contains("sasl")
                || lower.contains("transfer")) {
            return "protocol_field_mapping";
        }
        return "cross_boundary_mapping";
    }

    private static String embeddedMethodSignature(String cell) {
        if (cell == null) {
            return "";
        }
        int start = cell.indexOf('<');
        if (start < 0) {
            return "";
        }
        int end = cell.indexOf('>', start);
        if (end < 0) {
            return "";
        }
        String candidate = cell.substring(start, end + 1);
        return candidate.contains("(") && candidate.contains(":") ? candidate : "";
    }

    private static String fieldNameFromSignature(String fieldSignature) {
        if (fieldSignature == null) {
            return "";
        }
        Matcher matcher = Pattern.compile("<[^:]+:\\s+.+\\s+([^\\s>]+)>")
                .matcher(fieldSignature);
        return matcher.find() ? matcher.group(1) : "";
    }

    private static String jsonObject(Object... values) {
        StringBuilder builder = new StringBuilder();
        builder.append('{');
        for (int i = 0; i + 1 < values.length; i += 2) {
            if (i > 0) {
                builder.append(',');
            }
            builder.append(quote(String.valueOf(values[i]))).append(':');
            Object value = values[i + 1];
            if (value instanceof Number || value instanceof Boolean) {
                builder.append(String.valueOf(value));
            } else {
                builder.append(quote(value == null ? "" : String.valueOf(value)));
            }
        }
        builder.append('}');
        return builder.toString();
    }

    private static String join(Collection<String> values) {
        StringBuilder builder = new StringBuilder();
        boolean first = true;
        for (String value : values) {
            if (!first) {
                builder.append(',');
            }
            first = false;
            builder.append(value);
        }
        return builder.toString();
    }

    private static String join(Collection<String> values, String delimiter) {
        StringBuilder builder = new StringBuilder();
        boolean first = true;
        for (String value : values) {
            if (!first) {
                builder.append(delimiter);
            }
            first = false;
            builder.append(value);
        }
        return builder.toString();
    }

    private static String quote(String value) {
        StringBuilder builder = new StringBuilder();
        builder.append('"');
        for (int i = 0; i < value.length(); i++) {
            char ch = value.charAt(i);
            switch (ch) {
                case '"':
                    builder.append("\\\"");
                    break;
                case '\\':
                    builder.append("\\\\");
                    break;
                case '\n':
                    builder.append("\\n");
                    break;
                case '\r':
                    builder.append("\\r");
                    break;
                case '\t':
                    builder.append("\\t");
                    break;
                default:
                    if (ch < 0x20) {
                        builder.append(String.format("\\u%04x", (int) ch));
                    } else {
                        builder.append(ch);
                    }
            }
        }
        builder.append('"');
        return builder.toString();
    }

    private static String unescape(String value) {
        StringBuilder builder = new StringBuilder();
        boolean escaped = false;
        for (int i = 0; i < value.length(); i++) {
            char ch = value.charAt(i);
            if (!escaped) {
                if (ch == '\\') {
                    escaped = true;
                } else {
                    builder.append(ch);
                }
                continue;
            }
            switch (ch) {
                case '"':
                case '\\':
                case '/':
                    builder.append(ch);
                    break;
                case 'n':
                    builder.append('\n');
                    break;
                case 'r':
                    builder.append('\r');
                    break;
                case 't':
                    builder.append('\t');
                    break;
                default:
                    builder.append(ch);
                    break;
            }
            escaped = false;
        }
        if (escaped) {
            builder.append('\\');
        }
        return builder.toString();
    }

    private static void writeFile(File file, String value) {
        try {
            File parent = file.getParentFile();
            if (parent != null && !parent.exists()) {
                parent.mkdirs();
            }
            Files.write(file.toPath(), value.getBytes(StandardCharsets.UTF_8));
        } catch (IOException ignored) {
        }
    }

    private static void writeGraphFile(File file, String summary,
                                       List<String> nodes,
                                       Map<String, EdgeAccumulator> edges,
                                       boolean roleMerged) {
        File parent = file.getParentFile();
        if (parent != null && !parent.exists()) {
            parent.mkdirs();
        }
        try (BufferedWriter writer = Files.newBufferedWriter(file.toPath(),
                StandardCharsets.UTF_8)) {
            writer.write("{\"summary\":");
            writer.write(summary);
            writer.write(",\"nodes\":[");
            writeJsonElements(writer, nodes);
            writer.write("],\"edges\":[");
            writeEdgeJsonElements(writer, edges.values(), roleMerged);
            writer.write("]}");
        } catch (IOException ignored) {
        }
    }

    private static void writeEdgeJsonElements(BufferedWriter writer,
                                              Collection<EdgeAccumulator> edges,
                                              boolean roleMerged)
            throws IOException {
        boolean first = true;
        int index = 0;
        for (EdgeAccumulator edge : edges) {
            if (!first) {
                writer.write(',');
            }
            String id = (roleMerged ? "ROLE." : "DYN.") + index++;
            writer.write(roleMerged ? edge.toRoleJson(id) : edge.toJson(id));
            first = false;
        }
    }

    private static void writeJsonElements(BufferedWriter writer,
                                          List<String> elements)
            throws IOException {
        boolean first = true;
        for (String element : elements) {
            if (!first) {
                writer.write(',');
            }
            writer.write(element);
            first = false;
        }
    }

    private static void writeShutdownFailure(Throwable throwable) {
        File directory = outputDir == null ? new File("target/causynth-trace") : outputDir;
        String message = throwable == null ? "" : throwable.toString();
        writeFile(new File(directory, "summary.json"), jsonObject(
                "test", testName,
                "status", "shutdown_failure",
                "message", message,
                "traceFile", traceFile == null ? "" : traceFile.getPath(),
                "traceEventCount", EVENTS.size(),
                "fieldEventCount", FIELD_EVENTS.size(),
                "executionEventCount", EXECUTION_EVENTS.size(),
                "maxEvents", maxEvents,
                "maxGraphEdges", maxGraphEdges,
                "maxContextPairsPerEdge", maxContextPairsPerEdge));
    }

    private static String firstNonBlank(String... values) {
        if (values == null) {
            return "";
        }
        for (String value : values) {
            if (value != null && !value.trim().isEmpty()) {
                return value.trim();
            }
        }
        return "";
    }

    private static int parseInt(String value, int fallback) {
        try {
            return Integer.parseInt(value);
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }

    private static final class InstantiatedContextPair {
        private final MethodContext fromContext;
        private final MethodContext toContext;

        private InstantiatedContextPair(MethodContext fromContext,
                                        MethodContext toContext) {
            this.fromContext = fromContext;
            this.toContext = toContext;
        }
    }

    private static final class ContextPairSelection {
        private final List<InstantiatedContextPair> pairs;
        private final boolean truncated;
        private final long skipped;

        private ContextPairSelection(List<InstantiatedContextPair> pairs,
                                     boolean truncated, long skipped) {
            this.pairs = pairs;
            this.truncated = truncated;
            this.skipped = skipped;
        }

        private static ContextPairSelection empty() {
            return new ContextPairSelection(
                    Collections.<InstantiatedContextPair>emptyList(), false,
                    0L);
        }
    }

    private static final class RuntimeFieldBridgeStats {
        private int inputCount;
        private int mergedInputCount;
        private int roleMergedInputCount;
        private int skippedGraphEdgeInstances;
        private int skippedRoleGraphEdgeInstances;
        private boolean truncated;
        private boolean roleTruncated;
    }

    private static final class EdgeAccumulator {
        private final String kind;
        private final String from;
        private final String to;
        private final String method;
        private final String firstStaticEdgeId;
        private final MethodContext firstFromContext;
        private final MethodContext firstToContext;
        private final Set<String> staticEdgeIds = new LinkedHashSet<>();
        private final Set<String> fromContexts = new LinkedHashSet<>();
        private final Set<String> toContexts = new LinkedHashSet<>();
        private int mergedInstances;
        private int occurrences;
        private long firstSeq = Long.MAX_VALUE;
        private long lastSeq = Long.MIN_VALUE;

        private EdgeAccumulator(StaticEdge edge, String from, String to,
                                MethodContext fromContext,
                                MethodContext toContext) {
            this.kind = edge.kind;
            this.from = from;
            this.to = to;
            this.method = edge.method;
            this.firstStaticEdgeId = edge.id;
            this.firstFromContext = fromContext;
            this.firstToContext = toContext;
            observe(edge, fromContext, toContext);
        }

        private void observe(StaticEdge edge, MethodContext fromContext,
                             MethodContext toContext) {
            staticEdgeIds.add(edge.id);
            fromContexts.add(fromContext.contextKey());
            toContexts.add(toContext.contextKey());
            mergedInstances++;
            occurrences += Math.max(1,
                    Math.max(fromContext.occurrences, toContext.occurrences));
            firstSeq = Math.min(firstSeq,
                    Math.min(fromContext.firstSeq, toContext.firstSeq));
            lastSeq = Math.max(lastSeq,
                    Math.max(fromContext.lastSeq, toContext.lastSeq));
        }

        private String toJson(String id) {
            return jsonObject(
                    "id", id,
                    "staticEdgeId", firstStaticEdgeId,
                    "staticEdgeIds", join(staticEdgeIds, ";"),
                    "kind", kind,
                    "from", from,
                    "to", to,
                    "process", firstToContext.process,
                    "threadName", firstToContext.threadName,
                    "tid", firstToContext.tid,
                    "objectId", firstToContext.objectId,
                    "fromProcess", firstFromContext.process,
                    "fromThreadName", firstFromContext.threadName,
                    "fromTid", firstFromContext.tid,
                    "fromObjectId", firstFromContext.objectId,
                    "toProcess", firstToContext.process,
                    "toThreadName", firstToContext.threadName,
                    "toTid", firstToContext.tid,
                    "toObjectId", firstToContext.objectId,
                    "method", method,
                    "occurrences", occurrences,
                    "mergedInstances", mergedInstances,
                    "fromContextCount", fromContexts.size(),
                    "toContextCount", toContexts.size(),
                    "firstSeq", firstSeq == Long.MAX_VALUE ? 0 : firstSeq,
                    "lastSeq", lastSeq == Long.MIN_VALUE ? 0 : lastSeq);
        }

        private String toRoleJson(String id) {
            return jsonObject(
                    "id", id,
                    "staticEdgeId", firstStaticEdgeId,
                    "staticEdgeIds", join(staticEdgeIds, ";"),
                    "kind", kind,
                    "from", from,
                    "to", to,
                    "fromProcess", firstFromContext.process,
                    "fromThreadRole", threadRole(firstFromContext.threadName),
                    "toProcess", firstToContext.process,
                    "toThreadRole", threadRole(firstToContext.threadName),
                    "method", method,
                    "occurrences", occurrences,
                    "mergedInstances", mergedInstances,
                    "fromContextCount", fromContexts.size(),
                    "toContextCount", toContexts.size(),
                    "firstSeq", firstSeq == Long.MAX_VALUE ? 0 : firstSeq,
                    "lastSeq", lastSeq == Long.MIN_VALUE ? 0 : lastSeq);
        }
    }

    private static final class SummarySelection {
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> fieldSignatures = new LinkedHashSet<>();
        private final Set<String> fieldNames = new LinkedHashSet<>();
    }

    private static final class MethodRuntimeEvidence {
        private final String method;
        private final Set<String> receiverTypes = new LinkedHashSet<>();
        private final Set<String> argumentTypes = new LinkedHashSet<>();
        private final Set<String> returnTypes = new LinkedHashSet<>();
        private final Set<String> exceptionTypes = new LinkedHashSet<>();
        private final Set<String> branchOutcomes = new LinkedHashSet<>();
        private final Set<String> observedCallSites = new LinkedHashSet<>();
        private final Set<String> callsiteReceiverTypes = new LinkedHashSet<>();
        private final Set<String> declaredCallees = new LinkedHashSet<>();
        private final Set<String> observedCallees = new LinkedHashSet<>();
        private final Set<String> actualCalleesBySite = new LinkedHashSet<>();
        private final Set<String> processes = new LinkedHashSet<>();
        private final Set<String> threadRoles = new LinkedHashSet<>();
        private int methodEnterCount;
        private int normalExitCount;
        private int throwExitCount;
        private int callSiteCount;

        private MethodRuntimeEvidence(String method) {
            this.method = safe(method);
        }

        private void observe(ExecutionEvent event) {
            if (event == null) {
                return;
            }
            if (!event.process.isEmpty()) {
                processes.add(event.process);
            }
            if (!event.threadName.isEmpty()) {
                threadRoles.add(threadRole(event.threadName));
            }
            if ("METHOD_ARGUMENT".equals(event.kind)) {
                argumentTypes.add("arg" + event.argumentIndex + ":"
                        + firstNonBlank(event.runtimeType, event.declaredType, "unknown"));
            } else if ("METHOD_EXIT_NORMAL".equals(event.kind)) {
                normalExitCount++;
                if (!event.runtimeType.isEmpty()) {
                    returnTypes.add(event.runtimeType);
                }
            } else if ("METHOD_EXIT_THROW".equals(event.kind)) {
                throwExitCount++;
                if (!event.exceptionType.isEmpty()) {
                    exceptionTypes.add(event.exceptionType);
                }
            } else if ("BRANCH".equals(event.kind)) {
                branchOutcomes.add(event.siteId + "=" + event.outcome);
            } else if ("CALL_SITE_ENTER".equals(event.kind)) {
                callSiteCount++;
                observedCallSites.add(event.siteId);
                if (!event.declaredCallee.isEmpty()) {
                    declaredCallees.add(event.declaredCallee);
                }
                if (!event.runtimeType.isEmpty()) {
                    callsiteReceiverTypes.add(event.siteId + ":" + event.runtimeType);
                }
            } else if ("CALL_SITE_THROW".equals(event.kind)
                    && !event.exceptionType.isEmpty()) {
                exceptionTypes.add(event.exceptionType);
            }
        }

        private String toJson() {
            return jsonObject(
                    "observed", methodEnterCount > 0,
                    "method", method,
                    "methodEnterCount", methodEnterCount,
                    "normalExitCount", normalExitCount,
                    "throwExitCount", throwExitCount,
                    "callSiteCount", callSiteCount,
                    "receiverTypes", join(receiverTypes, ";"),
                    "argumentTypes", join(argumentTypes, ";"),
                    "returnTypes", join(returnTypes, ";"),
                    "exceptionTypes", join(exceptionTypes, ";"),
                    "branchOutcomes", join(branchOutcomes, ";"),
                    "observedCallSites", join(observedCallSites, ";"),
                    "callsiteReceiverTypes", join(callsiteReceiverTypes, ";"),
                    "declaredCallees", join(declaredCallees, ";"),
                    "observedCallees", join(observedCallees, ";"),
                    "actualCalleesBySite", join(actualCalleesBySite, ";"),
                    "processes", join(processes, ";"),
                    "threadRoles", join(threadRoles, ";"),
                    "evidenceLevel", actualCalleesBySite.isEmpty()
                            ? (methodEnterCount > 0 ? "METHOD_OBSERVED" : "UNOBSERVED")
                            : "CALLSITE_CORRELATED");
        }
    }

    private static final class RuntimeCallEdgeEvidence {
        private final String caller;
        private final String siteId;
        private final String declaredCallee;
        private final String actualCallee;
        private final String process;
        private final String threadRole;
        private final String receiverType;
        private int occurrences;

        private RuntimeCallEdgeEvidence(String caller, String siteId,
                                        String declaredCallee, String actualCallee,
                                        String process, String threadRole,
                                        String receiverType) {
            this.caller = safe(caller);
            this.siteId = safe(siteId);
            this.declaredCallee = safe(declaredCallee);
            this.actualCallee = safe(actualCallee);
            this.process = safe(process);
            this.threadRole = safe(threadRole);
            this.receiverType = safe(receiverType);
        }

        private String toJson() {
            return jsonObject(
                    "event", "RUNTIME_CALL_EDGE",
                    "caller", caller,
                    "siteId", siteId,
                    "declaredCallee", declaredCallee,
                    "actualCallee", actualCallee,
                    "receiverType", receiverType,
                    "process", process,
                    "threadRole", threadRole,
                    "occurrences", occurrences,
                    "evidenceLevel", "CALLSITE_CORRELATED");
        }
    }

    private static final class TraceEvent {
        private final long id;
        private final String testName;
        private final String process;
        private final String threadName;
        private final long tid;
        private final String method;
        private final int objectId;
        private final long timeNanos;
        private final long callId;
        private final long parentCallId;
        private final long parentSiteId;
        private final String siteId;
        private final String receiverType;

        private TraceEvent(long id, String testName, String process, String threadName,
                           long tid, String method, int objectId, long timeNanos) {
            this(id, testName, process, threadName, tid, method, objectId,
                    timeNanos, id, 0L, 0L, method + "#entry", "");
        }

        private TraceEvent(long id, String testName, String process, String threadName,
                           long tid, String method, int objectId, long timeNanos,
                           long callId, long parentCallId, long parentSiteId,
                           String siteId, String receiverType) {
            this.id = id;
            this.testName = testName;
            this.process = process;
            this.threadName = threadName;
            this.tid = tid;
            this.method = method;
            this.objectId = objectId;
            this.timeNanos = timeNanos;
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
            this.siteId = safe(siteId);
            this.receiverType = safe(receiverType);
        }

        private String contextKey() {
            return process + "|" + threadName + "|" + tid + "|" + objectId + "|" + method;
        }
    }

    private static final class ExecutionEvent {
        private long id;
        private String kind = "";
        private String testName = "";
        private String process = "";
        private String threadName = "";
        private long tid;
        private String method = "";
        private long callId;
        private long parentCallId;
        private long parentSiteId;
        private long invocationId;
        private String siteId = "";
        private int unitIndex = -1;
        private String declaredCallee = "";
        private int argumentIndex = -1;
        private String declaredType = "";
        private String runtimeType = "";
        private int objectId;
        private String primitiveValue = "";
        private String valueFingerprint = "";
        private boolean valueFingerprintComplete;
        private int valueFingerprintNodes;
        private String valueFingerprintReason = "";
        private String expression = "";
        private boolean outcome;
        private boolean hasOutcome;
        private String exceptionType = "";
        private long timeNanos;

        private static ExecutionEvent fromJson(String line, String eventKind) {
            ExecutionEvent event = new ExecutionEvent();
            event.id = jsonLongField(line, "seq", 0L);
            event.kind = safe(eventKind);
            event.testName = firstNonBlank(jsonField(line, "test"),
                    CausynthTraceRecorder.testName);
            event.process = jsonField(line, "process");
            event.threadName = jsonField(line, "threadName");
            event.tid = jsonLongField(line, "tid", 0L);
            event.method = jsonField(line, "method");
            event.callId = jsonLongField(line, "callId", 0L);
            event.parentCallId = jsonLongField(line, "parentCallId", 0L);
            event.parentSiteId = jsonLongField(line, "parentSiteId", 0L);
            event.invocationId = jsonLongField(line, "invocationId", 0L);
            event.siteId = jsonField(line, "siteId");
            event.unitIndex = jsonIntField(line, "unitIndex", -1);
            event.declaredCallee = jsonField(line, "declaredCallee");
            event.argumentIndex = jsonIntField(line, "argumentIndex", -1);
            event.declaredType = jsonField(line, "declaredType");
            event.runtimeType = jsonField(line, "runtimeType");
            event.objectId = jsonIntField(line, "objectId", 0);
            event.primitiveValue = jsonField(line, "primitiveValue");
            event.valueFingerprint = jsonField(line, "valueFingerprint");
            event.valueFingerprintComplete = jsonBooleanField(line,
                    "valueFingerprintComplete", false);
            event.valueFingerprintNodes = jsonIntField(line,
                    "valueFingerprintNodes", 0);
            event.valueFingerprintReason = jsonField(line,
                    "valueFingerprintReason");
            event.expression = jsonField(line, "expression");
            event.hasOutcome = jsonBooleanField(line, "hasOutcome",
                    "BRANCH".equals(eventKind));
            event.outcome = jsonBooleanField(line, "outcome", false);
            event.exceptionType = jsonField(line, "exceptionType");
            event.timeNanos = jsonLongField(line, "timeNanos", 0L);
            return event;
        }

        private void captureValueFingerprint(Object value,
                                             String primitiveValue) {
            ValueFingerprint fingerprint = valueFingerprintsEnabled
                    ? ValueFingerprint.capture(value, primitiveValue)
                    : ValueFingerprint.disabled();
            valueFingerprint = fingerprint.digest;
            valueFingerprintComplete = fingerprint.complete;
            valueFingerprintNodes = fingerprint.nodes;
            valueFingerprintReason = fingerprint.reason;
        }
    }

    private static final class ActiveCall {
        private final long callId;
        private final long parentCallId;
        private final long parentSiteId;
        private final String method;

        private ActiveCall(long callId, long parentCallId, long parentSiteId,
                           String method) {
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
            this.method = safe(method);
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
            this.siteId = safe(siteId);
            this.caller = safe(caller);
            this.declaredCallee = safe(declaredCallee);
        }
    }

    private static final class FieldEvent {
        private final long id;
        private final String testName;
        private final String process;
        private final String threadName;
        private final long tid;
        private final String method;
        private final int methodObjectId;
        private final int unitIndex;
        private final String kind;
        private final String field;
        private final int receiverObjectId;
        private final int valueObjectId;
        private final String primitiveValue;
        private final String valueFingerprint;
        private final boolean valueFingerprintComplete;
        private final int valueFingerprintNodes;
        private final String valueFingerprintReason;
        private final long timeNanos;
        private final long callId;
        private final String siteId;

        private FieldEvent(long id, String testName, String process, String threadName,
                           long tid, String method, int methodObjectId, int unitIndex,
                           String kind, String field, int receiverObjectId,
                           int valueObjectId, String primitiveValue, long timeNanos) {
            this(id, testName, process, threadName, tid, method, methodObjectId,
                    unitIndex, kind, field, receiverObjectId, valueObjectId,
                    primitiveValue, timeNanos, 0L, siteId(method, unitIndex),
                    "", false, 0, "LEGACY_TRACE_NO_FINGERPRINT");
        }

        private FieldEvent(long id, String testName, String process, String threadName,
                           long tid, String method, int methodObjectId, int unitIndex,
                           String kind, String field, int receiverObjectId,
                           int valueObjectId, String primitiveValue, long timeNanos,
                           long callId, String siteId) {
            this(id, testName, process, threadName, tid, method,
                    methodObjectId, unitIndex, kind, field,
                    receiverObjectId, valueObjectId, primitiveValue,
                    timeNanos, callId, siteId, "", false, 0,
                    "LEGACY_TRACE_NO_FINGERPRINT");
        }

        private FieldEvent(long id, String testName, String process,
                           String threadName, long tid, String method,
                           int methodObjectId, int unitIndex, String kind,
                           String field, int receiverObjectId,
                           int valueObjectId, String primitiveValue,
                           long timeNanos, long callId, String siteId,
                           String valueFingerprint,
                           boolean valueFingerprintComplete,
                           int valueFingerprintNodes,
                           String valueFingerprintReason) {
            this.id = id;
            this.testName = testName;
            this.process = process;
            this.threadName = threadName;
            this.tid = tid;
            this.method = method;
            this.methodObjectId = methodObjectId;
            this.unitIndex = unitIndex;
            this.kind = kind;
            this.field = field;
            this.receiverObjectId = receiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = primitiveValue == null ? "" : primitiveValue;
            this.valueFingerprint = safe(valueFingerprint);
            this.valueFingerprintComplete = valueFingerprintComplete;
            this.valueFingerprintNodes = valueFingerprintNodes;
            this.valueFingerprintReason = safe(valueFingerprintReason);
            this.timeNanos = timeNanos;
            this.callId = callId;
            this.siteId = safe(siteId);
        }
    }

    /**
     * A bounded, digest-only representation of a concrete runtime value.
     *
     * <p>The canonical text never leaves this method.  Only its SHA-256 digest
     * and completeness metadata are written to the trace.  Consequently a
     * static port mapping can be promoted to an equality only when both
     * endpoints were completely observed; reflection failures or bounds
     * produce an explicit non-composable gap instead of an assumed
     * relationship.</p>
     */
    private static final class ValueFingerprint {
        /*
         * These are deliberately small, hard ceilings rather than hints.
         * Fingerprinting runs in the instrumented VM (and, for HDFS, often
         * in the interpreted custom VM), so walking a service/manager object
         * graph here can otherwise dominate the workload.  The useful
         * evidence is the bounded value-shaped prefix: container shape and
         * entries, array elements, and scalar fields such as keyId/expiry.
         */
        private static final int MAX_DEPTH = 5;
        private static final int MAX_NODES = 256;
        private static final int MAX_COLLECTION_ELEMENTS = 64;
        private static final int MAX_TOTAL_ELEMENTS = 128;
        private static final int MAX_FIELDS_PER_OBJECT = 32;
        private static final int MAX_TOTAL_FIELDS = 128;
        private static final int MAX_TEXT_BYTES = 64 * 1024;

        private final String digest;
        private final boolean complete;
        private final int nodes;
        private final String reason;

        private ValueFingerprint(String digest, boolean complete, int nodes,
                                 String reason) {
            this.digest = safe(digest);
            this.complete = complete;
            this.nodes = nodes;
            this.reason = safe(reason);
        }

        private static ValueFingerprint disabled() {
            return new ValueFingerprint("", false, 0,
                    "DISABLED_FOR_CONTEXT_ONLY_CONCOLIC_REPLAY");
        }

        private static ValueFingerprint capture(Object value,
                                                String primitiveValue) {
            try {
                return captureUnchecked(value, primitiveValue);
            } catch (Throwable failure) {
                // Runtime evidence must be observational.  In particular, a
                // shared Map/Collection may change while it is fingerprinted;
                // a ConcurrentModificationException (or any reflective
                // access failure) must never escape into the instrumented
                // HDFS execution.  Incomplete fingerprints are already
                // ineligible for automatic endpoint equality.
                String type = failure.getClass().getName();
                return new ValueFingerprint("", false, 0,
                        "CAPTURE_FAILURE:" + type);
            }
        }

        private static ValueFingerprint captureUnchecked(Object value,
                                                         String primitiveValue) {
            FingerprintState state = new FingerprintState();
            StringBuilder canonical = new StringBuilder();
            if (value == null && primitiveValue != null
                    && !primitiveValue.isEmpty()) {
                state.nodes = 1;
                appendToken(canonical, state, "PRIMITIVE", primitiveValue);
            } else {
                appendValue(value, canonical, state, 0);
            }
            return new ValueFingerprint(sha256(canonical.toString()),
                    state.complete, state.nodes, state.reason);
        }

        private static void appendValue(Object value, StringBuilder out,
                                        FingerprintState state, int depth) {
            if (!state.complete) return;
            if (depth > MAX_DEPTH) {
                state.fail("MAX_DEPTH");
                return;
            }
            if (++state.nodes > state.nodeBudget) {
                state.fail("MAX_NODES");
                return;
            }
            if (value == null) {
                appendToken(out, state, "NULL", "");
                return;
            }
            Class<?> type = value.getClass();
            if (value instanceof CharSequence || value instanceof Number
                    || value instanceof Boolean || value instanceof Character
                    || value instanceof Enum<?>) {
                appendToken(out, state, type.getName(), String.valueOf(value));
                return;
            }
            Integer previous = state.seen.get(value);
            if (previous != null) {
                appendToken(out, state, "REF", String.valueOf(previous));
                return;
            }
            state.seen.put(value, state.seen.size());
            if (type.isArray()) {
                int length = Array.getLength(value);
                appendToken(out, state, "ARRAY", type.getName() + ":" + length);
                int limit = Math.min(length, MAX_COLLECTION_ELEMENTS);
                for (int index = 0; index < limit; index++) {
                    if (!state.takeElement()) return;
                    appendToken(out, state, "INDEX", String.valueOf(index));
                    appendValue(Array.get(value, index), out, state,
                            depth + 1);
                }
                if (length > limit) state.fail("MAX_ARRAY_ELEMENTS");
                return;
            }
            if (value instanceof Map<?, ?>) {
                Map<?, ?> map = (Map<?, ?>) value;
                appendToken(out, state, "MAP", type.getName() + ":" + map.size());
                List<String> entries = new ArrayList<>();
                int count = 0;
                for (Map.Entry<?, ?> entry : map.entrySet()) {
                    if (count++ >= MAX_COLLECTION_ELEMENTS) {
                        state.fail("MAX_MAP_ENTRIES");
                        break;
                    }
                    if (!state.takeElement()) break;
                    FingerprintState entryState = state.childForMapEntry();
                    StringBuilder item = new StringBuilder();
                    appendToken(item, entryState, "KEY", "");
                    appendValue(entry.getKey(), item, entryState, depth + 1);
                    appendToken(item, entryState, "VALUE", "");
                    appendValue(entry.getValue(), item, entryState, depth + 1);
                    if (!entryState.complete) {
                        state.fail(entryState.reason);
                        break;
                    }
                    state.nodes += entryState.nodes;
                    state.elements += entryState.elements;
                    state.fields += entryState.fields;
                    if (state.nodes > state.nodeBudget) {
                        state.fail("MAX_NODES");
                        break;
                    }
                    entries.add(item.toString());
                }
                Collections.sort(entries);
                for (String entry : entries) {
                    appendToken(out, state, "ENTRY", entry);
                    if (!state.complete) break;
                }
                return;
            }
            if (value instanceof Collection<?>) {
                Collection<?> collection = (Collection<?>) value;
                appendToken(out, state, "COLLECTION",
                        type.getName() + ":" + collection.size());
                int index = 0;
                for (Object item : collection) {
                    if (index >= MAX_COLLECTION_ELEMENTS) {
                        state.fail("MAX_COLLECTION_ELEMENTS");
                        break;
                    }
                    if (!state.takeElement()) break;
                    appendToken(out, state, "INDEX", String.valueOf(index++));
                    appendValue(item, out, state, depth + 1);
                }
                return;
            }
            if (value instanceof Class<?> || value instanceof ClassLoader
                    || value instanceof Thread
                    || type.getName().startsWith("java.lang.reflect.")) {
                appendToken(out, state, "OPAQUE_ID", type.getName() + ":"
                        + System.identityHashCode(value));
                state.fail("UNSUPPORTED_RUNTIME_OBJECT:" + type.getName());
                return;
            }
            /*
             * JDK implementation objects are usually service graphs (random
             * providers, executors, class metadata, ...), not serialized data
             * values.  Reflection through them is both unstable across JDKs
             * and extremely expensive under the custom interpreter.  Arrays,
             * collections, strings and boxed primitives were handled above.
             */
            if (isOpaquePlatformObject(type)) {
                appendToken(out, state, "OPAQUE_ID", type.getName() + ":"
                        + System.identityHashCode(value));
                state.fail("OPAQUE_PLATFORM_OBJECT:" + type.getName());
                return;
            }
            appendToken(out, state, "OBJECT", type.getName());
            List<Field> fields = instanceFields(type);
            if (fields.size() > MAX_FIELDS_PER_OBJECT) {
                state.fail("MAX_OBJECT_FIELDS");
                return;
            }
            for (Field field : fields) {
                if (!state.takeField()) return;
                try {
                    if (!field.isAccessible()) field.setAccessible(true);
                    appendToken(out, state, "FIELD", field.getDeclaringClass()
                            .getName() + "#" + field.getName());
                    appendValue(field.get(value), out, state, depth + 1);
                } catch (Throwable failure) {
                    state.fail("INACCESSIBLE_FIELD:"
                            + field.getDeclaringClass().getName() + "#"
                            + field.getName());
                    return;
                }
            }
        }

        private static boolean isOpaquePlatformObject(Class<?> type) {
            String name = type == null ? "" : type.getName();
            return name.startsWith("java.") || name.startsWith("javax.")
                    || name.startsWith("sun.")
                    || name.startsWith("com.sun.")
                    || name.startsWith("jdk.");
        }

        private static List<Field> instanceFields(Class<?> type) {
            List<Field> result = new ArrayList<>();
            Set<String> seen = new LinkedHashSet<>();
            for (Class<?> current = type; current != null
                    && current != Object.class; current = current.getSuperclass()) {
                for (Field field : current.getDeclaredFields()) {
                    int modifiers = field.getModifiers();
                    if (Modifier.isStatic(modifiers)
                            || Modifier.isTransient(modifiers)
                            || field.isSynthetic()) continue;
                    String key = field.getDeclaringClass().getName() + "#"
                            + field.getName();
                    if (seen.add(key)) result.add(field);
                }
            }
            Collections.sort(result, (left, right) -> {
                String leftKey = left.getDeclaringClass().getName() + "#"
                        + left.getName();
                String rightKey = right.getDeclaringClass().getName() + "#"
                        + right.getName();
                return leftKey.compareTo(rightKey);
            });
            return result;
        }

        private static void appendToken(StringBuilder out,
                                        FingerprintState state,
                                        String type, String value) {
            if (!state.complete) return;
            String safeType = safe(type);
            String safeValue = safe(value);
            int remaining = state.byteBudget - state.bytes;
            int typeBytes = utf8LengthCapped(safeType, remaining);
            if (typeBytes > remaining) {
                state.fail("MAX_CANONICAL_BYTES");
                return;
            }
            remaining -= typeBytes;
            int valueBytes = utf8LengthCapped(safeValue, remaining);
            int headerBytes = decimalLength(safeType.length())
                    + decimalLength(safeValue.length()) + 2;
            long tokenBytes = (long) headerBytes + typeBytes + valueBytes;
            if (valueBytes > remaining
                    || tokenBytes > state.byteBudget - state.bytes) {
                state.fail("MAX_CANONICAL_BYTES");
                return;
            }
            out.append(safeType.length()).append(':').append(safeType)
                    .append(safeValue.length()).append(':').append(safeValue);
            state.bytes += (int) tokenBytes;
        }

        private static int decimalLength(int value) {
            if (value < 10) return 1;
            if (value < 100) return 2;
            if (value < 1000) return 3;
            if (value < 10000) return 4;
            if (value < 100000) return 5;
            if (value < 1000000) return 6;
            if (value < 10000000) return 7;
            if (value < 100000000) return 8;
            if (value < 1000000000) return 9;
            return 10;
        }

        /** Returns {@code limit + 1} as soon as the UTF-8 budget is exceeded. */
        private static int utf8LengthCapped(String value, int limit) {
            if (limit < 0) return 0;
            int bytes = 0;
            for (int index = 0; index < value.length(); index++) {
                char item = value.charAt(index);
                if (item <= 0x7f) {
                    bytes++;
                } else if (item <= 0x7ff) {
                    bytes += 2;
                } else if (Character.isHighSurrogate(item)
                        && index + 1 < value.length()
                        && Character.isLowSurrogate(value.charAt(index + 1))) {
                    bytes += 4;
                    index++;
                } else {
                    // Conservatively budget malformed surrogates as a full
                    // three-byte code unit.  The final canonical text can
                    // therefore never exceed this ceiling when encoded.
                    bytes += 3;
                }
                if (bytes > limit) return limit + 1;
            }
            return bytes;
        }

        private static String sha256(String value) {
            try {
                MessageDigest digest = MessageDigest.getInstance("SHA-256");
                byte[] bytes = digest.digest(value.getBytes(
                        StandardCharsets.UTF_8));
                StringBuilder result = new StringBuilder(bytes.length * 2);
                for (byte item : bytes) {
                    result.append(String.format(Locale.ROOT, "%02x",
                            item & 0xff));
                }
                return "sha256:" + result;
            } catch (NoSuchAlgorithmException impossible) {
                throw new IllegalStateException(impossible);
            }
        }
    }

    private static final class FingerprintState {
        private final IdentityHashMap<Object, Integer> seen =
                new IdentityHashMap<>();
        private final int byteBudget;
        private final int nodeBudget;
        private final int elementBudget;
        private final int fieldBudget;
        private boolean complete = true;
        private int nodes;
        private int elements;
        private int fields;
        private int bytes;
        private String reason = "COMPLETE";

        private FingerprintState() {
            this(ValueFingerprint.MAX_TEXT_BYTES,
                    ValueFingerprint.MAX_NODES,
                    ValueFingerprint.MAX_TOTAL_ELEMENTS,
                    ValueFingerprint.MAX_TOTAL_FIELDS);
        }

        private FingerprintState(int byteBudget, int nodeBudget,
                                 int elementBudget, int fieldBudget) {
            this.byteBudget = Math.max(0, byteBudget);
            this.nodeBudget = Math.max(0, nodeBudget);
            this.elementBudget = Math.max(0, elementBudget);
            this.fieldBudget = Math.max(0, fieldBudget);
        }

        private FingerprintState childForMapEntry() {
            FingerprintState child = new FingerprintState(
                    Math.max(0, byteBudget - bytes),
                    Math.max(0, nodeBudget - nodes),
                    Math.max(0, elementBudget - elements),
                    Math.max(0, fieldBudget - fields));
            // Map entries are canonicalized independently so their texts can
            // be sorted, but seed the ancestor identities.  This makes a map
            // that contains itself terminate as REF instead of recursively
            // constructing fresh per-entry states.
            child.seen.putAll(seen);
            return child;
        }

        private boolean takeElement() {
            if (++elements > elementBudget) {
                fail("MAX_TOTAL_ELEMENTS");
                return false;
            }
            return true;
        }

        private boolean takeField() {
            if (++fields > fieldBudget) {
                fail("MAX_TOTAL_FIELDS");
                return false;
            }
            return true;
        }

        private void fail(String why) {
            if (!complete) return;
            complete = false;
            reason = firstNonBlank(why, "INCOMPLETE");
        }
    }

    private static final class MethodContext {
        private final String process;
        private final String threadName;
        private final long tid;
        private final int objectId;
        private final String method;
        private long firstSeq;
        private long lastSeq;
        private int occurrences;

        private MethodContext(TraceEvent event) {
            this.process = event.process;
            this.threadName = event.threadName;
            this.tid = event.tid;
            this.objectId = event.objectId;
            this.method = event.method;
            this.firstSeq = event.id;
        }

        private void observe(TraceEvent event) {
            occurrences++;
            firstSeq = Math.min(firstSeq, event.id);
            lastSeq = Math.max(lastSeq, event.id);
        }

        private String contextKey() {
            return process + "|" + threadName + "|" + tid + "|" + objectId + "|" + method;
        }
    }

    private static final class StaticEdge {
        private final String id;
        private final String kind;
        private final String fromCell;
        private final String toCell;
        private final String method;
        private final int unitIndex;

        private StaticEdge(String id, String kind, String fromCell,
                           String toCell, String method, int unitIndex) {
            this.id = id;
            this.kind = kind;
            this.fromCell = fromCell;
            this.toCell = toCell;
            this.method = method;
            this.unitIndex = unitIndex;
        }
    }
}
