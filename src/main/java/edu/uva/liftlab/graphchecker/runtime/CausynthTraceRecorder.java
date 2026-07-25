package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.CausynthJson;

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
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Pattern;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

public final class CausynthTraceRecorder {
    private static final Object LOCK = new Object();
    private static final AtomicBoolean INITIALIZED = new AtomicBoolean();
    private static final AtomicLong EVENT_COUNTER = new AtomicLong();
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
    /**
     * A plain concolic replay uses the rich-trace call stacks only as exact
     * accessor-site context. It does not publish a runtime trace, so hashing
     * every packet/argument is both semantically unused and prohibitively
     * expensive on the interpreted custom JVM. Campaign discovery supplies
     * an explicit trace output directory and therefore keeps fingerprints.
     * The system property is an auditable override for either mode.
     */
    private static volatile boolean valueFingerprintsEnabled = true;
    private static volatile boolean contextOnlyConcolicReplay;

    private static volatile File outputDir;
    private static volatile File traceFile;
    private static volatile String testName;
    private static volatile int maxEvents;
    /**
     * Rich campaign replays may emit hundreds of thousands of events.  When
     * aggregation is performed by a fresh host JVM, retaining the same rows
     * in the instrumented JVM only doubles memory and can make shutdown
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
        try {
            aggregateExistingTrace(directory, graph, test);
        } catch (Throwable throwable) {
            outputDir = directory;
            traceFile = new File(directory, "runtime_trace.jsonl");
            testName = test;
            maxEvents = DEFAULT_MAX_EVENTS;
            writeShutdownFailure(throwable);
            System.err.println("Failed to aggregate Causynth runtime trace: "
                    + throwable);
            throwable.printStackTrace(System.err);
            System.exit(1);
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
        Deque<ActiveCall> calls = ACTIVE_CALLS.get();
        ActiveCall parent = calls.peek();
        Deque<ActiveCallSite> sites = ACTIVE_CALL_SITES.get();
        ActiveCallSite parentSite = sites.peek();
        long parentCallId = parent == null ? 0L : parent.callId;
        long parentSiteId = parentSite == null ? 0L : parentSite.invocationId;
        TraceEvent event = new TraceEvent(id, process, threadName, tid,
                method, objectId, id, parentCallId, parentSiteId,
                method + "#entry", runtimeType(receiver));
        calls.push(new ActiveCall(id, parentSiteId, method));
        if (contextOnlyConcolicReplay) {
            return id;
        }
        synchronized (LOCK) {
            if (retainRecordedEventsInMemory) {
                EVENTS.add(event);
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
        event.siteId = siteId(event.method, unitIndex);
        event.declaredCallee = safe(declaredCallee);
        event.runtimeType = runtimeType(receiver);
        event.objectId = identity(receiver);
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
        event.siteId = siteId(event.method, unitIndex);
        event.outcome = outcome;
        event.hasOutcome = true;
        emitExecutionEvent(event);
    }

    /** Records one exact case/default successor of a JVM switch. */
    public static void recordSwitchBranch(long callId, String method,
                                          int unitIndex, String expression,
                                          int successorIndex,
                                          String branchKind,
                                          String encodedCaseKeys) {
        ExecutionEvent event = newExecutionEvent("BRANCH",
                firstNonBlank(method, methodForCall(callId)), callId);
        event.siteId = siteId(event.method, unitIndex);
        event.branchKind = safe(branchKind);
        event.switchCaseKeys = safe(encodedCaseKeys);
        event.successorIndex = successorIndex;
        event.hasSuccessorIndex = successorIndex >= 0;
        int caseCount = encodedCaseKeys == null
                || encodedCaseKeys.isEmpty() ? 0
                : encodedCaseKeys.split(",", -1).length;
        event.outcome = successorIndex >= 0 && successorIndex < caseCount;
        event.hasOutcome = event.hasSuccessorIndex;
        emitExecutionEvent(event);
    }

    public static void exitMethod(long callId, Object returnValue,
                                  String primitiveValue) {
        ActiveCall call = activeCall(callId);
        long resolvedCallId = call == null ? callId : call.callId;
        closeCallSites(resolvedCallId, "CALL_SITE_INCOMPLETE");
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_NORMAL",
                call == null ? "" : call.method, resolvedCallId);
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
        closeCallSites(resolvedCallId, "CALL_SITE_THROW");
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_THROW",
                call == null ? "" : call.method, resolvedCallId);
        event.parentSiteId = call == null ? 0L : call.parentSiteId;
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
        int methodObjectId = methodReceiver == null ? 0 : System.identityHashCode(methodReceiver);
        int receiverObjectId = fieldReceiver == null ? 0 : System.identityHashCode(fieldReceiver);
        int valueObjectId = valueObject == null ? 0 : System.identityHashCode(valueObject);
        ValueFingerprint fingerprint = valueFingerprintsEnabled
                ? ValueFingerprint.capture(valueObject, primitiveValue)
                : ValueFingerprint.disabled();
        ActiveCall activeCall = ACTIVE_CALLS.get().peek();
        FieldEvent event = new FieldEvent(id, method, methodObjectId,
                unitIndex, kind, field, receiverObjectId,
                valueObjectId, primitiveValue,
                activeCall == null ? 0L : activeCall.callId,
                siteId(method, unitIndex), fingerprint.digest,
                fingerprint.complete, fingerprint.nodes,
                fingerprint.reason);
        synchronized (LOCK) {
            if (retainRecordedEventsInMemory) {
                FIELD_EVENTS.add(event);
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
        ExecutionEvent event = new ExecutionEvent();
        event.id = id;
        event.kind = safe(kind);
        event.method = safe(method);
        event.callId = callId;
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

    private static void closeCallSite(ActiveCallSite site, String kind) {
        if (site == null) {
            return;
        }
        ExecutionEvent event = newExecutionEvent(kind, site.caller,
                site.ownerCallId);
        event.invocationId = site.invocationId;
        event.siteId = site.siteId;
        event.declaredCallee = site.declaredCallee;
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
                writeFileQuietly(new File(outputDir,
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
                    writeRuntimeRegionArtifacts();
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
                                               String test) throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            outputDir = directory;
            traceFile = new File(directory, "runtime_trace.jsonl");
            testName = test;
            maxEvents = Integer.MAX_VALUE;
            // This JVM is the offline aggregator.  Rows loaded below must be
            // retained regardless of the recording-mode property inherited
            // from a caller.
            retainRecordedEventsInMemory = true;
            traceWriter = null;
            System.setProperty("causynth.static.graph", staticGraph.getPath());
            loadExistingTrace(traceFile);
            writeRuntimeRegionArtifacts();
        }
    }

    private static void clearInMemoryTrace() {
        INITIALIZED.set(false);
        EVENT_COUNTER.set(0L);
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
            int lineNumber = 0;
            while ((line = reader.readLine()) != null) {
                lineNumber++;
                final JsonObject row;
                try {
                    JsonElement parsed = JsonParser.parseString(line);
                    if (!parsed.isJsonObject()) {
                        throw new IllegalArgumentException(
                                "row is not an object");
                    }
                    row = parsed.getAsJsonObject();
                } catch (RuntimeException malformed) {
                    throw new IOException("Malformed runtime trace row "
                            + lineNumber + " in " + file, malformed);
                }
                if (integer(row, "schemaVersion", -1) != 2) {
                    throw new IOException("Unsupported runtime trace row: "
                            + line);
                }
                String eventKind = string(row, "event");
                if ("METHOD_ENTER".equals(eventKind)) {
                    String method = string(row, "method");
                    String threadName = string(row, "threadName");
                    long seq = longInteger(row, "seq", 0L);
                    addTraceEvent(new TraceEvent(
                            seq,
                            normalizeRecordedProcess(string(row, "process"),
                                    method, threadName),
                            threadName,
                            longInteger(row, "tid", 0L),
                            method,
                            integer(row, "objectId", 0),
                            longInteger(row, "callId", seq),
                            longInteger(row, "parentCallId", 0L),
                            longInteger(row, "parentSiteId", 0L),
                            string(row, "siteId"),
                            string(row, "receiverType")));
                } else if ("FIELD_READ".equals(eventKind)
                        || "FIELD_WRITE".equals(eventKind)) {
                    String method = string(row, "method");
                    addFieldEvent(new FieldEvent(
                            longInteger(row, "seq", 0L),
                            method,
                            integer(row, "objectId", 0),
                            integer(row, "unitIndex", -1),
                            eventKind,
                            string(row, "field"),
                            integer(row, "fieldReceiverObjectId", 0),
                            integer(row, "valueObjectId", 0),
                            string(row, "primitiveValue"),
                            longInteger(row, "callId", 0L),
                            string(row, "siteId"),
                            string(row, "valueFingerprint"),
                            bool(row, "valueFingerprintComplete", false),
                            integer(row, "valueFingerprintNodes", 0),
                            string(row, "valueFingerprintReason")));
                } else if (isExecutionEventKind(eventKind)) {
                    addExecutionEvent(ExecutionEvent.fromJson(row, eventKind));
                }
            }
        }
    }

    /**
     * A recorder sequence is allocated before a thread acquires the streaming
     * writer lock.  Consequently a valid multi-threaded trace can contain
     * rows in a different file order from their sequence order.  Every
     * offline consumer uses the recorder sequence as its observation-order
     * authority instead of treating writer-lock acquisition order as
     * execution order.
     */
    private static void normalizeRecordedEventOrder() {
        EVENTS.sort((left, right) -> Long.compare(left.id, right.id));
        FIELD_EVENTS.sort((left, right) -> Long.compare(left.id, right.id));
        EXECUTION_EVENTS.sort((left, right) -> Long.compare(left.id, right.id));
    }

    private static void addTraceEvent(TraceEvent event) {
        if (event == null || event.method == null || event.method.isEmpty()) {
            return;
        }
        EVENTS.add(event);
        EVENT_COUNTER.set(Math.max(EVENT_COUNTER.get(), event.id));
    }

    private static void addFieldEvent(FieldEvent event) {
        if (event == null || event.method == null || event.method.isEmpty()
                || event.field == null || event.field.isEmpty()) {
            return;
        }
        FIELD_EVENTS.add(event);
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
                    "schemaVersion", 2,
                    "event", "METHOD_ENTER",
                    "seq", event.id,
                    "process", event.process,
                    "threadName", event.threadName,
                    "tid", event.tid,
                    "method", event.method,
                    "objectId", event.objectId,
                    "receiverType", event.receiverType,
                    "callId", event.callId,
                    "parentCallId", event.parentCallId,
                    "parentSiteId", event.parentSiteId,
                    "siteId", event.siteId));
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
                    "schemaVersion", 2,
                    "event", event.kind,
                    "seq", event.id,
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
                    "valueFingerprintReason", event.valueFingerprintReason));
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
                    "schemaVersion", 2,
                    "event", event.kind,
                    "seq", event.id,
                    "method", event.method,
                    "callId", event.callId,
                    "parentSiteId", event.parentSiteId,
                    "invocationId", event.invocationId,
                    "siteId", event.siteId,
                    "declaredCallee", event.declaredCallee,
                    "argumentIndex", event.argumentIndex,
                    "runtimeType", event.runtimeType,
                    "objectId", event.objectId,
                    "primitiveValue", event.primitiveValue,
                    "valueFingerprint", event.valueFingerprint,
                    "valueFingerprintComplete", event.valueFingerprintComplete,
                    "valueFingerprintNodes", event.valueFingerprintNodes,
                    "valueFingerprintReason", event.valueFingerprintReason,
                    "outcome", event.hasOutcome ? event.outcome : null,
                    "branchKind", event.branchKind,
                    "switchCaseKeys", event.switchCaseKeys,
                    "successorIndex", event.hasSuccessorIndex
                            ? event.successorIndex : null));
            traceWriter.newLine();
        } catch (IOException ignored) {
            traceWriteFailure = true;
        }
    }

    private static void writeRuntimeRegionArtifacts() throws IOException {
        normalizeRecordedEventOrder();
        File staticGraph = new File(firstNonBlank(
                System.getProperty("causynth.static.graph"),
                System.getenv("CAUSYNTH_STATIC_GRAPH"),
                new File(outputDir, "static_dataflow_edges.jsonl").getPath()));
        writeRuntimeRegionPlans(staticGraph);
    }
    private static String inferProcessName(String method, String threadName) {
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
        return "unknown";
    }

    private static String normalizeRecordedProcess(String recorded, String method,
                                                   String threadName) {
        return firstNonBlank(recorded, inferProcessName(method, threadName), "unknown");
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

    /** Binds frozen static regions to concrete same-thread invocations. */
    private static void writeRuntimeRegionPlans(File staticGraph)
            throws IOException {
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
                    event.id, testName, event.process, event.threadName,
                    event.tid, event.method, event.objectId, event.receiverType,
                    event.callId, event.parentCallId, event.parentSiteId));
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
                    event.valueFingerprintReason,
                    event.hasSuccessorIndex, event.successorIndex,
                    event.branchKind, event.switchCaseKeys));
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
                regionFile, regionEdgeFile, staticGraph, methods,
                runtimeEvents, fields);
        Files.deleteIfExists(new File(outputDir,
                "runtime_region_instances.jsonl").toPath());
        Files.deleteIfExists(new File(outputDir,
                "runtime_region_summary.json").toPath());
        writeFile(new File(outputDir, "runtime_region_edge_validation.jsonl"),
                planned.edgeValidationsJsonl());
        writeFile(new File(outputDir, "concolic_activation_plan.jsonl"),
                planned.activationsJsonl());
    }

    private static String jsonObject(Object... values) {
        return CausynthJson.objectWithoutNulls(values);
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

    private static void writeShutdownFailure(Throwable throwable) {
        File directory = outputDir == null ? new File("target/causynth-trace") : outputDir;
        String message = throwable == null ? "" : throwable.toString();
        writeFileQuietly(new File(directory, "summary.json"), jsonObject(
                "test", testName,
                "status", "shutdown_failure",
                "message", message,
                "traceFile", traceFile == null ? "" : traceFile.getPath(),
                "traceEventCount", EVENTS.size(),
                "fieldEventCount", FIELD_EVENTS.size(),
                "executionEventCount", EXECUTION_EVENTS.size(),
                "maxEvents", maxEvents));
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

    private static final class TraceEvent {
        private final long id;
        private final String process;
        private final String threadName;
        private final long tid;
        private final String method;
        private final int objectId;
        private final long callId;
        private final long parentCallId;
        private final long parentSiteId;
        private final String siteId;
        private final String receiverType;

        private TraceEvent(long id, String process, String threadName,
                           long tid, String method, int objectId,
                           long callId, long parentCallId, long parentSiteId,
            String siteId, String receiverType) {
            this.id = id;
            this.process = process;
            this.threadName = threadName;
            this.tid = tid;
            this.method = method;
            this.objectId = objectId;
            this.callId = callId;
            this.parentCallId = parentCallId;
            this.parentSiteId = parentSiteId;
            this.siteId = safe(siteId);
            this.receiverType = safe(receiverType);
        }
    }

    private static final class ExecutionEvent {
        private long id;
        private String kind = "";
        private String method = "";
        private long callId;
        private long parentSiteId;
        private long invocationId;
        private String siteId = "";
        private String declaredCallee = "";
        private int argumentIndex = -1;
        private String runtimeType = "";
        private int objectId;
        private String primitiveValue = "";
        private String valueFingerprint = "";
        private boolean valueFingerprintComplete;
        private int valueFingerprintNodes;
        private String valueFingerprintReason = "";
        private boolean outcome;
        private boolean hasOutcome;
        private String branchKind = "";
        private String switchCaseKeys = "";
        private boolean hasSuccessorIndex;
        private int successorIndex = -1;

        private static ExecutionEvent fromJson(JsonObject row,
                                               String eventKind) {
            ExecutionEvent event = new ExecutionEvent();
            event.id = longInteger(row, "seq", 0L);
            event.kind = safe(eventKind);
            event.method = string(row, "method");
            event.callId = longInteger(row, "callId", 0L);
            event.parentSiteId = longInteger(row, "parentSiteId", 0L);
            event.invocationId = longInteger(row, "invocationId", 0L);
            event.siteId = string(row, "siteId");
            event.declaredCallee = string(row, "declaredCallee");
            event.argumentIndex = integer(row, "argumentIndex", -1);
            event.runtimeType = string(row, "runtimeType");
            event.objectId = integer(row, "objectId", 0);
            event.primitiveValue = string(row, "primitiveValue");
            event.valueFingerprint = string(row, "valueFingerprint");
            event.valueFingerprintComplete = bool(row,
                    "valueFingerprintComplete", false);
            event.valueFingerprintNodes = integer(row,
                    "valueFingerprintNodes", 0);
            event.valueFingerprintReason = string(row,
                    "valueFingerprintReason");
            event.hasOutcome = row.has("outcome");
            event.outcome = bool(row, "outcome", false);
            event.branchKind = string(row, "branchKind");
            event.switchCaseKeys = string(row, "switchCaseKeys");
            event.hasSuccessorIndex = row.has("successorIndex");
            event.successorIndex = integer(row, "successorIndex", -1);
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
        private final long parentSiteId;
        private final String method;

        private ActiveCall(long callId, long parentSiteId, String method) {
            this.callId = callId;
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
        private final long callId;
        private final String siteId;

        private FieldEvent(long id, String method,
                           int methodObjectId, int unitIndex, String kind,
                           String field, int receiverObjectId,
                           int valueObjectId, String primitiveValue,
                           long callId, String siteId,
                           String valueFingerprint,
                           boolean valueFingerprintComplete,
                           int valueFingerprintNodes,
                           String valueFingerprintReason) {
            this.id = id;
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
         * Fingerprinting runs in the instrumented VM (often the interpreted
         * custom VM), so walking a service/manager object
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
                // execution. Incomplete fingerprints are already
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

}
