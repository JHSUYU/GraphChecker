package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.CausynthJson;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;

import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
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
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.bool;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.longInteger;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.string;

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
    private static final int DEFAULT_MAX_EVENTS = 200000;
    /** A concolic replay keeps call stacks but does not publish a trace. */
    private static volatile boolean contextOnlyConcolicReplay;

    private static volatile File outputDir;
    private static volatile String testName;
    private static volatile int maxEvents;
    /** Guarded by {@link #LOCK}; persisted in the streaming close manifest. */
    private static boolean traceWriteFailure;
    private static BufferedWriter traceWriter;
    /** Guarded by {@link #LOCK}; a reset must not install duplicate hooks. */
    private static boolean shutdownHookRegistered;

    private CausynthTraceRecorder() {
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
        File regions = skeletonOnly ? null
                : new File(requiredArg(params, "regions"));
        File regionEdges = skeletonOnly ? null
                : new File(requiredArg(params, "region-edges"));
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
                        "refined_dataflow_edges.jsonl")
                        : new File(configuredRefined.trim());
                aggregateStateTrace(directory, graph, candidateSkeletons,
                        refinedGraph, regions, regionEdges, test,
                        planOutputDirectory);
            }
        } catch (Throwable throwable) {
            System.err.println("Failed to aggregate Causynth runtime trace: "
                    + throwable);
            throwable.printStackTrace(System.err);
            System.exit(1);
        }
    }

    /** Records a method observation when rich call-frame evidence is unnecessary. */
    public static void record(String method, Object receiver) {
        if (method == null) {
            return;
        }
        initialize();
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents || contextOnlyConcolicReplay) {
            return;
        }
        Thread thread = Thread.currentThread();
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName,
                        inferProcessName(method, thread.getName()),
                        thread.getName(), thread.getId(), method,
                        identity(receiver), runtimeType(receiver),
                        id, 0L, 0L);
        synchronized (LOCK) {
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
        Deque<ActiveCall> calls = ACTIVE_CALLS.get();
        ActiveCall parent = calls.peek();
        Deque<ActiveCallSite> sites = ACTIVE_CALL_SITES.get();
        ActiveCallSite parentSite = sites.peek();
        long parentCallId = parent == null ? 0L : parent.callId;
        long parentSiteId = parentSite == null ? 0L : parentSite.invocationId;
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName, process,
                        threadName, tid, method, objectId,
                        runtimeType(receiver), id, parentCallId, parentSiteId);
        calls.push(new ActiveCall(id, parentSiteId, method));
        if (contextOnlyConcolicReplay) {
            return id;
        }
        synchronized (LOCK) {
            writeTraceLine(event);
        }
        return id;
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
        // Keep the nesting stack balanced even after the trace budget has
        // been exhausted; the silent exit hook must not pop the parent.
        calls.push(new ActiveCall(id, 0L, method));
        if (id > maxEvents) {
            return id;
        }
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName,
                        inferProcessName(method, threadName), threadName,
                        thread.getId(), method, 0, "", id,
                        parentCallId, 0L);
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
        event.primitiveValue = safe(primitiveValue);
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
        emitExecutionEvent(event);
        removeCallSite(invocationId);
    }

    public static void recordBranch(long callId, String method, int unitIndex,
                                    String expression, boolean outcome) {
        ExecutionEvent event = newExecutionEvent("BRANCH",
                firstNonBlank(method, methodForCall(callId)), callId);
        event.siteId = siteId(event.method, unitIndex);
        event.outcome = outcome;
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
        event.successorIndex = successorIndex >= 0 ? successorIndex : null;
        int caseCount = encodedCaseKeys == null
                || encodedCaseKeys.isEmpty() ? 0
                : encodedCaseKeys.split(",", -1).length;
        event.outcome = event.successorIndex == null ? null
                : successorIndex < caseCount;
        emitExecutionEvent(event);
    }

    public static void exitMethod(long callId, Object returnValue,
                                  String primitiveValue) {
        ActiveCall call = activeCall(callId);
        long resolvedCallId = call == null ? callId : call.callId;
        closeCallSites(resolvedCallId, "CALL_SITE_INCOMPLETE");
        ExecutionEvent event = newExecutionEvent("METHOD_EXIT_NORMAL",
                call == null ? "" : call.method, resolvedCallId);
        event.runtimeType = runtimeType(returnValue);
        event.objectId = identity(returnValue);
        event.primitiveValue = safe(primitiveValue);
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

    /** Removes the current lite activation without emitting an exit row. */
    public static void exitActiveMethodLite() {
        exitActiveMethodLite("CALL_SITE_INCOMPLETE");
    }

    private static void exitActiveMethodLite(String callSiteExit) {
        ActiveCall call = ACTIVE_CALLS.get().peek();
        if (call != null) {
            closeCallSites(call.callId, callSiteExit);
            removeCall(call.callId);
        }
    }

    /** Removes an exceptionally exiting lite activation without trace output. */
    public static void throwActiveMethodLite() {
        throwActiveMethodLite(null);
    }

    /** Throwable-shaped overload used by the existing catch-all instrumenter. */
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
        if (id > maxEvents) {
            return;
        }
        int receiverObjectId = identity(fieldReceiver);
        int valueObjectId = identity(valueObject);
        ActiveCall activeCall = ACTIVE_CALLS.get().peek();
        RuntimeRegionPlanner.FieldAccessEvent event =
                new RuntimeRegionPlanner.FieldAccessEvent(id, kind, method,
                        activeCall == null ? 0L : activeCall.callId,
                        unitIndex, siteId(method, unitIndex), field,
                        receiverObjectId, valueObjectId, primitiveValue);
        synchronized (LOCK) {
            writeFieldTraceLine(event);
        }
    }

    /** Records one transport endpoint without inspecting the payload. */
    public static void recordRpcEndpoint(String direction, String transport,
                                         String wireId, String endpoint) {
        if (direction == null || transport == null || wireId == null) {
            return;
        }
        initialize();
        if (contextOnlyConcolicReplay) {
            return;
        }
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) {
            return;
        }
        Thread thread = Thread.currentThread();
        ActiveCall call = ACTIVE_CALLS.get().peek();
        ActiveCallSite site = ACTIVE_CALL_SITES.get().peek();
        String method = call == null ? "" : call.method;
        RuntimeRegionPlanner.ProtocolEvent event =
                new RuntimeRegionPlanner.ProtocolEvent(id,
                        safe(direction).toUpperCase(), safe(transport),
                        safe(wireId), safe(endpoint),
                        inferProcessName(method, thread.getName()),
                        thread.getName(), thread.getId(), method,
                        call == null ? 0L : call.callId,
                        site == null ? 0L : site.invocationId,
                        site == null ? "" : site.declaredCallee);
        synchronized (LOCK) {
            writeProtocolTraceLine(event);
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
            boolean configuredContextOnly =
                    configuredContextOnlyConcolicReplay();
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

                // INITIALIZED is the release publication for every field above.
                // No recording thread can observe a partially initialized writer
                // or the JVM default value of an event limit.
                testName = configuredTestName;
                maxEvents = Integer.getInteger(
                        "causynth.trace.max.events", DEFAULT_MAX_EVENTS);
                traceWriteFailure = false;
                outputDir = configuredOutputDir;
                traceWriter = configuredWriter;
                contextOnlyConcolicReplay = false;
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
            if (outputDir != null) {
                writeFileQuietly(new File(outputDir,
                                "streaming_trace_manifest.json"),
                        CausynthJson.objectWithoutNulls(
                                "schemaVersion", 1,
                                "kind", "STREAMING_RUNTIME_TRACE",
                                "status", EVENT_COUNTER.get() <= maxEvents
                                        && !traceWriteFailure
                                        ? "CLOSED" : "INCOMPLETE"));
            }
        }
    }

    private static void aggregateStateTrace(
            File directory, File candidateGraph, File selectedSkeletons,
            File refinedGraph, File regionFile, File regionEdgeFile,
            String test, File planOutputDirectory) throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            long traceLoadStart = System.nanoTime();
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, false);
            trace.sort();
            long traceLoadMillis = elapsedMillis(traceLoadStart);
            Set<String> observedMethods = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                observedMethods.add(event.method);
            }
            long refinementStart = System.nanoTime();
            RuntimeRefinedGraphBuilder.Result refinement =
                    RuntimeRefinedGraphBuilder.refine(candidateGraph,
                            selectedSkeletons, trace.methods, trace.execution,
                            trace.fields, trace.protocol,
                            refinedGraph.toPath());
            long refinementMillis = elapsedMillis(refinementStart);
            long candidatePlanningStart = System.nanoTime();
            RuntimeSelectedRegionFinalizer.finalizeRegions(
                    refinedGraph, selectedSkeletons, regionFile,
                    regionEdgeFile,
                    observedMethods);
            long candidatePlanningMillis =
                    elapsedMillis(candidatePlanningStart);
            writeRuntimeRegionPlans(planOutputDirectory, refinedGraph,
                    regionFile, regionEdgeFile, trace);
            writeFile(new File(planOutputDirectory,
                            "runtime_refinement_manifest.json"),
                    CausynthJson.objectWithoutNulls(
                            "schemaVersion", 1,
                            "kind", "RUNTIME_REFINED_GRAPH",
                            "status", "COMPLETE",
                            "traceLoadMillis", traceLoadMillis,
                            "refinementMillis", refinementMillis,
                            "regionPlanningMillis", candidatePlanningMillis,
                            "selectedMethodCount",
                            refinement.selectedMethodCount,
                            "activationCount", refinement.activationCount,
                            "edgeCount", refinement.edgeCount,
                            "runtimeBoundEdgeCount",
                            refinement.runtimeBoundEdgeCount));
        }
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
            long traceLoadStart = System.nanoTime();
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, true);
            trace.sort();
            long traceLoadMillis = elapsedMillis(traceLoadStart);
            File skeletons = new File(outputDirectory,
                    "region_skeletons.jsonl");
            if (candidateSkeletons == null) {
                throw new IOException("skeleton aggregation requires the "
                        + "schema-3 candidate skeleton artifact");
            }
            File planningSkeletons = candidateSkeletons;

            long runtimeGraphStart = System.nanoTime();
            RuntimeRegionPlanner.Result graph =
                    RuntimeRegionPlanner.planSkeletonGraph(planningSkeletons,
                            trace.methods);
            long runtimeGraphMillis = elapsedMillis(runtimeGraphStart);
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
            StringBuilder encoded = new StringBuilder();
            encoded.append(CausynthJson.objectWithoutNulls(
                    "schemaVersion", 1,
                    "kind", "RUNTIME_REGION_GRAPH_METADATA",
                    "status", "COMPLETE",
                    "traceLoadMillis", traceLoadMillis,
                    "staticCandidateRegionPlanning",
                    "PRECOMPUTED_DURING_ANALYZE",
                    "runtimeActivationGraphMillis", runtimeGraphMillis,
                    "nodeCount", graph.runtimeInstances.size(),
                    "edgeCount", graph.runtimeGraphEdges.size()))
                    .append('\n');
            encoded.append(graph.runtimeInstancesJsonl());
            encoded.append(graph.runtimeGraphEdgesJsonl());
            writeFile(new File(outputDirectory,
                    "runtime_region_graph.jsonl"), encoded.toString());
        }
    }

    private static void writeSelectedSkeletons(
            File candidates, File output,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        Map<String, Map<String, Integer>> rootCounts = new LinkedHashMap<>();
        Map<String, Map<String, Set<String>>> methodsByRoot =
                new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances) {
            String region = String.valueOf(instance.get("regionId"));
            String root = String.valueOf(instance.get("rootMethod"));
            rootCounts.computeIfAbsent(region,
                    ignored -> new LinkedHashMap<>()).merge(root, 1,
                    Integer::sum);
            Set<String> observed = methodsByRoot.computeIfAbsent(region,
                    ignored -> new LinkedHashMap<>()).computeIfAbsent(root,
                    ignored -> new LinkedHashSet<>());
            Object methods = instance.get("observedMethods");
            if (methods instanceof Collection<?>) {
                for (Object method : (Collection<?>) methods) {
                    observed.add(String.valueOf(method));
                }
            }
        }
        File parent = output.getParentFile();
        if (parent != null) {
            Files.createDirectories(parent.toPath());
        }
        try (BufferedReader reader = skeletonReader(candidates);
             BufferedWriter writer = Files.newBufferedWriter(output.toPath(),
                     StandardCharsets.UTF_8)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                String region = string(row, "regionId");
                Map<String, Integer> counts = rootCounts.get(region);
                if (counts == null || counts.isEmpty()) {
                    continue;
                }
                String selectedRoot = "";
                int selectedCount = -1;
                for (Map.Entry<String, Integer> entry : counts.entrySet()) {
                    if (entry.getValue() > selectedCount) {
                        selectedRoot = entry.getKey();
                        selectedCount = entry.getValue();
                    }
                }
                row.addProperty("rootMethod", selectedRoot);
                JsonArray selectedMethods = new JsonArray();
                for (String method : methodsByRoot.get(region).get(
                        selectedRoot)) {
                    selectedMethods.add(method);
                }
                row.add("methods", selectedMethods);
                row.addProperty("planningMode",
                        "RUNTIME_SELECTED_ACTIVATION_SKELETON");
                writer.write(row.toString());
                writer.write('\n');
            }
        }
    }

    private static BufferedReader skeletonReader(File file)
            throws IOException {
        InputStream input = Files.newInputStream(file.toPath());
        try {
            if (file.getName().endsWith(".gz")) {
                input = new GZIPInputStream(input);
            }
            return new BufferedReader(new InputStreamReader(input,
                    StandardCharsets.UTF_8));
        } catch (IOException exception) {
            input.close();
            throw exception;
        }
    }

    private static long elapsedMillis(long startNanos) {
        return (System.nanoTime() - startNanos) / 1_000_000L;
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
        if (integer(manifest, "schemaVersion", -1) != 1
                || !"STREAMING_RUNTIME_TRACE".equals(
                string(manifest, "kind"))
                || !"CLOSED".equals(string(manifest, "status"))) {
            throw new IOException("Runtime trace is incomplete: "
                    + manifestFile);
        }
    }

    private static void clearInMemoryTrace() {
        INITIALIZED.set(false);
        EVENT_COUNTER.set(0L);
        ACTIVE_CALLS.remove();
        ACTIVE_CALL_SITES.remove();
        OBJECT_IDS.clear();
        nextObjectId = 1;
        contextOnlyConcolicReplay = false;
        traceWriteFailure = false;
        traceWriter = null;
    }

    private static TraceData loadExistingTrace(
            File file, String test, boolean skeletonOnly) throws IOException {
        if (file == null || !file.isFile()) {
            throw new IOException("Runtime trace not found: " + file);
        }
        TraceData trace = new TraceData();
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
                if (integer(row, "schemaVersion", -1) != 3) {
                    throw new IOException("Unsupported runtime trace row: "
                            + line);
                }
                String eventKind = string(row, "event");
                if ("METHOD_ENTER".equals(eventKind)) {
                    String method = string(row, "method");
                    String threadName = string(row, "threadName");
                    String process = string(row, "process");
                    if (process.isEmpty()) {
                        throw new IOException("METHOD_ENTER has no process at "
                                + file + ":" + lineNumber);
                    }
                    long seq = longInteger(row, "seq", 0L);
                    trace.methods.add(new RuntimeRegionPlanner.MethodEvent(
                            seq,
                            test,
                            process,
                            threadName,
                            longInteger(row, "tid", 0L),
                            method,
                            integer(row, "objectId", 0),
                            string(row, "receiverType"),
                            longInteger(row, "callId", seq),
                            longInteger(row, "parentCallId", 0L),
                            longInteger(row, "parentSiteId", 0L)));
                } else if (!skeletonOnly && ("FIELD_READ".equals(eventKind)
                        || "FIELD_WRITE".equals(eventKind))) {
                    String method = string(row, "method");
                    trace.fields.add(
                            new RuntimeRegionPlanner.FieldAccessEvent(
                            longInteger(row, "seq", 0L),
                            eventKind,
                            method,
                            longInteger(row, "callId", 0L),
                            integer(row, "unitIndex", -1),
                            string(row, "siteId"),
                            string(row, "field"),
                            integer(row, "fieldReceiverObjectId", 0),
                            integer(row, "valueObjectId", 0),
                            string(row, "primitiveValue")));
                } else if (!skeletonOnly && ("RPC_SEND".equals(eventKind)
                        || "RPC_RECEIVE".equals(eventKind))) {
                    trace.protocol.add(new RuntimeRegionPlanner.ProtocolEvent(
                            longInteger(row, "seq", 0L),
                            "RPC_SEND".equals(eventKind)
                                    ? "SEND" : "RECEIVE",
                            string(row, "transport"),
                            string(row, "wireId"),
                            string(row, "endpoint"),
                            string(row, "process"),
                            string(row, "threadName"),
                            longInteger(row, "tid", 0L),
                            string(row, "method"),
                            longInteger(row, "callId", 0L),
                            longInteger(row, "invocationId", 0L),
                            string(row, "declaredCallee")));
                } else if (!skeletonOnly && isExecutionEventKind(eventKind)) {
                    trace.execution.add(new RuntimeRegionPlanner.RuntimeEvent(
                            longInteger(row, "seq", 0L), eventKind,
                            string(row, "method"),
                            longInteger(row, "callId", 0L),
                            longInteger(row, "invocationId", 0L),
                            0L,
                            string(row, "siteId"),
                            string(row, "declaredCallee"),
                            integer(row, "argumentIndex", -1),
                            string(row, "runtimeType"),
                            integer(row, "objectId", 0),
                            string(row, "primitiveValue"),
                            row.has("outcome")
                                    ? bool(row, "outcome", false) : null,
                            row.has("successorIndex")
                                    ? integer(row, "successorIndex", -1)
                                    : null,
                            string(row, "branchKind"),
                            ""));
                }
            }
        }
        return trace;
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
        writeTraceRow(
                "schemaVersion", 3,
                "event", "METHOD_ENTER",
                "seq", event.seq,
                "process", event.process,
                "threadName", event.threadName,
                "tid", event.tid,
                "method", event.method,
                "objectId", event.objectId,
                "receiverType", event.receiverType,
                "callId", event.callId,
                "parentCallId", event.parentCallId,
                "parentSiteId", event.parentSiteId);
    }

    private static void writeFieldTraceLine(
            RuntimeRegionPlanner.FieldAccessEvent event) {
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
        writeTraceRow(
                "schemaVersion", 3,
                "event", "SEND".equals(event.direction)
                        ? "RPC_SEND" : "RPC_RECEIVE",
                "seq", event.seq,
                "transport", event.transport,
                "wireId", event.wireId,
                "endpoint", event.endpoint,
                "process", event.process,
                "threadName", event.threadName,
                "tid", event.tid,
                "method", event.method,
                "callId", event.callId,
                "invocationId", event.invocationId,
                "declaredCallee", event.declaredCallee);
    }

    private static void writeExecutionTraceLine(ExecutionEvent event) {
        if (event == null) return;
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
                "successorIndex", event.successorIndex);
    }

    private static void writeTraceRow(Object... fields) {
        if (traceWriter == null) return;
        try {
            traceWriter.write(CausynthJson.objectWithoutNulls(fields));
            traceWriter.newLine();
        } catch (IOException ignored) {
            traceWriteFailure = true;
        }
    }

    private static String inferProcessName(String method, String threadName) {
        String configuredPatterns = firstNonBlank(
                System.getProperty("causynth.trace.process.patterns"),
                System.getenv("CAUSYNTH_TRACE_PROCESS_PATTERNS"), "");
        if (configuredPatterns.isEmpty()) {
            return "unknown";
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
        return "unknown";
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
            File directory, File staticGraph, File regionFile,
            File regionEdgeFile, TraceData trace) throws IOException {
        RuntimeRegionPlanner.Result planned = RuntimeRegionPlanner.plan(
                regionFile,
                regionEdgeFile, staticGraph, trace.methods,
                trace.execution, trace.fields);
        writeRuntimePlanArtifacts(directory,
                planned.edgeValidationsJsonl(), planned.regionPlansJsonl(),
                planned.runtimeInstances);
    }

    private static void writeRuntimePlanArtifacts(
            File directory,
            String edgeValidations, String regionPlans) throws IOException {
        writeRuntimePlanArtifacts(directory, edgeValidations, regionPlans,
                "");
    }

    private static void writeRuntimePlanArtifacts(
            File directory,
            String edgeValidations, String regionPlans,
            String runtimeInstances) throws IOException {
        writeFile(new File(directory,
                        "runtime_region_edge_validation.jsonl"),
                edgeValidations);
        writeFile(new File(directory,
                        "concolic_region_plan.jsonl"),
                regionPlans);
        if (!runtimeInstances.isEmpty()) {
            writeFile(new File(directory,
                            "runtime_region_instances.jsonl"),
                    runtimeInstances);
        }
    }

    private static void writeRuntimePlanArtifacts(
            File directory,
            String edgeValidations, String regionPlans,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        writeFile(new File(directory,
                        "runtime_region_edge_validation.jsonl"),
                edgeValidations);
        writeFile(new File(directory,
                        "concolic_region_plan.jsonl"),
                regionPlans);
        writeJsonMapLines(new File(directory,
                "runtime_region_instances.jsonl"),
                runtimeInstances);
    }

    private static void writeJsonMapLines(
            File file, Collection<Map<String, Object>> rows)
            throws IOException {
        File parent = file.getParentFile();
        if (parent != null) {
            Files.createDirectories(parent.toPath());
        }
        try (BufferedWriter writer = Files.newBufferedWriter(file.toPath(),
                StandardCharsets.UTF_8)) {
            for (Map<String, Object> row : rows) {
                writer.write(CausynthJson.write(row));
                writer.newLine();
            }
        }
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

    }

    private static final class TraceData {
        private final List<RuntimeRegionPlanner.MethodEvent> methods =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.RuntimeEvent> execution =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.ProtocolEvent> protocol =
                new ArrayList<>();

        private void sort() {
            methods.sort((left, right) -> Long.compare(left.seq, right.seq));
            fields.sort((left, right) -> Long.compare(left.seq, right.seq));
            execution.sort((left, right) ->
                    Long.compare(left.seq, right.seq));
            protocol.sort((left, right) -> Long.compare(left.seq, right.seq));
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

}
