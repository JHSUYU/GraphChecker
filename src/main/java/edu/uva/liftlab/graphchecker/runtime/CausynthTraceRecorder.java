package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
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
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
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
import java.util.Locale;
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
    private static final ThreadLocal<Deque<ActiveCall>> ACTIVE_CALLS =
            ThreadLocal.withInitial(ArrayDeque::new);
    private static final ThreadLocal<Deque<ActiveCallSite>> ACTIVE_CALL_SITES =
            ThreadLocal.withInitial(ArrayDeque::new);
    private static final int DEFAULT_MAX_EVENTS = 200000;
    /**
     * A plain concolic replay uses the rich-trace call stacks only as exact
     * accessor-site context. It does not publish a runtime trace, so hashing
     * every packet/argument is both semantically unused and prohibitively
     * expensive on the interpreted custom JVM. Campaign discovery supplies
     * an explicit trace output directory and therefore keeps fingerprints.
     */
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
        boolean inventoryOnly = Boolean.parseBoolean(
                params.get("inventory-only"));
        boolean skeletonOnly = Boolean.parseBoolean(
                params.get("region-skeleton-only"));
        if (inventoryOnly && skeletonOnly) {
            throw new IllegalArgumentException("--inventory-only and "
                    + "--region-skeleton-only are mutually exclusive");
        }
        String configuredSkeletons = params.get("region-skeletons");
        File candidateSkeletons = configuredSkeletons == null
                || configuredSkeletons.trim().isEmpty()
                ? null : new File(configuredSkeletons.trim());
        File graph = skeletonOnly && candidateSkeletons != null ? null
                : new File(requiredArg(params, "static-graph"));
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
                aggregateSkeletonTrace(directory, graph, candidateSkeletons,
                        test, planOutputDirectory);
            } else {
                aggregateExistingTrace(directory, graph, regions, regionEdges,
                        test, planOutputDirectory, inventoryOnly);
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

    /**
     * Records the activation metadata needed by inventory planning without
     * collecting arguments, call sites, branches, or return values.
     */
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
                        thread.getId(), method, 0, runtimeType(receiver), id,
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

    /** Completes a lite container call without inspecting its return value. */
    public static void endCallLite(long invocationId) {
        initialize();
        ActiveCallSite site = activeCallSite(invocationId);
        long id = EVENT_COUNTER.incrementAndGet();
        if (id <= maxEvents && !contextOnlyConcolicReplay) {
            synchronized (LOCK) {
                writeTraceRow(
                        "schemaVersion", 2,
                        "event", "CALL_SITE_RETURN",
                        "seq", id,
                        "method", site == null ? "" : site.caller,
                        "callId", site == null ? 0L : site.ownerCallId,
                        "invocationId", invocationId,
                        "siteId", site == null ? "" : site.siteId,
                        "declaredCallee",
                        site == null ? "" : site.declaredCallee);
            }
        }
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

    /**
     * Records only the exact declared field and owning activation required by
     * the post-runtime inventory input slice.
     */
    public static void recordFieldReadLite(String field) {
        recordFieldReadLite(field, null, null);
    }

    public static void recordFieldReadLite(
            String field, Object fieldOwner, Object referenceValue) {
        recordFieldLite("FIELD_READ", field, fieldOwner, referenceValue);
    }

    /** Records a shared-state producer without inspecting its owner or value. */
    public static void recordFieldWriteLite(String field) {
        recordFieldWriteLite(field, null, null);
    }

    public static void recordFieldWriteLite(
            String field, Object fieldOwner, Object referenceValue) {
        recordFieldLite("FIELD_WRITE", field, fieldOwner, referenceValue);
    }

    private static void recordFieldLite(
            String kind, String field, Object fieldOwner,
            Object referenceValue) {
        if (field == null || field.isEmpty()) {
            return;
        }
        initialize();
        if (contextOnlyConcolicReplay) {
            return;
        }
        ActiveCall call = ACTIVE_CALLS.get().peek();
        if (call == null) {
            return;
        }
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) {
            return;
        }
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 2,
                    "event", kind,
                    "seq", id,
                    "callId", call.callId,
                    "field", field,
                    "fieldReceiverObjectId", identity(fieldOwner),
                    "fieldReceiverRuntimeType", runtimeType(fieldOwner),
                    "valueObjectId", identity(referenceValue),
                    "valueRuntimeType", runtimeType(referenceValue));
        }
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
        int receiverObjectId = fieldReceiver == null ? 0 : System.identityHashCode(fieldReceiver);
        int valueObjectId = valueObject == null ? 0 : System.identityHashCode(valueObject);
        ValueFingerprint fingerprint =
                ValueFingerprint.capture(valueObject, primitiveValue);
        ActiveCall activeCall = ACTIVE_CALLS.get().peek();
        RuntimeRegionPlanner.FieldAccessEvent event =
                new RuntimeRegionPlanner.FieldAccessEvent(id, kind, method,
                        activeCall == null ? 0L : activeCall.callId,
                        unitIndex, siteId(method, unitIndex), field,
                        receiverObjectId, valueObjectId, primitiveValue,
                        fingerprint.digest, fingerprint.complete);
        synchronized (LOCK) {
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

    private static void aggregateExistingTrace(
            File directory, File staticGraph, File regionFile,
            File regionEdgeFile, String test) throws IOException {
        aggregateExistingTrace(directory, staticGraph, regionFile,
                regionEdgeFile, test, directory, false);
    }

    private static void aggregateExistingTrace(
            File directory, File staticGraph, File regionFile,
            File regionEdgeFile, String test, File planOutputDirectory,
            boolean inventoryOnly) throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            long traceLoadStart = System.nanoTime();
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, inventoryOnly);
            trace.sort();
            long traceLoadMillis = elapsedMillis(traceLoadStart);
            Set<String> observedMethods = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                observedMethods.add(event.method);
            }
            long candidatePlanningStart = System.nanoTime();
            if (inventoryOnly) {
                RuntimeSelectedRegionFinalizer.finalizeInventory(
                        staticGraph, regionFile, regionEdgeFile,
                        observedMethods);
            } else {
                RuntimeSelectedRegionFinalizer.finalizeRegions(
                        staticGraph, regionFile, regionEdgeFile,
                        observedMethods);
            }
            long candidatePlanningMillis =
                    elapsedMillis(candidatePlanningStart);
            writeRuntimeRegionPlans(planOutputDirectory, staticGraph,
                    regionFile, regionEdgeFile, trace,
                    inventoryOnly, traceLoadMillis,
                    candidatePlanningMillis);
        }
    }

    /** Emits only static region skeletons and their concrete activation graph. */
    private static void aggregateSkeletonTrace(
            File directory, File staticGraph, File candidateSkeletons,
            String test,
            File outputDirectory)
            throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            long traceLoadStart = System.nanoTime();
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, false, true);
            trace.sort();
            long traceLoadMillis = elapsedMillis(traceLoadStart);
            File skeletons = new File(outputDirectory,
                    "region_skeletons.jsonl");
            File planningSkeletons = candidateSkeletons;
            long candidatePlanningMillis = 0L;
            if (planningSkeletons == null) {
                Set<String> observedMethods = new LinkedHashSet<>();
                for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                    observedMethods.add(event.method);
                }
                File discardedRegionEdges = Files.createTempFile(
                        "causynth-region-skeleton-edges-", ".jsonl").toFile();
                long candidatePlanningStart = System.nanoTime();
                try {
                    RuntimeSelectedRegionFinalizer.finalizeSkeletons(
                            staticGraph, skeletons, discardedRegionEdges,
                            observedMethods);
                } finally {
                    Files.deleteIfExists(discardedRegionEdges.toPath());
                }
                candidatePlanningMillis =
                        elapsedMillis(candidatePlanningStart);
                planningSkeletons = skeletons;
            }

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
            if (candidateSkeletons != null) {
                writeSelectedSkeletons(candidateSkeletons, skeletons,
                        graph.runtimeInstances);
            }
            StringBuilder encoded = new StringBuilder();
            encoded.append(CausynthJson.objectWithoutNulls(
                    "schemaVersion", 1,
                    "kind", "RUNTIME_REGION_GRAPH_METADATA",
                    "status", "COMPLETE",
                    "traceLoadMillis", traceLoadMillis,
                    "staticCandidateRegionPlanningMillis",
                    candidatePlanningMillis,
                    "staticCandidateRegionPlanning",
                    candidateSkeletons == null
                            ? "OFFLINE_FROM_STATIC_GRAPH"
                            : "PRECOMPUTED_DURING_ANALYZE",
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
        Set<String> selectedIds = new LinkedHashSet<>();
        for (Map<String, Object> instance : runtimeInstances) {
            Object memberships = instance.get("regionIds");
            if (memberships instanceof Collection<?>) {
                for (Object membership : (Collection<?>) memberships) {
                    selectedIds.add(String.valueOf(membership));
                }
            } else if (instance.containsKey("regionId")) {
                selectedIds.add(String.valueOf(instance.get("regionId")));
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
                if (selectedIds.contains(string(row, "regionId"))) {
                    writer.write(line);
                    writer.write('\n');
                }
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
        contextOnlyConcolicReplay = false;
        traceWriteFailure = false;
        traceWriter = null;
    }

    private static TraceData loadExistingTrace(
            File file, String test, boolean inventoryOnly)
            throws IOException {
        return loadExistingTrace(file, test, inventoryOnly, false);
    }

    private static TraceData loadExistingTrace(
            File file, String test, boolean inventoryOnly,
            boolean skeletonOnly) throws IOException {
        if (file == null || !file.isFile()) {
            throw new IOException("Runtime trace not found: " + file);
        }
        TraceData trace = new TraceData();
        Map<String, String> canonicalFieldNames = inventoryOnly
                ? new LinkedHashMap<String, String>()
                : Collections.<String, String>emptyMap();
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
                    if (!inventoryOnly
                            || "FIELD_READ".equals(eventKind)
                            || "FIELD_WRITE".equals(eventKind)
                            && method.contains(": void <init>(")) {
                        String field = string(row, "field");
                        if (inventoryOnly) {
                            String canonical =
                                    canonicalFieldNames.get(field);
                            if (canonical == null) {
                                canonicalFieldNames.put(field, field);
                            } else {
                                field = canonical;
                            }
                        }
                        boolean compactRead = inventoryOnly
                                && "FIELD_READ".equals(eventKind);
                        trace.fields.add(
                                new RuntimeRegionPlanner.FieldAccessEvent(
                            longInteger(row, "seq", 0L),
                            eventKind,
                            compactRead ? "" : method,
                            longInteger(row, "callId", 0L),
                            compactRead ? -1
                                    : integer(row, "unitIndex", -1),
                            compactRead ? "" : string(row, "siteId"),
                            field,
                            compactRead ? 0 : integer(row,
                                    "fieldReceiverObjectId", 0),
                            compactRead ? 0 : integer(row,
                                    "valueObjectId", 0),
                            compactRead ? "" : string(row,
                                    "primitiveValue"),
                            compactRead ? "" : string(row,
                                    "valueFingerprint"),
                            !compactRead && bool(row,
                                    "valueFingerprintComplete", false)));
                    }
                } else if (!skeletonOnly && !inventoryOnly
                        && isExecutionEventKind(eventKind)) {
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
                            string(row, "valueFingerprint"),
                            bool(row, "valueFingerprintComplete", false),
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
                "schemaVersion", 2,
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
                "schemaVersion", 2,
                "event", event.kind,
                "seq", event.seq,
                "method", event.method,
                "callId", event.callId,
                "siteId", event.siteId,
                "unitIndex", event.unitIndex,
                "field", event.field,
                "fieldReceiverObjectId", event.receiverObjectId,
                "valueObjectId", event.valueObjectId,
                "primitiveValue", event.primitiveValue,
                "valueFingerprint", event.valueFingerprint,
                "valueFingerprintComplete", event.valueFingerprintComplete);
    }

    private static void writeExecutionTraceLine(ExecutionEvent event) {
        if (event == null) return;
        writeTraceRow(
                "schemaVersion", 2,
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
                "valueFingerprint", event.valueFingerprint,
                "valueFingerprintComplete", event.valueFingerprintComplete,
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
        writeRuntimeRegionPlans(directory, staticGraph, regionFile,
                regionEdgeFile, trace, false, 0L, 0L);
    }

    private static void writeRuntimeRegionPlans(
            File directory, File staticGraph, File regionFile,
            File regionEdgeFile, TraceData trace,
            boolean inventoryOnly, long traceLoadMillis,
            long candidatePlanningMillis) throws IOException {
        RuntimeRegionPlanner.Result planned = inventoryOnly
                ? RuntimeRegionPlanner.planInventory(regionFile,
                trace.methods, trace.execution, trace.fields)
                : RuntimeRegionPlanner.plan(regionFile,
                regionEdgeFile, staticGraph, trace.methods,
                trace.execution, trace.fields);
        writeRuntimePlanArtifacts(directory,
                planned.edgeValidationsJsonl(), planned.regionPlansJsonl(),
                planned.runtimeInstances);
        if (inventoryOnly) {
            writeFile(new File(directory,
                            "runtime_region_inventory_manifest.json"),
                    CausynthJson.objectWithoutNulls(
                            "schemaVersion", 1,
                            "kind", "RUNTIME_REGION_INPUT_INVENTORY",
                            "status", "COMPLETE",
                            "phaseOrder", Arrays.asList(
                                    "STATIC_CANDIDATE_REGION_PLANNING",
                                    "RUNTIME_REGION_INSTANTIATION",
                                    "POST_RUNTIME_REGION_INPUT_SLICING"),
                            "traceLoadMillis", traceLoadMillis,
                            "staticCandidateRegionPlanningMillis",
                            candidatePlanningMillis,
                            "runtimeRegionInstantiationMillis",
                            Math.max(0L,
                                    planned.runtimeInventoryTotalNanos
                                            - planned.regionInputSlicingNanos)
                                    / 1_000_000L,
                            "postRuntimeRegionInputSlicingMillis",
                            planned.regionInputSlicingNanos / 1_000_000L,
                            "concolicPlanning", "NOT_REQUESTED",
                            "materialization", "NOT_COMPUTED",
                            "staticRegionCount",
                            planned.staticRegionCount,
                            "runtimeInstanceCount",
                            planned.runtimeInstances.size(),
                            "staticInputCandidateCount",
                            planned.staticInputCandidateCount,
                            "runtimeInputCandidateOccurrenceCount",
                            planned.runtimeInputCandidateOccurrenceCount,
                            "runtimeRegionInputCount",
                            planned.runtimeRegionInputCount,
                            "runtimePrunedInputCandidateCount",
                            planned.runtimePrunedInputCandidateCount,
                            "projectedEdgesUsedByOutputSlices",
                            "NOT_APPLICABLE_IN_INVENTORY_MODE",
                            "runtimeSymbolizedProjectedPorts", 0));
        }
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
        private String valueFingerprint = "";
        private boolean valueFingerprintComplete;
        private Boolean outcome;
        private String branchKind = "";
        private Integer successorIndex;

        private void captureValueFingerprint(Object value,
                                             String primitiveValue) {
            ValueFingerprint fingerprint = contextOnlyConcolicReplay
                    ? ValueFingerprint.disabled()
                    : ValueFingerprint.capture(value, primitiveValue);
            valueFingerprint = fingerprint.digest;
            valueFingerprintComplete = fingerprint.complete;
        }
    }

    private static final class TraceData {
        private final List<RuntimeRegionPlanner.MethodEvent> methods =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.RuntimeEvent> execution =
                new ArrayList<>();

        private void sort() {
            methods.sort((left, right) -> Long.compare(left.seq, right.seq));
            fields.sort((left, right) -> Long.compare(left.seq, right.seq));
            execution.sort((left, right) ->
                    Long.compare(left.seq, right.seq));
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
        private static final ThreadLocal<Boolean> ACTIVE =
                ThreadLocal.withInitial(() -> false);
        /*
         * These bounds protect the observed execution, not the causal slice:
         * every static edge and REGION.IN remains available. A value that
         * exceeds this budget is marked incomplete and is therefore ineligible
         * for an inferred equality. Unbounded object-graph walks can otherwise
         * hold system locks long enough to change the execution being observed.
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

        private ValueFingerprint(String digest, boolean complete) {
            this.digest = safe(digest);
            this.complete = complete;
        }

        private static ValueFingerprint disabled() {
            return new ValueFingerprint("", false);
        }

        private static ValueFingerprint capture(Object value,
                                                String primitiveValue) {
            if (ACTIVE.get()) {
                return disabled();
            }
            ACTIVE.set(true);
            try {
                return captureUnchecked(value, primitiveValue);
            } catch (Throwable failure) {
                // Runtime evidence must be observational.  In particular, a
                // shared Map/Collection may change while it is fingerprinted;
                // a ConcurrentModificationException (or any reflective
                // access failure) must never escape into the instrumented
                // execution. Incomplete fingerprints are already
                // ineligible for automatic endpoint equality.
                return new ValueFingerprint("", false);
            } finally {
                ACTIVE.remove();
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
                    state.complete);
        }

        private static void appendValue(Object value, StringBuilder out,
                                        FingerprintState state, int depth) {
            if (!state.complete) return;
            if (depth > MAX_DEPTH) {
                state.fail();
                return;
            }
            if (++state.nodes > state.nodeBudget) {
                state.fail();
                return;
            }
            if (value == null) {
                appendToken(out, state, "NULL", "");
                return;
            }
            Class<?> type = value.getClass();
            if (value instanceof Enum<?>) {
                appendToken(out, state, type.getName(),
                        ((Enum<?>) value).name());
                return;
            }
            if (value instanceof CharSequence || value instanceof Number
                    || value instanceof Boolean || value instanceof Character) {
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
                if (length > limit) state.fail();
                return;
            }
            if (value instanceof Map<?, ?>) {
                Map<?, ?> map = (Map<?, ?>) value;
                appendToken(out, state, "MAP", type.getName() + ":" + map.size());
                List<String> entries = new ArrayList<>();
                int count = 0;
                for (Map.Entry<?, ?> entry : map.entrySet()) {
                    if (count++ >= MAX_COLLECTION_ELEMENTS) {
                        state.fail();
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
                        state.fail();
                        break;
                    }
                    state.nodes += entryState.nodes;
                    state.elements += entryState.elements;
                    state.fields += entryState.fields;
                    if (state.nodes > state.nodeBudget) {
                        state.fail();
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
                        state.fail();
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
                state.fail();
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
                state.fail();
                return;
            }
            appendToken(out, state, "OBJECT", type.getName());
            List<Field> fields = instanceFields(type);
            if (fields.size() > MAX_FIELDS_PER_OBJECT) {
                state.fail();
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
                    state.fail();
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
                state.fail();
                return;
            }
            remaining -= typeBytes;
            int valueBytes = utf8LengthCapped(safeValue, remaining);
            int headerBytes = decimalLength(safeType.length())
                    + decimalLength(safeValue.length()) + 2;
            long tokenBytes = (long) headerBytes + typeBytes + valueBytes;
            if (valueBytes > remaining
                    || tokenBytes > state.byteBudget - state.bytes) {
                state.fail();
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
                fail();
                return false;
            }
            return true;
        }

        private boolean takeField() {
            if (++fields > fieldBudget) {
                fail();
                return false;
            }
            return true;
        }

        private void fail() {
            complete = false;
        }
    }

}
