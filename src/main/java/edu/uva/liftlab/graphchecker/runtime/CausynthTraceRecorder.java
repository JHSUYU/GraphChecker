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
import java.util.Collection;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.zip.GZIPInputStream;

import static edu.uva.liftlab.graphchecker.concolic.JsonFields.firstNonBlank;
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.integer;
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
                        refinedGraph, test, planOutputDirectory);
            }
        } catch (Throwable throwable) {
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
        Deque<ActiveCall> calls = ACTIVE_CALLS.get();
        ActiveCall parent = calls.peek();
        Deque<ActiveCallSite> sites = ACTIVE_CALL_SITES.get();
        ActiveCallSite parentSite = sites.peek();
        long parentCallId = parent == null ? 0L : parent.callId;
        long parentSiteId = parentSite == null ? 0L : parentSite.invocationId;
        RuntimeTraceContext.View context = parent == null
                ? RuntimeTraceContext.enterRoot(receiver)
                : RuntimeTraceContext.current();
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName,
                        threadName, tid, method, objectId,
                        runtimeType(receiver), id, parentCallId, parentSiteId,
                        context.laneId, context.spanId, context.parentSpanId,
                        context.remoteParentSpanId, context.source,
                        context.requestKey, context.requestApi);
        calls.push(new ActiveCall(id, parentSiteId, method,
                context.spanId, parent == null));
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
        RuntimeTraceContext.View context = parent == null
                ? RuntimeTraceContext.enterRoot(receiver)
                : RuntimeTraceContext.current();
        // Keep the nesting stack balanced even after the trace budget has
        // been exhausted; the silent exit hook must not pop the parent.
        calls.push(new ActiveCall(id, 0L, method, context.spanId,
                parent == null));
        if (id > maxEvents) {
            return id;
        }
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName,
                        threadName, thread.getId(), method, 0, "", id,
                        parentCallId, 0L, context.laneId, context.spanId,
                        context.parentSpanId, context.remoteParentSpanId,
                        context.source, context.requestKey,
                        context.requestApi);
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
        if (isThreadStart(declaredCallee, receiver)) {
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
        if (argumentIndex == 0 && isAsyncTaskSubmission(
                site == null ? "" : site.declaredCallee, value)) {
            RuntimeTraceContext.captureAsync(value);
        }
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

    /** Closes one exact call-site activation on its exceptional edge. */
    public static void throwCall(long invocationId) {
        closeCallSite(activeCallSite(invocationId), "CALL_SITE_THROW");
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
        if (call != null && call.rootContext) {
            RuntimeTraceContext.exitRoot(call.spanId);
        }
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
            if (call.rootContext) {
                RuntimeTraceContext.exitRoot(call.spanId);
            }
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

    /** Records one exact aaload/aastore of a reference-array element. */
    public static void recordArrayElement(String kind, String method,
                                          int unitIndex, Object array,
                                          int index, Object element) {
        if (method == null || !("ARRAY_READ".equals(kind)
                || "ARRAY_WRITE".equals(kind))) {
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
        ActiveCall activeCall = ACTIVE_CALLS.get().peek();
        RuntimeRegionPlanner.ArrayAccessEvent event =
                new RuntimeRegionPlanner.ArrayAccessEvent(id, kind, method,
                        activeCall == null ? 0L : activeCall.callId,
                        unitIndex, siteId(method, unitIndex),
                        identity(array), index, identity(element));
        synchronized (LOCK) {
            writeArrayTraceLine(event);
        }
    }

    /**
     * Switches off application RPC correlation for one run.
     *
     * <p>An ablation control, not a tuning knob. The application names an
     * exchange by calling {@link #recordRpc}; that name is the only thing
     * that says two boundary crossings are one delivery. Turning it off is
     * how a run demonstrates what the pipeline does when the correlation is
     * absent: the exchange must become a named gap rather than an edge
     * recovered from callsites and matching values.</p>
     */
    private static final String RPC_CORRELATION_PROPERTY =
            "causynth.trace.rpc.correlation";

    private static boolean rpcCorrelationEnabled() {
        String configured = firstNonBlank(
                System.getProperty(RPC_CORRELATION_PROPERTY),
                System.getenv("CAUSYNTH_TRACE_RPC_CORRELATION"));
        return configured == null || configured.trim().isEmpty()
                || !"false".equalsIgnoreCase(configured.trim());
    }

    /**
     * Records one fully stated RPC boundary/span and an optional receiver-side
     * owner.
     *
     * <p>One exchange has two halves and each half has a send and a receive,
     * so one correlation carries four legs.  The correlation names the
     * exchange and only the exchange.  The attempt separates retries and the
     * half separates request from response for the causal interaction trace;
     * neither is inferred from a direction or payload value.</p>
     */
    public static void recordRpc(String direction, String transport,
                                 String correlationId, String attemptId,
                                 String half,
                                 Object localOwner) {
        if (direction == null || transport == null
                || correlationId == null
                || !rpcCorrelationEnabled()) {
            return;
        }
        initialize();
        String normalizedAttempt = safe(attemptId).trim();
        String normalizedHalf = safe(half).trim();
        RuntimeTraceContext.View context = RuntimeTraceContext.rpc(direction,
                transport, correlationId, normalizedHalf, localOwner);
        // The same declared leg carries the live broker handles of the leaves
        // inside this message.  That transfer is the propagation itself, so
        // it happens whether or not this pass also serializes the trace.
        ConcolicRegionRuntime.observeExchangeLeg(direction, transport,
                correlationId, normalizedHalf);
        if ("SEND".equalsIgnoreCase(safe(direction))
                && "RESPONSE".equalsIgnoreCase(normalizedHalf)) {
            ConcolicRegionRuntime.completeResponseHandoff();
        }
        if (contextOnlyConcolicReplay) return;
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
                        safe(correlationId), normalizedAttempt,
                        normalizedHalf,
                        thread.getName(),
                        thread.getId(), method,
                        call == null ? 0L : call.callId,
                        site == null ? 0L : site.invocationId,
                        site == null ? "" : site.declaredCallee,
                        context.laneId, context.spanId,
                        context.parentSpanId, context.remoteParentSpanId,
                        context.source, context.requestKey,
                        context.requestApi);
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

    /** Starts an external API request without changing the application data. */
    public static long beginSourceRequest(Object sourceAnchor,
                                          String apiName) {
        initialize();
        long requestId = RuntimeTraceContext.beginRequest(sourceAnchor,
                apiName);
        writeSourceTraceLine("REQUEST_BEGIN",
                RuntimeTraceContext.currentSource(), null, requestId,
                safe(apiName), 0);
        return requestId;
    }

    public static void endSourceRequest(long requestId, String apiName) {
        SourceRef source = RuntimeTraceContext.currentSource();
        writeSourceTraceLine("REQUEST_END", source, null, requestId,
                safe(apiName), 0);
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
     * Exact currently executing instrumented call site, or {@code null}.
     *
     * <p>This is an immutable snapshot rather than the mutable thread-local
     * stack entry.  Configured-source replay uses it to bind a manual hook to
     * the static site and replay ordinal frozen in its task.  Normal return,
     * exceptional return, stale-site replacement and test reset all remove
     * the underlying entry before a later hook can observe it.</p>
     */
    public static ActiveCallSiteContext currentCallSiteContext() {
        ActiveCallSite site = ACTIVE_CALL_SITES.get().peek();
        return site == null ? null : new ActiveCallSiteContext(
                site.siteId, site.declaredCallee, site.ownerCallId,
                site.invocationId);
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

    private static boolean isThreadStart(String declaredCallee,
                                         Object receiver) {
        return receiver instanceof Thread
                && safe(declaredCallee).contains(": void start()>");
    }

    private static boolean isAsyncTaskSubmission(String declaredCallee,
                                                 Object task) {
        if (!(task instanceof Runnable) && !(task instanceof Callable)) {
            return false;
        }
        String signature = safe(declaredCallee);
        return signature.contains(" execute(")
                || signature.contains(" submit(")
                || signature.contains(" schedule(");
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

    /**
     * The trace identity this run already gave {@code value}, or 0 when the
     * trace has never recorded it.
     *
     * <p>Lookup only, deliberately: {@link #identity} assigns on miss, and a
     * caller outside the tracing path that assigned would shift every later
     * object's number and change the trace it is trying to describe. An
     * object the trace never saw has no cross-session name here, and 0 says
     * exactly that rather than inventing one.</p>
     */
    static int recordedObjectId(Object value) {
        if (value == null) {
            return 0;
        }
        synchronized (LOCK) {
            Integer existing = OBJECT_IDS.get(value);
            return existing == null ? 0 : existing;
        }
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
            File refinedGraph, String test, File planOutputDirectory)
            throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            requireClosedTrace(new File(directory,
                    "streaming_trace_manifest.json"));
            long traceLoadStart = System.nanoTime();
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, false);
            trace.sort();
            reattributeFramesToRegisteredOwners(trace);
            writeSourceEvents(planOutputDirectory, trace.sources);
            long traceLoadMillis = elapsedMillis(traceLoadStart);
            Set<String> observedMethods = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                observedMethods.add(event.method);
            }
            RuntimeRegionPlanner.Result activationGraph =
                    RuntimeRegionPlanner.planSkeletonGraph(
                            selectedSkeletons, trace.methods,
                            trace.execution, trace.protocol);
            long refinementStart = System.nanoTime();
            RuntimeRefinedGraphBuilder.Result refinement =
                    RuntimeRefinedGraphBuilder.refine(candidateGraph,
                            selectedSkeletons,
                            activationGraph.runtimeInstances,
                            trace.methods, trace.execution,
                            trace.fields, trace.arrays, trace.protocol,
                            activationGraph.occurrenceLinks,
                            refinedGraph.toPath());
            long refinementMillis = elapsedMillis(refinementStart);
            long candidatePlanningStart = System.nanoTime();
            // The refined rows returned by the builder are normalized to the
            // exact JSONL round-trip domain, so the flow index and the
            // finalizer see precisely what re-reading the artifact would
            // produce, without parsing the multi-hundred-MB file twice more.
            RuntimeRegionPlanner.RefinedFlowIndex refinedFlowIndex =
                    RuntimeRegionPlanner.buildFlowIndex(refinement.rows,
                            refinedGraph);
            RuntimeSelectedRegionFinalizer.Result closure =
                    RuntimeSelectedRegionFinalizer.finalizeRegions(
                    refinement.rows, refinedGraph, selectedSkeletons,
                    observedMethods, activationGraph.runtimeInstances,
                    branchObservations(trace.execution, trace.methods),
                    activationGraph.occurrenceLinks);
            long candidatePlanningMillis =
                    elapsedMillis(candidatePlanningStart);
            long planBindingStart = System.nanoTime();
            for (Map<String, Object> row : closure.regions) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            for (Map<String, Object> row : closure.regionEdges) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            RuntimeRegionPlanner.Result planned = writeRuntimeRegionPlans(
                    planOutputDirectory, refinedFlowIndex, closure.regions,
                    closure.regionEdges, trace,
                    activationGraph.runtimeInstances);
            long planBindingMillis = elapsedMillis(planBindingStart);
            writeCommunicationEvidence(planOutputDirectory, activationGraph,
                    planned, closure.gaps);
            writeFile(new File(planOutputDirectory,
                            "runtime_refinement_manifest.json"),
                    CausynthJson.objectWithoutNulls(
                            "schemaVersion", 1,
                            "kind", "RUNTIME_REFINED_GRAPH",
                            "status", "COMPLETE",
                            "traceLoadMillis", traceLoadMillis,
                            "refinementMillis", refinementMillis,
                            "regionPlanningMillis", candidatePlanningMillis,
                            "regionPlanBindingMillis", planBindingMillis));
        }
    }

    /**
     * Compact, lossless BRANCH rows used to bind fatal sites to activations.
     *
     * <p>Each row also carries the stable logical source current when the
     * method owning the branch was entered.  A target region attributes its
     * relation to the source of the event its selected failure branch was
     * observed on, and that event lives inside the root subtree, so the root
     * activation row cannot answer for it.</p>
     */
    private static List<Map<String, Object>> branchObservations(
            Collection<RuntimeRegionPlanner.RuntimeEvent> events,
            Collection<RuntimeRegionPlanner.MethodEvent> methods) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (events == null) return result;
        Map<Long, String> sourceKeyByCall = new LinkedHashMap<>();
        if (methods != null) {
            for (RuntimeRegionPlanner.MethodEvent method : methods) {
                sourceKeyByCall.put(method.callId, method.sourceKey);
            }
        }
        for (RuntimeRegionPlanner.RuntimeEvent event : events) {
            if (!"BRANCH".equals(event.kind) || event.outcome == null
                    || event.callId <= 0L || event.siteId.isEmpty()) {
                continue;
            }
            Map<String, Object> row = new LinkedHashMap<>();
            row.put("kind", "BRANCH");
            row.put("eventSeq", event.seq);
            row.put("method", event.method);
            row.put("callId", event.callId);
            row.put("siteId", event.siteId);
            row.put("outcome", event.outcome);
            String callSourceKey = sourceKeyByCall.get(event.callId);
            if (callSourceKey != null && !callSourceKey.isEmpty()) {
                row.put("callSourceKey", callSourceKey);
            }
            if (event.successorIndex != null) {
                row.put("successorIndex", event.successorIndex);
            }
            if (!event.branchKind.isEmpty()) {
                row.put("branchKind", event.branchKind);
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
            File skeletons = new File(outputDirectory,
                    "region_skeletons.jsonl");
            if (candidateSkeletons == null) {
                throw new IOException("skeleton aggregation requires the "
                        + "schema-3 candidate skeleton artifact");
            }
            File planningSkeletons = candidateSkeletons;

            RuntimeRegionPlanner.Result graph =
                    RuntimeRegionPlanner.planSkeletonGraph(planningSkeletons,
                            trace.methods);
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
        }
    }

    private static void writeSelectedSkeletons(
            File candidates, File output,
            Collection<Map<String, Object>> runtimeInstances)
            throws IOException {
        Map<String, String> rootByRegion = new LinkedHashMap<>();
        Map<String, Set<String>> methodsByRegion = new LinkedHashMap<>();
        Map<String, Integer> activationCounts = new LinkedHashMap<>();
        Map<String, String> selectionByRegion = new LinkedHashMap<>();
        Map<String, String> anchorByRegion = new LinkedHashMap<>();
        Map<String, Set<String>> anchorsByRegion = new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances) {
            String region = String.valueOf(instance.get("regionId"));
            String root = String.valueOf(instance.get("rootMethod"));
            String previous = rootByRegion.putIfAbsent(region, root);
            if (previous != null && !previous.equals(root)) {
                throw new IOException("one region definition resolved to "
                        + "multiple execution-context roots: " + region);
            }
            activationCounts.merge(region, 1, Integer::sum);
            String selection = String.valueOf(instance.get("selection"));
            String previousSelection = selectionByRegion.get(region);
            if (previousSelection == null
                    || RuntimeRegionPlanner.selectionRank(selection)
                    > RuntimeRegionPlanner.selectionRank(
                    previousSelection)) {
                selectionByRegion.put(region, selection);
                anchorByRegion.put(region,
                        String.valueOf(instance.get("anchorMethod")));
            }
            Set<String> runtimeAnchors = anchorsByRegion.computeIfAbsent(
                    region, ignored -> new LinkedHashSet<>());
            Object encodedAnchors = instance.get("anchorMethods");
            if (encodedAnchors instanceof Collection<?>) {
                for (Object anchor : (Collection<?>) encodedAnchors) {
                    runtimeAnchors.add(String.valueOf(anchor));
                }
            }
            Set<String> observed = methodsByRegion.computeIfAbsent(region,
                    ignored -> new LinkedHashSet<>());
            Object methods = instance.get("observedMethods");
            if (methods instanceof Collection<?>) {
                for (Object method : (Collection<?>) methods) {
                    observed.add(String.valueOf(method));
                }
            }
        }
        List<JsonObject> candidateRows = new ArrayList<>();
        Map<String, JsonObject> candidateByRegion = new LinkedHashMap<>();
        try (BufferedReader reader = skeletonReader(candidates)) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                JsonObject row = JsonParser.parseString(line)
                        .getAsJsonObject();
                candidateRows.add(row);
                candidateByRegion.put(string(row, "regionId"), row);
            }
        }

        File parent = output.getParentFile();
        if (parent != null) {
            Files.createDirectories(parent.toPath());
        }
        try (BufferedWriter writer = Files.newBufferedWriter(output.toPath(),
                     StandardCharsets.UTF_8)) {
            for (JsonObject candidate : candidateRows) {
                JsonObject row = candidate.deepCopy();
                String region = string(row, "regionId");
                String selectedRoot = rootByRegion.get(region);
                if (selectedRoot == null) {
                    continue;
                }
                if (!selectedRoot.equals(string(row, "rootMethod"))) {
                    throw new IOException("runtime changed authoritative "
                            + "region root: " + region);
                }
                Set<String> observedMethods = methodsByRegion.get(region);
                String selectedAnchor = anchorByRegion.get(region);
                if (selectedAnchor == null
                        || !observedMethods.contains(selectedAnchor)) {
                    throw new IOException("selected region anchor was not "
                            + "observed inside its activation: " + region);
                }
                for (String anchor : anchorsByRegion.get(region)) {
                    if (!observedMethods.contains(anchor)) {
                        throw new IOException("selected region admission "
                                + "anchor was not observed inside its "
                                + "activation: " + region + " " + anchor);
                    }
                }
                // One activation names exactly one static region, so its
                // method universe and demanded scope are that region's own.
                Set<String> potentialMethods = new LinkedHashSet<>();
                Set<String> demandScope = new LinkedHashSet<>();
                boolean demandScopeKnown = true;
                JsonObject source = candidateByRegion.get(region);
                if (source == null) {
                    throw new IOException("runtime activation references "
                            + "unknown static region: " + region);
                }
                for (JsonElement method
                        : source.getAsJsonArray("methods")) {
                    potentialMethods.add(method.getAsString());
                }
                JsonArray sourceScope = source.getAsJsonArray(
                        RuntimeSelectedRegionFinalizer.DEMAND_SCOPE);
                if (sourceScope == null) {
                    demandScopeKnown = false;
                } else {
                    for (JsonElement method : sourceScope) {
                        demandScope.add(method.getAsString());
                    }
                }
                if (!potentialMethods.contains(selectedRoot)
                        || !potentialMethods.contains(selectedAnchor)) {
                    throw new IOException("coalesced static region methods "
                            + "must contain runtime root and anchor: "
                            + region);
                }
                JsonArray encodedPotentialMethods = new JsonArray();
                for (String method : potentialMethods) {
                    encodedPotentialMethods.add(method);
                }
                row.add("methods", encodedPotentialMethods);
                JsonArray encodedDemandScope = new JsonArray();
                if (demandScopeKnown) {
                    for (String method : demandScope) {
                        encodedDemandScope.add(method);
                    }
                }
                row.add(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                        encodedDemandScope);
                JsonArray baselineObservedMethods = new JsonArray();
                for (String method : observedMethods) {
                    baselineObservedMethods.add(method);
                }
                row.add("baselineObservedMethods",
                        baselineObservedMethods);
                row.addProperty("selection", selectionByRegion.get(region));
                row.addProperty("anchorMethod", anchorByRegion.get(region));
                JsonArray selectedAnchors = new JsonArray();
                for (String anchor : anchorsByRegion.get(region)) {
                    selectedAnchors.add(anchor);
                }
                row.add("anchorMethods", selectedAnchors);
                row.addProperty("runtimeActivationCount",
                        activationCounts.get(region));
                row.addProperty("planningMode",
                        "RUNTIME_BOUND_AUTHORITY_SKELETON");
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

    /**
     * Applies every source registration this trace recorded to the frames of
     * the object it registered.
     *
     * <p>A frame is stamped with the ambient source when it is entered, and a
     * node starts its service threads before it declares which source owns
     * them - a DataNode's {@code BPServiceActor} runs a quarter of a million
     * events before the registration that names it.  Those frames kept the
     * driver that started the thread, which filed a whole node's activations
     * under the test driver and left a producer and its target on different
     * owners.</p>
     *
     * <p>This runs after the trace is fully re-read, which is the first
     * moment every registration is known.  It reads the durable rows, not a
     * live map: the previous attempt consulted an in-process binding that
     * {@link #clearInMemoryTrace()} had already emptied one statement
     * earlier, so it returned null for every activation and was
     * indistinguishable from a receiver that registered nothing.</p>
     *
     * <p>An identity that two registrations disagree about is left alone.
     * Re-attributing it would move frames across a lifecycle boundary the
     * frame's own stamp already answers correctly.</p>
     */
    private static void reattributeFramesToRegisteredOwners(TraceData trace) {
        Map<Integer, SourceRef> owners = new LinkedHashMap<>();
        Set<Integer> disputed = new LinkedHashSet<>();
        for (SourceTraceEvent event : trace.sources) {
            if (event.objectId <= 0 || event.source == null) continue;
            if (!"SOURCE_REGISTER".equals(event.kind)
                    && !"SOURCE_ALIAS".equals(event.kind)
                    && !"SOURCE_RESTART".equals(event.kind)) {
                continue;
            }
            SourceRef owner = "SOURCE_RESTART".equals(event.kind)
                    ? event.relatedSource : event.source;
            if (owner == null) continue;
            SourceRef previous = owners.put(event.objectId, owner);
            if (previous != null && !previous.equals(owner)) {
                disputed.add(event.objectId);
            }
        }
        for (Integer objectId : disputed) {
            owners.remove(objectId);
        }
        if (owners.isEmpty()) return;
        Map<Long, SourceRef> recordedSources = new LinkedHashMap<>();
        Map<Long, SourceRef> registeredContexts = new LinkedHashMap<>();
        for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
            SourceRef recorded = event.source;
            SourceRef owner = owners.get(event.objectId);
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
                event.reattribute(owner);
                registeredContexts.put(event.callId, owner);
            }
            recordedSources.put(event.callId, recorded);
        }
    }

    /**
     * Test seam for load-time re-attribution, run as the planning path runs
     * it: clear, re-read the durable trace, sort, re-attribute.
     *
     * <p>The sequence is the point.  A test that registers a source and looks
     * it up in the same live session validates a path whose production
     * precondition is impossible - the aggregation path clears the in-memory
     * state one statement before it reads the trace, so any binding that
     * lives only in memory is gone by the time it is consulted.  That is how
     * the previous attempt passed its tests and never once matched in a
     * campaign.</p>
     */
    static List<RuntimeRegionPlanner.MethodEvent> reattributedFramesForTests(
            File traceFile, String test) throws IOException {
        synchronized (LOCK) {
            clearInMemoryTrace();
            TraceData trace = loadExistingTrace(traceFile, test, false);
            trace.sort();
            reattributeFramesToRegisteredOwners(trace);
            return trace.methods;
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

    /**
     * Number of worker threads used by offline trace aggregation parsing.
     * Aggregation is a batch job; the default deliberately leaves cores for
     * a concurrently running workload VM.
     */
    private static int aggregationThreads() {
        int configured = Integer.getInteger(
                "causynth.aggregate.threads", 0);
        if (configured > 0) {
            return Math.min(configured, 32);
        }
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
            trace.arrays.addAll(part.arrays);
            trace.execution.addAll(part.execution);
            trace.protocol.addAll(part.protocol);
            trace.sources.addAll(part.sources);
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
                    row.longValue("parentSpanId", 0L),
                    row.longValue("remoteParentSpanId", 0L),
                    sourceRef(row), row.stringValue("requestKey"),
                    row.stringValue("requestApi")));
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
        } else if (!skeletonOnly && ("ARRAY_READ".equals(eventKind)
                || "ARRAY_WRITE".equals(eventKind))) {
            trace.arrays.add(new RuntimeRegionPlanner.ArrayAccessEvent(
                    row.longValue("seq", 0L),
                    eventKind,
                    row.stringValue("method"),
                    row.longValue("callId", 0L),
                    row.intValue("unitIndex", -1),
                    row.stringValue("siteId"),
                    row.intValue("arrayObjectId", 0),
                    row.intValue("arrayIndex", -1),
                    row.intValue("elementObjectId", 0)));
        } else if (!skeletonOnly && ("RPC_SEND".equals(eventKind)
                || "RPC_RECEIVE".equals(eventKind))) {
            trace.protocol.add(new RuntimeRegionPlanner.ProtocolEvent(
                    row.longValue("seq", 0L),
                    "RPC_SEND".equals(eventKind) ? "SEND" : "RECEIVE",
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
                    row.longValue("parentSpanId", 0L),
                    row.longValue("remoteParentSpanId", 0L),
                    sourceRef(row), row.stringValue("requestKey"),
                    row.stringValue("requestApi")));
        } else if (PROTOCOL_NOTE_EVENT.equals(eventKind)) {
            // Recognised, and deliberately not a protocol event.  The row
            // records that an application named a gap or a lifecycle note
            // about an exchange; it is not a leg of it, so it enters neither
            // the delivery ledger nor the send/receive pairing.  Dropping it
            // here is the refusal, not an oversight: nothing downstream may
            // count it as a crossing.
            return;
        } else if ("SOURCE_REGISTER".equals(eventKind)
                || "SOURCE_ALIAS".equals(eventKind)
                || "SOURCE_RESTART".equals(eventKind)
                || "REQUEST_BEGIN".equals(eventKind)
                || "REQUEST_END".equals(eventKind)) {
            trace.sources.add(new SourceTraceEvent(
                    row.longValue("seq", 0L), eventKind,
                    sourceRef(row), relatedSourceRef(row),
                    row.longValue("requestId", 0L),
                    row.stringValue("requestKey"),
                    row.stringValue("apiName"),
                    row.stringValue("aliasClass"),
                    row.intValue("objectId", 0),
                    row.longValue("laneId", 0L),
                    row.longValue("spanId", 0L)));
        } else if (!skeletonOnly && isExecutionEventKind(eventKind)) {
            trace.execution.add(new RuntimeRegionPlanner.RuntimeEvent(
                    row.longValue("seq", 0L), eventKind,
                    row.stringValue("method"),
                    row.longValue("callId", 0L),
                    row.longValue("invocationId", 0L),
                    0L,
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
                    ""));
        }
    }

    static void parseTraceLineForTests(String line) throws IOException {
        parseTraceLine(new TraceData(), line, 1,
                new File("runtime-trace-test.jsonl"), "test", false,
                new ConcurrentHashMap<String, String>());
    }

    /** Reads whole trace rows exactly as aggregation reads them. */
    static TraceData parseTraceLinesForTests(List<String> lines)
            throws IOException {
        TraceData trace = new TraceData();
        int lineNumber = 1;
        for (String line : lines) {
            parseTraceLine(trace, line, lineNumber++,
                    new File("runtime-trace-test.jsonl"), "test", false,
                    new ConcurrentHashMap<String, String>());
        }
        trace.sort();
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
                "parentSpanId", event.parentSpanId,
                "remoteParentSpanId", event.remoteParentSpanId,
                "sourceKind", sourceKind(event.source),
                "sourceRole", sourceRole(event.source),
                "sourceId", sourceId(event.source),
                "sourceEpoch", sourceEpoch(event.source),
                "sourceKey", sourceKey(event.source),
                "requestKey", event.requestKey,
                "requestApi", event.requestApi);
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

    private static void writeArrayTraceLine(
            RuntimeRegionPlanner.ArrayAccessEvent event) {
        writeTraceRow(
                "schemaVersion", 3,
                "event", event.kind,
                "seq", event.seq,
                "method", event.method,
                "callId", event.callId,
                "siteId", event.siteId,
                "unitIndex", event.unitIndex,
                "arrayObjectId", event.arrayObjectId,
                "arrayIndex", event.index,
                "elementObjectId", event.elementObjectId);
    }

    /**
     * The row kind one recorded protocol leg is written under.
     *
     * <p>A boundary states {@code SEND} or {@code RECEIVE} and is a delivery.
     * Everything else an application records on this hook - a named handoff
     * gap, an exchange lifecycle note - states a direction that is
     * deliberately neither, precisely so it cannot be read as a boundary of
     * the exchange it is about.  Writing anything that is not a send as a
     * receive threw that statement away and put a non-delivery into the
     * delivery stream under a delivery's own name; only the annotation these
     * rows carry in their correlation kept them from being paired with a
     * real one.  A row that is not a boundary now says so in its kind.</p>
     */
    static final String PROTOCOL_NOTE_EVENT = "RPC_NOTE";

    static String protocolEventKind(String direction) {
        if ("SEND".equals(direction)) return "RPC_SEND";
        if ("RECEIVE".equals(direction)) return "RPC_RECEIVE";
        return PROTOCOL_NOTE_EVENT;
    }

    private static void writeProtocolTraceLine(
            RuntimeRegionPlanner.ProtocolEvent event) {
        String kind = protocolEventKind(event.direction);
        writeTraceRow(
                "schemaVersion", 3,
                "event", kind,
                // The stated direction of a non-boundary row, kept as the
                // application named it: a handoff gap and a lifecycle note
                // are two different notes and must not merge into one kind.
                "noteKind", PROTOCOL_NOTE_EVENT.equals(kind)
                        ? event.direction : null,
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
                "parentSpanId", event.parentSpanId,
                "remoteParentSpanId", event.remoteParentSpanId,
                "sourceKind", sourceKind(event.source),
                "sourceRole", sourceRole(event.source),
                "sourceId", sourceId(event.source),
                "sourceEpoch", sourceEpoch(event.source),
                "sourceKey", sourceKey(event.source),
                "requestKey", event.requestKey,
                "requestApi", event.requestApi);
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
                    // activations of the object it names.  Without it the
                    // reloaded trace holds only a class name, two DataNodes'
                    // service objects are byte-identical rows, and an
                    // activation entered before its registration can never be
                    // attributed to the receiver that later claimed it.
                    "objectId", objectId <= 0 ? null : objectId,
                    event.startsWith("REQUEST_") ? "apiName" : "aliasClass",
                    detail,
                    "laneId", context.laneId,
                    "spanId", context.spanId);
        }
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
    private static RuntimeRegionPlanner.Result writeRuntimeRegionPlans(
            File directory, RuntimeRegionPlanner.RefinedFlowIndex flowIndex,
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges, TraceData trace,
            Collection<Map<String, Object>> runtimeSeeds) throws IOException {
        RuntimeRegionPlanner.Result planned = RuntimeRegionPlanner.plan(
                regions, regionEdges, flowIndex,
                "runtime region closure", "runtime region edge closure",
                runtimeSeeds, trace.methods,
                trace.execution, trace.fields, trace.protocol);
        writeFile(new File(directory, "concolic_region_plan.jsonl"),
                planned.runtimePlanJsonl());
        return planned;
    }

    /**
     * Publishes the runtime half of README Step 1 as its own artifacts.
     *
     * <p>{@code runtime_occurrence_links.jsonl} carries recorded-exchange and
     * shared-location links between independent coarse occurrences, and
     * {@code communication_runtime_gaps.jsonl} carries every place the
     * runtime could not stamp an occurrence, an outcome, an exchange or a
     * source.
     * Both are separate files so the canonical plan artifact keeps its
     * existing three sections.</p>
     */
    @SafeVarargs
    private static void writeCommunicationEvidence(
            File directory, RuntimeRegionPlanner.Result activationGraph,
            RuntimeRegionPlanner.Result plannedGraph,
            List<Map<String, Object>>... stages)
            throws IOException {
        List<Map<String, Object>> gaps = new ArrayList<>(
                activationGraph.gaps);
        gaps.addAll(plannedGraph.gaps);
        for (List<Map<String, Object>> stage : stages) {
            if (stage != null) gaps.addAll(stage);
        }
        List<Map<String, Object>> links = new ArrayList<>(
                activationGraph.occurrenceLinks);
        // Shared-location touch/admission links are known only after the
        // target closure has enumerated its carriers.  The former call wrote
        // only the pre-finalization activation links and silently discarded
        // these final-plan evidence rows.
        links.addAll(plannedGraph.occurrenceLinks);
        writeFile(new File(directory, "runtime_occurrence_links.jsonl"),
                jsonlOf(links));
        writeFile(new File(directory, "communication_runtime_gaps.jsonl"),
                jsonlOf(gaps));
    }

    private static String jsonlOf(List<Map<String, Object>> rows) {
        StringBuilder encoded = new StringBuilder();
        for (Map<String, Object> row : rows) {
            encoded.append(CausynthJson.write(row)).append('\n');
        }
        return encoded.toString();
    }

    private static void writeSourceEvents(File directory,
                                          List<SourceTraceEvent> events)
            throws IOException {
        StringBuilder encoded = new StringBuilder();
        for (SourceTraceEvent event : events) {
            encoded.append(CausynthJson.objectWithoutNulls(
                    "schemaVersion", 1,
                    "kind", event.kind,
                    "seq", event.seq,
                    "sourceKind", sourceKind(event.source),
                    "sourceRole", sourceRole(event.source),
                    "sourceId", sourceId(event.source),
                    "sourceEpoch", sourceEpoch(event.source),
                    "sourceKey", sourceKey(event.source),
                    "relatedSourceKind", sourceKind(event.relatedSource),
                    "relatedSourceRole", sourceRole(event.relatedSource),
                    "relatedSourceId", sourceId(event.relatedSource),
                    "relatedSourceEpoch", sourceEpoch(event.relatedSource),
                    "relatedSourceKey", sourceKey(event.relatedSource),
                    "requestId", event.requestId <= 0L
                            ? null : event.requestId,
                    "requestKey", event.requestKey,
                    "apiName", event.apiName,
                    "aliasClass", event.aliasClass,
                    "laneId", event.laneId,
                    "spanId", event.spanId)).append('\n');
        }
        writeFile(new File(directory, "causal_source_events.jsonl"),
                encoded.toString());
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

    static final class TraceData {
        final List<RuntimeRegionPlanner.MethodEvent> methods =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.ArrayAccessEvent> arrays =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.RuntimeEvent> execution =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.ProtocolEvent> protocol =
                new ArrayList<>();
        final List<SourceTraceEvent> sources = new ArrayList<>();

        private void sort() {
            methods.sort((left, right) -> Long.compare(left.seq, right.seq));
            fields.sort((left, right) -> Long.compare(left.seq, right.seq));
            arrays.sort((left, right) -> Long.compare(left.seq, right.seq));
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
        private final long requestId;
        private final String requestKey;
        private final String apiName;
        private final String aliasClass;
        /** Recorded identity of the object this row registered, or 0. */
        private final int objectId;
        private final long laneId;
        private final long spanId;

        private SourceTraceEvent(long seq, String kind, SourceRef source,
                                 SourceRef relatedSource, long requestId,
                                 String requestKey, String apiName,
                                 String aliasClass, int objectId,
                                 long laneId, long spanId) {
            this.objectId = objectId;
            this.seq = seq;
            this.kind = safe(kind);
            this.source = source;
            this.relatedSource = relatedSource;
            this.requestId = requestId;
            this.requestKey = safe(requestKey);
            this.apiName = safe(apiName);
            this.aliasClass = safe(aliasClass);
            this.laneId = laneId;
            this.spanId = spanId;
        }
    }

    private static final class ActiveCall {
        private final long callId;
        private final long parentSiteId;
        private final String method;
        private final long spanId;
        private final boolean rootContext;

        private ActiveCall(long callId, long parentSiteId, String method,
                           long spanId, boolean rootContext) {
            this.callId = callId;
            this.parentSiteId = parentSiteId;
            this.method = safe(method);
            this.spanId = spanId;
            this.rootContext = rootContext;
        }
    }

    /**
     * Strict scanner for one flat JSON trace row: an object whose values are
     * only strings, numbers, booleans, or null.  Any row using structure the
     * scanner does not model exactly yields {@code null} and the caller
     * falls back to the reference Gson parser, so acceptance and diagnostics
     * are unchanged; this class only removes tree-parse overhead from the
     * hot, well-formed path.  Accessors replicate the forgiving semantics of
     * {@code JsonFields} over a Gson tree.
     */
    private static final class FlatJsonRow {
        private final String[] keys;
        private final Object[] values;
        private final int size;

        private FlatJsonRow(String[] keys, Object[] values, int size) {
            this.keys = keys;
            this.values = values;
            this.size = size;
        }

        private static FlatJsonRow parse(
                String line, ConcurrentHashMap<String, String> pool) {
            int length = line.length();
            int cursor = skipWhitespace(line, 0);
            if (cursor >= length || line.charAt(cursor) != '{') {
                return null;
            }
            cursor++;
            String[] keys = new String[24];
            Object[] values = new Object[24];
            int size = 0;
            cursor = skipWhitespace(line, cursor);
            if (cursor < length && line.charAt(cursor) == '}') {
                cursor = skipWhitespace(line, cursor + 1);
                return cursor == length
                        ? new FlatJsonRow(keys, values, 0) : null;
            }
            StringBuilder scratch = new StringBuilder(64);
            while (true) {
                cursor = skipWhitespace(line, cursor);
                if (cursor >= length || line.charAt(cursor) != '"') {
                    return null;
                }
                scratch.setLength(0);
                cursor = scanString(line, cursor + 1, scratch);
                if (cursor < 0) {
                    return null;
                }
                String key = intern(pool, scratch.toString());
                cursor = skipWhitespace(line, cursor);
                if (cursor >= length || line.charAt(cursor) != ':') {
                    return null;
                }
                cursor = skipWhitespace(line, cursor + 1);
                if (cursor >= length) {
                    return null;
                }
                Object value;
                char first = line.charAt(cursor);
                if (first == '"') {
                    scratch.setLength(0);
                    cursor = scanString(line, cursor + 1, scratch);
                    if (cursor < 0) {
                        return null;
                    }
                    value = intern(pool, scratch.toString());
                } else if (first == 't') {
                    if (!line.startsWith("true", cursor)) {
                        return null;
                    }
                    cursor += 4;
                    value = Boolean.TRUE;
                } else if (first == 'f') {
                    if (!line.startsWith("false", cursor)) {
                        return null;
                    }
                    cursor += 5;
                    value = Boolean.FALSE;
                } else if (first == 'n') {
                    if (!line.startsWith("null", cursor)) {
                        return null;
                    }
                    cursor += 4;
                    value = null;
                } else if (first == '-' || first >= '0' && first <= '9') {
                    int start = cursor;
                    cursor++;
                    boolean floating = false;
                    while (cursor < length) {
                        char digit = line.charAt(cursor);
                        if (digit >= '0' && digit <= '9') {
                            cursor++;
                        } else if (digit == '.' || digit == 'e'
                                || digit == 'E' || digit == '+'
                                || digit == '-') {
                            floating = true;
                            cursor++;
                        } else {
                            break;
                        }
                    }
                    String token = line.substring(start, cursor);
                    try {
                        value = floating ? (Object) Double.valueOf(token)
                                : (Object) Long.valueOf(token);
                    } catch (NumberFormatException malformed) {
                        return null;
                    }
                } else {
                    return null;
                }
                if (size == keys.length) {
                    String[] grownKeys = new String[size * 2];
                    Object[] grownValues = new Object[size * 2];
                    System.arraycopy(keys, 0, grownKeys, 0, size);
                    System.arraycopy(values, 0, grownValues, 0, size);
                    keys = grownKeys;
                    values = grownValues;
                }
                keys[size] = key;
                values[size] = value;
                size++;
                cursor = skipWhitespace(line, cursor);
                if (cursor >= length) {
                    return null;
                }
                char separator = line.charAt(cursor);
                if (separator == ',') {
                    cursor++;
                    continue;
                }
                if (separator == '}') {
                    cursor = skipWhitespace(line, cursor + 1);
                    return cursor == length
                            ? new FlatJsonRow(keys, values, size) : null;
                }
                return null;
            }
        }

        /** Escape-aware string scan; returns -1 on malformed input. */
        private static int scanString(String line, int cursor,
                                      StringBuilder target) {
            int length = line.length();
            while (cursor < length) {
                char value = line.charAt(cursor);
                if (value == '"') {
                    return cursor + 1;
                }
                if (value == '\\') {
                    cursor++;
                    if (cursor >= length) {
                        return -1;
                    }
                    char escape = line.charAt(cursor);
                    switch (escape) {
                        case '"': target.append('"'); break;
                        case '\\': target.append('\\'); break;
                        case '/': target.append('/'); break;
                        case 'b': target.append('\b'); break;
                        case 'f': target.append('\f'); break;
                        case 'n': target.append('\n'); break;
                        case 'r': target.append('\r'); break;
                        case 't': target.append('\t'); break;
                        case 'u':
                            if (cursor + 4 >= length) {
                                return -1;
                            }
                            try {
                                target.append((char) Integer.parseInt(
                                        line.substring(cursor + 1,
                                                cursor + 5), 16));
                            } catch (NumberFormatException malformed) {
                                return -1;
                            }
                            cursor += 4;
                            break;
                        default:
                            return -1;
                    }
                    cursor++;
                    continue;
                }
                if (value < 0x20) {
                    return -1;
                }
                target.append(value);
                cursor++;
            }
            return -1;
        }

        private static int skipWhitespace(String line, int cursor) {
            int length = line.length();
            while (cursor < length) {
                char value = line.charAt(cursor);
                if (value != ' ' && value != '\t' && value != '\r'
                        && value != '\n') {
                    break;
                }
                cursor++;
            }
            return cursor;
        }

        private static String intern(ConcurrentHashMap<String, String> pool,
                                     String value) {
            String existing = pool.putIfAbsent(value, value);
            return existing != null ? existing : value;
        }

        private Object find(String key) {
            // Later duplicate keys win, matching JsonObject.add overwrite.
            for (int index = size - 1; index >= 0; index--) {
                if (keys[index].equals(key)) {
                    return values[index];
                }
            }
            return MISSING;
        }

        private static final Object MISSING = new Object();

        private boolean has(String key) {
            return find(key) != MISSING;
        }

        private String stringValue(String key) {
            Object value = find(key);
            if (value == MISSING || value == null) {
                return "";
            }
            return String.valueOf(value);
        }

        private long longValue(String key, long fallback) {
            Object value = find(key);
            if (value == MISSING || value == null) {
                return fallback;
            }
            if (value instanceof Long) {
                return (Long) value;
            }
            if (value instanceof Double) {
                return (long) (double) (Double) value;
            }
            if (value instanceof String) {
                try {
                    return Long.parseLong((String) value);
                } catch (NumberFormatException malformed) {
                    return fallback;
                }
            }
            return fallback;
        }

        private int intValue(String key, int fallback) {
            Object value = find(key);
            if (value == MISSING || value == null) {
                return fallback;
            }
            if (value instanceof Long) {
                return (int) (long) (Long) value;
            }
            if (value instanceof Double) {
                return (int) (double) (Double) value;
            }
            if (value instanceof String) {
                try {
                    return Integer.parseInt((String) value);
                } catch (NumberFormatException malformed) {
                    return fallback;
                }
            }
            return fallback;
        }

        private boolean booleanValue(String key, boolean fallback) {
            Object value = find(key);
            if (value == MISSING || value == null) {
                return fallback;
            }
            if (value instanceof Boolean) {
                return (Boolean) value;
            }
            // JsonPrimitive.getAsBoolean parses any non-boolean primitive
            // with Boolean.parseBoolean.
            return Boolean.parseBoolean(String.valueOf(value));
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

    /** Immutable public view of one exact active call-site invocation. */
    public static final class ActiveCallSiteContext {
        private final String siteId;
        private final String declaredCallee;
        private final long ownerCallId;
        private final long invocationId;

        private ActiveCallSiteContext(String siteId, String declaredCallee,
                                      long ownerCallId, long invocationId) {
            this.siteId = safe(siteId);
            this.declaredCallee = safe(declaredCallee);
            this.ownerCallId = ownerCallId;
            this.invocationId = invocationId;
        }

        public String siteId() { return siteId; }

        public String declaredCallee() { return declaredCallee; }

        public long ownerCallId() { return ownerCallId; }

        public long invocationId() { return invocationId; }
    }

}
