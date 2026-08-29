package edu.uva.liftlab.graphchecker.runtime;

import edu.uva.liftlab.graphchecker.causynth.MapFields;
import com.google.gson.JsonElement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.CommunicationCatalogContract;
import edu.uva.liftlab.graphchecker.contract.ConfiguredSourcePhaseContract;
import edu.uva.liftlab.graphchecker.contract.StaticSymbolicSourceDeclaration;
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
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
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
import static edu.uva.liftlab.graphchecker.concolic.JsonFields.objectWithoutNulls;
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

    /** The source-hook declarations a minted client entry may only carry
     *  when every holder of its endpoint declared exactly the same ones. */
    private static final String[] SHARED_SOURCE_DECLARATION_FIELDS = {
            StaticSymbolicSourceDeclaration.FIELD,
            ConfiguredSourcePhaseContract.DECLARATION_FIELD,
            ConfiguredSourcePhaseContract.TRACE_METHODS_FIELD};

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
                        context.receiverAttributed,
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
                        context.source, context.receiverAttributed,
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
        event.siteId = siteId(event.method, unitIndex);
        event.declaredCallee = MapFields.safe(declaredCallee);
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
        event.primitiveValue = MapFields.safe(primitiveValue);
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
        event.branchKind = MapFields.safe(branchKind);
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
        event.primitiveValue = MapFields.safe(primitiveValue);
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
     * Records one fully stated RPC boundary/span and an optional receiver-side
     * owner.
     */
    public static void recordRpc(String direction, String transport,
                                 String correlationId, String attemptId,
                                 String half,
                                 Object localOwner) {
        if (direction == null || transport == null
                || correlationId == null) {
            return;
        }
        initialize();
        String normalizedAttempt = MapFields.safe(attemptId).trim();
        String normalizedHalf = MapFields.safe(half).trim();
        RuntimeTraceContext.View context = RuntimeTraceContext.rpc(direction,
                transport, correlationId, normalizedHalf, localOwner);
        // The same declared leg carries the live broker handles of the leaves
        // inside this message.
        ConcolicRegionRuntime.observeExchangeLeg(direction, transport,
                correlationId, normalizedHalf);
        if ("SEND".equalsIgnoreCase(MapFields.safe(direction))
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
                        MapFields.safe(direction).toUpperCase(), MapFields.safe(transport),
                        MapFields.safe(correlationId), normalizedAttempt,
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
        if (id > maxEvents) {
            return new ExecutionEvent();
        }
        ExecutionEvent event = new ExecutionEvent();
        event.id = id;
        event.kind = MapFields.safe(kind);
        event.method = MapFields.safe(method);
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
        String expectedSite = siteId(callerMethod, callerUnitIndex);
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

    private static boolean isThreadStart(String declaredCallee,
                                         Object receiver) {
        return receiver instanceof Thread
                && MapFields.safe(declaredCallee).contains(": void start()>");
    }

    private static boolean isAsyncTaskSubmission(String declaredCallee,
                                                 Object task) {
        if (!(task instanceof Runnable) && !(task instanceof Callable)) {
            return false;
        }
        String signature = MapFields.safe(declaredCallee);
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
        return MapFields.safe(method) + "#u" + unitIndex;
    }

    /**
     * The trace identity this run already gave {@code value}, or 0 when the
     * trace has never recorded it.
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
                    // accessor invocation.
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

                // INITIALIZED is the release publication for every field
                // above.
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
            TraceData trace = loadExistingTrace(new File(directory,
                    "runtime_trace.jsonl"), test, false);
            trace.sort();
            reattributeFramesToRegisteredOwners(trace);
            Set<String> observedMethods = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                observedMethods.add(event.method);
            }
            RuntimeRegionPlanner.Result activationGraph =
                    RuntimeRegionPlanner.planSkeletonGraph(
                            selectedSkeletons, trace.methods,
                            trace.execution, trace.protocol);
            RuntimeRefinedGraphBuilder.Result refinement =
                    RuntimeRefinedGraphBuilder.refine(candidateGraph,
                            selectedSkeletons,
                            activationGraph.runtimeInstances,
                            trace.methods, trace.execution,
                            trace.fields,
                            refinedGraph.toPath());
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
            for (Map<String, Object> row : closure.regions) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            for (Map<String, Object> row : closure.regionEdges) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            writeRuntimeRegionPlans(planOutputDirectory, refinedFlowIndex,
                    closure.regions, closure.regionEdges, trace,
                    activationGraph.runtimeInstances);
        }
    }

    /**
     * Compact, lossless BRANCH rows used to bind fatal sites to activations.
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
                    graph.runtimeInstances, trace.methods,
                    trace.execution, trace.protocol);
        }
    }

    private static void writeSelectedSkeletons(
            File candidates, File output,
            Collection<Map<String, Object>> runtimeInstances,
            List<RuntimeRegionPlanner.MethodEvent> methodEvents,
            List<RuntimeRegionPlanner.RuntimeEvent> executionEvents,
            List<RuntimeRegionPlanner.ProtocolEvent> protocolEvents)
            throws IOException {
        Map<String, String> rootByRegion = new LinkedHashMap<>();
        Map<String, Set<String>> methodsByRegion = new LinkedHashMap<>();
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
                writer.write(row.toString());
                writer.write('\n');
            }
            // A communication client half whose every holder this run
            // dropped leaves the exchange with no modelled peer; the one
            // region that stands for it is minted here, from the exact SEND
            // and caller frame the run recorded, never from a holder's root.
            for (JsonObject minted : mintUncoveredClientEntryRegions(
                    candidateRows, rootByRegion.keySet(),
                    rootByRegion.values(), methodEvents,
                    executionEvents, protocolEvents)) {
                writer.write(minted.toString());
                writer.write('\n');
            }
        }
    }


    /**
     * Mints one region for a communication client half whose every static
     * holder a run dropped.
     *
     * <p>Static planning can give an execution-context authority only to a
     * main, a thread or task entry, and a protocol server stub.  A client
     * call site has none of its own, so it can only ride inside whichever
     * declared roots statically reach it.  A workload that drives the
     * component as a library never enters those roots, every holder is
     * dropped, and the client half of the exchange leaves no occurrence at
     * all -- the server records an activation with no modelled peer.  This
     * mints the missing root from the exact request SEND and the caller frame
     * the run itself recorded.</p>
     *
     * <p>It fires only when no holder was selected, so a run that entered any
     * declared root mints nothing and this is inert wherever those roots run.
     * The interchangeable holders are never tie-broken: the identity comes
     * from the call site, its exchange and the demand slice they all share,
     * and every ambiguity or missing evidence refuses instead of guessing.
     * </p>
     */
    private static List<JsonObject> mintUncoveredClientEntryRegions(
            List<JsonObject> candidates, Set<String> selectedRegions,
            Collection<String> selectedRoots,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> execution,
            List<RuntimeRegionPlanner.ProtocolEvent> protocol) {
        List<JsonObject> minted = new ArrayList<>();
        if (methods == null || methods.isEmpty()
                || execution == null || execution.isEmpty()
                || protocol == null || protocol.isEmpty()) {
            return minted;
        }
        Map<String, List<JsonObject>> holders = new LinkedHashMap<>();
        Set<String> claimedRegions = new LinkedHashSet<>();
        for (JsonObject candidate : candidates) {
            claimedRegions.add(string(candidate, "regionId"));
            for (String endpoint : clientEndpointKeys(candidate)) {
                holders.computeIfAbsent(endpoint,
                        ignored -> new ArrayList<JsonObject>())
                        .add(candidate);
            }
        }
        Set<String> claimedRoots = new LinkedHashSet<>(selectedRoots);
        List<String> endpoints = new ArrayList<>(holders.keySet());
        Collections.sort(endpoints);
        ObservedFrames frames = null;
        for (String endpoint : endpoints) {
            List<JsonObject> group = holders.get(endpoint);
            boolean covered = false;
            for (JsonObject holder : group) {
                covered = covered || selectedRegions.contains(
                        string(holder, "regionId"));
            }
            if (covered) {
                continue;
            }
            if (frames == null) {
                frames = new ObservedFrames(methods);
            }
            JsonObject row = mintClientEntryRegion(endpoint, group, frames,
                    execution, protocol, claimedRegions, claimedRoots);
            if (row != null) {
                minted.add(row);
                claimedRegions.add(string(row, "regionId"));
                claimedRoots.add(string(row, "rootMethod"));
            }
        }
        return minted;
    }

    /**
     * Test seam for the mint rule, run exactly as the selection stage runs
     * it: the candidate rows, the regions and roots the run already selected,
     * and the frames it entered.
     */
    static List<JsonObject> mintedClientEntryRegionsForTests(
            List<JsonObject> candidates, Set<String> selectedRegions,
            Collection<String> selectedRoots,
            List<RuntimeRegionPlanner.MethodEvent> methods,
            List<RuntimeRegionPlanner.RuntimeEvent> execution,
            List<RuntimeRegionPlanner.ProtocolEvent> protocol) {
        return mintUncoveredClientEntryRegions(candidates, selectedRegions,
                selectedRoots, methods, execution, protocol);
    }

    /** The {@code callSiteId + exchange} of every client half a candidate
     *  region declares, in one deterministic order. */
    private static List<String> clientEndpointKeys(JsonObject candidate) {
        Set<String> keys = new LinkedHashSet<>();
        for (JsonObject port : portsOf(candidate)) {
            if (!RuntimeSelectedRegionFinalizer.PORT_ROLE_CLIENT.equals(
                    string(port, RuntimeSelectedRegionFinalizer.PORT_ROLE))) {
                continue;
            }
            String site = string(port,
                    CommunicationCatalogContract.CALL_SITE_ID);
            String exchange = string(port,
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY);
            if (!site.isEmpty() && !exchange.isEmpty()) {
                keys.add(site + '\n' + exchange);
            }
        }
        List<String> ordered = new ArrayList<>(keys);
        Collections.sort(ordered);
        return ordered;
    }

    private static List<JsonObject> portsOf(JsonObject region) {
        List<JsonObject> ports = new ArrayList<>();
        JsonElement encoded = region.get(
                RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS);
        if (encoded == null || !encoded.isJsonArray()) {
            return ports;
        }
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (element.isJsonObject()) {
                ports.add(element.getAsJsonObject());
            }
        }
        return ports;
    }

    /**
     * One dropped client endpoint, or {@code null} when the evidence does not
     * name exactly one region.
     */
    private static JsonObject mintClientEntryRegion(
            String endpoint, List<JsonObject> holders, ObservedFrames frames,
            List<RuntimeRegionPlanner.RuntimeEvent> execution,
            List<RuntimeRegionPlanner.ProtocolEvent> protocol,
            Set<String> claimedRegions, Set<String> claimedRoots) {
        int separator = endpoint.indexOf('\n');
        String callSite = endpoint.substring(0, separator);
        String exchange = endpoint.substring(separator + 1);
        // The demand slice every holder shares.  The holders differ only in
        // the declared root each carries, so their intersection is the slice
        // the endpoint itself demands and no holder's own closure.
        Set<String> slice = null;
        for (JsonObject holder : holders) {
            Set<String> scope = strings(holder,
                    RuntimeSelectedRegionFinalizer.DEMAND_SCOPE);
            if (slice == null) {
                slice = scope;
            } else {
                slice.retainAll(scope);
            }
        }
        if (slice == null || slice.isEmpty()) {
            return null;
        }
        JsonArray ports = new JsonArray();
        String definitionMethod = "";
        String declaredCallee = null;
        for (JsonObject port : portsOf(holders.get(0))) {
            if (!endpoint.equals(string(port,
                    CommunicationCatalogContract.CALL_SITE_ID) + '\n'
                    + string(port,
                    CommunicationCatalogContract.EXCHANGE_SITE_KEY))) {
                continue;
            }
            ports.add(port);
            String owner = string(port,
                    CommunicationCatalogContract.PORT_DEFINITION_METHOD);
            if (definitionMethod.isEmpty()) {
                definitionMethod = owner;
            } else if (!definitionMethod.equals(owner)) {
                return null;
            }
            String callee = string(port,
                    CommunicationCatalogContract.DECLARED_CALLEE);
            if (declaredCallee == null) {
                declaredCallee = callee;
            } else if (!declaredCallee.equals(callee)) {
                return null;
            }
        }
        if (ports.size() == 0 || definitionMethod.isEmpty()
                || declaredCallee == null || declaredCallee.isEmpty()
                || !slice.contains(definitionMethod)) {
            return null;
        }
        // Every holder must declare this endpoint identically, or the
        // endpoint is not one shared thing and nothing may stand for it.
        for (JsonObject holder : holders) {
            JsonArray declared = new JsonArray();
            for (JsonObject port : portsOf(holder)) {
                if (endpoint.equals(string(port,
                        CommunicationCatalogContract.CALL_SITE_ID) + '\n'
                        + string(port, CommunicationCatalogContract
                        .EXCHANGE_SITE_KEY))) {
                    declared.add(port);
                }
            }
            if (!declared.equals(ports)) {
                return null;
            }
        }
        Set<String> anchors = null;
        for (JsonObject holder : holders) {
            Set<String> declared = strings(holder, "anchorMethods");
            if (anchors == null) {
                anchors = declared;
            } else {
                anchors.retainAll(declared);
            }
        }
        anchors.retainAll(slice);
        if (!anchors.contains(definitionMethod)) {
            return null;
        }
        String selection = string(holders.get(0), "selection");
        JsonArray loops = retainedLoopsInScope(holders.get(0), slice);
        for (JsonObject holder : holders) {
            if (!selection.equals(string(holder, "selection"))
                    || !retainedLoopsInScope(holder, slice).equals(loops)) {
                return null;
            }
        }
        for (String field : SHARED_SOURCE_DECLARATION_FIELDS) {
            JsonElement declared = holders.get(0).get(field);
            for (JsonObject holder : holders) {
                JsonElement other = holder.get(field);
                if (declared == null ? other != null
                        : !declared.equals(other)) {
                    return null;
                }
            }
        }
        ObservedClientEntry observed = frames.clientEntry(
                definitionMethod, callSite, declaredCallee, slice,
                execution, protocol);
        String root = observed == null ? "" : observed.rootMethod;
        if (root.isEmpty() || claimedRoots.contains(root)) {
            return null;
        }
        List<String> scope = new ArrayList<>(slice);
        Collections.sort(scope);
        StringBuilder identity = new StringBuilder(
                RuntimeRegionPlanner.COMMUNICATION_CLIENT_ENTRY)
                .append('\n').append(root)
                .append('\n').append(callSite)
                .append('\n').append(exchange);
        for (String method : scope) {
            identity.append('\n').append(method);
        }
        String regionId = "REGION." + UUID.nameUUIDFromBytes(
                identity.toString().getBytes(StandardCharsets.UTF_8));
        if (claimedRegions.contains(regionId)) {
            return null;
        }
        JsonObject row = new JsonObject();
        row.addProperty("schemaVersion",
                RuntimeSelectedRegionFinalizer.REGION_SCHEMA_VERSION);
        row.addProperty("kind", RuntimeSelectedRegionFinalizer.SKELETON_KIND);
        row.addProperty("regionId", regionId);
        row.addProperty("rootMethod", root);
        row.addProperty("rootAuthority",
                RuntimeRegionPlanner.COMMUNICATION_CLIENT_ENTRY);
        row.addProperty("anchorMethod", definitionMethod);
        List<String> anchorList = new ArrayList<>(anchors);
        Collections.sort(anchorList);
        row.add("anchorMethods", encodeStrings(anchorList));
        row.add("methods", encodeStrings(scope));
        row.add(RuntimeSelectedRegionFinalizer.DEMAND_SCOPE,
                encodeStrings(scope));
        row.addProperty("selection", selection);
        row.add(RuntimeSelectedRegionFinalizer.COMMUNICATION_PORTS, ports);
        if (loops.size() > 0) {
            row.add(RuntimeSelectedRegionFinalizer.RETAINED_LOOPS, loops);
        }
        for (String field : SHARED_SOURCE_DECLARATION_FIELDS) {
            JsonElement declared = holders.get(0).get(field);
            if (declared != null) {
                row.add(field, declared);
            }
        }
        row.add("baselineObservedMethods", encodeStrings(
                frames.observedInScope(observed.rootCallIds, slice)));
        // The re-root this row performs, named rather than implied: which
        // static regions declared this endpoint, and the roots they declared
        // that the run never entered.
        JsonObject reroot = new JsonObject();
        reroot.addProperty("schemaVersion", 1);
        reroot.addProperty("kind", "RUNTIME_CLIENT_ENTRY_REROOT");
        reroot.addProperty("authority", "OBSERVED_RPC_SEND_CLIENT_ENDPOINT_V2");
        reroot.addProperty(CommunicationCatalogContract.CALL_SITE_ID,
                callSite);
        reroot.addProperty(CommunicationCatalogContract.EXCHANGE_SITE_KEY,
                exchange);
        reroot.addProperty("observedRootMethod", root);
        JsonArray declaredRegions = new JsonArray();
        JsonArray declaredRoots = new JsonArray();
        for (JsonObject holder : holders) {
            declaredRegions.add(string(holder, "regionId"));
            declaredRoots.add(string(holder, "rootMethod"));
        }
        reroot.add("declaredRegionIds", declaredRegions);
        reroot.add("declaredRootMethods", declaredRoots);
        JsonArray observedSends = new JsonArray();
        for (RuntimeRegionPlanner.ProtocolEvent send : observed.sends) {
            JsonObject boundary = new JsonObject();
            boundary.addProperty("eventSeq", send.seq);
            boundary.addProperty("exchangeId", send.correlationId);
            if (!send.attemptId.isEmpty()) {
                boundary.addProperty("attemptId", send.attemptId);
            }
            boundary.addProperty("half", send.half);
            boundary.addProperty("invocationId", send.invocationId);
            observedSends.add(boundary);
        }
        reroot.add("observedRpcSends", observedSends);
        row.add(RuntimeRegionPlanner.CLIENT_ENTRY_REROOT, reroot);
        return row;
    }

    /** The retained loops a region declares for methods the scope holds. */
    private static JsonArray retainedLoopsInScope(JsonObject region,
                                                  Set<String> scope) {
        JsonArray result = new JsonArray();
        JsonElement encoded = region.get(
                RuntimeSelectedRegionFinalizer.RETAINED_LOOPS);
        if (encoded == null || !encoded.isJsonArray()) {
            return result;
        }
        for (JsonElement element : encoded.getAsJsonArray()) {
            if (element.isJsonObject() && scope.contains(string(
                    element.getAsJsonObject(), "enclosingMethod"))) {
                result.add(element);
            }
        }
        return result;
    }

    private static Set<String> strings(JsonObject row, String field) {
        Set<String> values = new LinkedHashSet<>();
        JsonElement encoded = row.get(field);
        if (encoded == null || !encoded.isJsonArray()) {
            return values;
        }
        for (JsonElement element : encoded.getAsJsonArray()) {
            values.add(element.getAsString());
        }
        return values;
    }

    private static JsonArray encodeStrings(Collection<String> values) {
        JsonArray encoded = new JsonArray();
        for (String value : values) {
            encoded.add(value);
        }
        return encoded;
    }

    /** Exact protocol evidence that authorizes one minted client entry. */
    private static final class ObservedClientEntry {
        private final String rootMethod;
        private final Set<Long> rootCallIds;
        private final List<RuntimeRegionPlanner.ProtocolEvent> sends;

        private ObservedClientEntry(
                String rootMethod, Set<Long> rootCallIds,
                List<RuntimeRegionPlanner.ProtocolEvent> sends) {
            this.rootMethod = rootMethod;
            this.rootCallIds = new LinkedHashSet<>(rootCallIds);
            this.sends = new ArrayList<>(sends);
        }
    }

    /**
     * The observed call tree, read only for the frames a minted client entry
     * needs: the frames one method entered, and the parent of each.
     */
    private static final class ObservedFrames {
        private final Map<Long, RuntimeRegionPlanner.MethodEvent> byCall =
                new LinkedHashMap<>();
        private final Map<Long, List<Long>> children = new LinkedHashMap<>();

        private ObservedFrames(
                List<RuntimeRegionPlanner.MethodEvent> methods) {
            for (RuntimeRegionPlanner.MethodEvent event : methods) {
                // A repeated call id cannot address one frame, so no frame
                // it names may root or bound a minted region.
                byCall.put(event.callId,
                        byCall.containsKey(event.callId) ? null : event);
                children.computeIfAbsent(event.parentCallId,
                        ignored -> new ArrayList<Long>()).add(event.callId);
            }
        }

        /**
         * Resolves the client entry from the exact request SENDs recorded
         * under one static cut.  Merely entering {@code owner} is not evidence
         * that the cut fired: a protocol boundary must sit below the matching
         * {@code CALL_SITE_ENTER} invocation in the recorded call tree.
         */
        private ObservedClientEntry clientEntry(
                String owner, String callSite, String declaredCallee,
                Set<String> scope,
                List<RuntimeRegionPlanner.RuntimeEvent> execution,
                List<RuntimeRegionPlanner.ProtocolEvent> protocol) {
            Map<Long, RuntimeRegionPlanner.RuntimeEvent> sites =
                    new LinkedHashMap<>();
            Set<Long> disputedSites = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.RuntimeEvent event : execution) {
                if (!"CALL_SITE_ENTER".equals(event.kind)
                        || event.invocationId <= 0L) {
                    continue;
                }
                RuntimeRegionPlanner.RuntimeEvent previous = sites.put(
                        event.invocationId, event);
                if (previous != null) {
                    disputedSites.add(event.invocationId);
                }
            }
            for (Long disputed : disputedSites) {
                sites.remove(disputed);
            }

            String rootMethod = "";
            Set<Long> rootCalls = new LinkedHashSet<>();
            List<RuntimeRegionPlanner.ProtocolEvent> sends = new ArrayList<>();
            for (RuntimeRegionPlanner.ProtocolEvent boundary : protocol) {
                if (!"SEND".equals(boundary.direction)
                        || !"REQUEST".equals(boundary.half)
                        || boundary.correlationId.isEmpty()) {
                    continue;
                }
                RuntimeRegionPlanner.RuntimeEvent site = enclosingSite(
                        boundary, sites, owner, callSite, declaredCallee);
                if (site == null || site.seq >= boundary.seq) {
                    continue;
                }
                RuntimeRegionPlanner.MethodEvent outermost =
                        clientEntryRoot(site.callId, scope);
                if (outermost == null) {
                    continue;
                }
                if (rootMethod.isEmpty()) {
                    rootMethod = outermost.method;
                } else if (!rootMethod.equals(outermost.method)) {
                    return null;
                }
                rootCalls.add(outermost.callId);
                sends.add(boundary);
            }
            return sends.isEmpty() ? null : new ObservedClientEntry(
                    rootMethod, rootCalls, sends);
        }

        /** The matching static call-site invocation enclosing one SEND. */
        private RuntimeRegionPlanner.RuntimeEvent enclosingSite(
                RuntimeRegionPlanner.ProtocolEvent boundary,
                Map<Long, RuntimeRegionPlanner.RuntimeEvent> sites,
                String owner, String callSite, String declaredCallee) {
            Set<Long> invocations = new LinkedHashSet<>();
            if (boundary.invocationId > 0L) {
                invocations.add(boundary.invocationId);
            }
            RuntimeRegionPlanner.MethodEvent frame = byCall.get(
                    boundary.callId);
            Set<Long> seenCalls = new LinkedHashSet<>();
            while (frame != null && seenCalls.add(frame.callId)) {
                if (frame.parentSiteId > 0L) {
                    invocations.add(frame.parentSiteId);
                }
                frame = byCall.get(frame.parentCallId);
            }
            RuntimeRegionPlanner.RuntimeEvent matched = null;
            for (Long invocation : invocations) {
                RuntimeRegionPlanner.RuntimeEvent site = sites.get(invocation);
                if (site == null || !owner.equals(site.method)
                        || !callSite.equals(site.siteId)
                        || !declaredCallee.equals(site.declaredCallee)) {
                    continue;
                }
                if (matched != null && matched.callId != site.callId) {
                    return null;
                }
                matched = site;
            }
            return matched;
        }

        /** The outermost in-scope owner frame of one exact call-site send. */
        private RuntimeRegionPlanner.MethodEvent clientEntryRoot(
                long ownerCallId, Set<String> scope) {
            RuntimeRegionPlanner.MethodEvent frame = byCall.get(ownerCallId);
            if (frame == null || frame.requestKey.isEmpty()
                    || !scope.contains(frame.method)) {
                return null;
            }
            RuntimeRegionPlanner.MethodEvent outermost = frame;
            while (true) {
                RuntimeRegionPlanner.MethodEvent parent =
                        byCall.get(outermost.parentCallId);
                if (parent == null || parent.laneId != frame.laneId
                        || !parent.requestKey.equals(frame.requestKey)
                        || !scope.contains(parent.method)) {
                    return outermost;
                }
                outermost = parent;
            }
        }

        /** The scope methods observed under every frame of {@code root}. */
        private List<String> observedInScope(Collection<Long> rootCalls,
                                             Set<String> scope) {
            Set<String> observed = new LinkedHashSet<>();
            Deque<Long> work = new ArrayDeque<>(rootCalls);
            Set<Long> seen = new LinkedHashSet<>(work);
            while (!work.isEmpty()) {
                long call = work.removeFirst();
                RuntimeRegionPlanner.MethodEvent frame = byCall.get(call);
                // The scope bounds which frames the region owns, not which
                // ones it may look through: a scope method called from a
                // frame outside the scope is still inside this activation,
                // exactly as the activation planner reads its own subtree.
                if (frame != null && scope.contains(frame.method)) {
                    observed.add(frame.method);
                }
                for (Long child : children.getOrDefault(call,
                        Collections.<Long>emptyList())) {
                    if (seen.add(child)) {
                        work.addLast(child);
                    }
                }
            }
            List<String> ordered = new ArrayList<>(observed);
            Collections.sort(ordered);
            return ordered;
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

    /**
     * Test seam for load-time re-attribution, run as the planning path runs
     * it: clear, re-read the durable trace, sort, re-attribute.
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

    /** Number of worker threads used by offline trace aggregation parsing. */
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
                    sourceRef(row),
                    row.longValue("receiverAttributed", 0L) != 0L,
                    row.stringValue("requestKey"),
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
        } else if ("RPC_SEND".equals(eventKind)
                || "RPC_RECEIVE".equals(eventKind)) {
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
            // Recognised, and deliberately not a protocol event.
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
        } else if ((!skeletonOnly || "CALL_SITE_ENTER".equals(eventKind))
                && isExecutionEventKind(eventKind)) {
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

    /** Reads the minimal pass-1 domain used to authenticate client entries. */
    static TraceData parseSkeletonTraceLinesForTests(List<String> lines)
            throws IOException {
        TraceData trace = new TraceData();
        int lineNumber = 1;
        for (String line : lines) {
            parseTraceLine(trace, line, lineNumber++,
                    new File("runtime-trace-test.jsonl"), "test", true,
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
                // Absent rather than false: an activation the context named
                // is the ordinary case and the trace is written per call.
                "receiverAttributed", event.receiverAttributed ? 1 : null,
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

    /** The row kind one recorded protocol leg is written under. */
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
                    // activations of the object it names.
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
        final List<RuntimeRegionPlanner.RuntimeEvent> execution =
                new ArrayList<>();
        final List<RuntimeRegionPlanner.ProtocolEvent> protocol =
                new ArrayList<>();
        final List<SourceTraceEvent> sources = new ArrayList<>();

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
            this.kind = MapFields.safe(kind);
            this.source = source;
            this.relatedSource = relatedSource;
            this.requestId = requestId;
            this.requestKey = MapFields.safe(requestKey);
            this.apiName = MapFields.safe(apiName);
            this.aliasClass = MapFields.safe(aliasClass);
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
            this.method = MapFields.safe(method);
            this.spanId = spanId;
            this.rootContext = rootContext;
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
