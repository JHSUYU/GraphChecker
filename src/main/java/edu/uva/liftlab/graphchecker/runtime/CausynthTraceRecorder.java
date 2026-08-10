package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.JsonElement;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import edu.uva.liftlab.graphchecker.causynth.CausynthJson;
import edu.uva.liftlab.graphchecker.causynth.RuntimeSelectedRegionFinalizer;
import edu.uva.liftlab.graphchecker.contract.FieldPathSpec;
import edu.uva.liftlab.graphchecker.contract.ProtocolBoundaryScalarConfig;

import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
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
import java.util.concurrent.Callable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Pattern;
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
    /** Immutable declarations shared by all recording threads. */
    private static volatile ProtocolBoundaryScalarConfig boundaryScalars;
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
        RuntimeTraceContext.View context = parent == null
                ? RuntimeTraceContext.enterRoot(receiver)
                : RuntimeTraceContext.current();
        RuntimeRegionPlanner.MethodEvent event =
                new RuntimeRegionPlanner.MethodEvent(id, testName, process,
                        threadName, tid, method, objectId,
                        runtimeType(receiver), id, parentCallId, parentSiteId,
                        context.ownerId, context.laneId, context.spanId,
                        context.parentSpanId, context.remoteParentSpanId);
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
                        inferProcessName(method, threadName), threadName,
                        thread.getId(), method, 0, "", id,
                        parentCallId, 0L, context.ownerId, context.laneId,
                        context.spanId, context.parentSpanId,
                        context.remoteParentSpanId);
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
        emitBoundaryScalars(boundaryScalars.serverLeaves(event.method,
                        "REQUEST", argumentIndex), "SERVER", "REQUEST",
                "METHOD_ARGUMENT", event.method, callId, 0L, event.id,
                value);
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
        emitBoundaryScalars(boundaryScalars.clientLeaves(
                        event.declaredCallee, "REQUEST", argumentIndex),
                "CLIENT", "REQUEST", "CALL_ARGUMENT", event.declaredCallee,
                event.callId, invocationId, event.id, value);
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
        emitBoundaryScalars(boundaryScalars.clientLeaves(
                        event.declaredCallee, "RESPONSE", -1),
                "CLIENT", "RESPONSE", "CALL_RETURN", event.declaredCallee,
                event.callId, invocationId, event.id, returnValue);
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
        emitBoundaryScalars(boundaryScalars.serverLeaves(event.method,
                        "RESPONSE", -1), "SERVER", "RESPONSE",
                "METHOD_RETURN", event.method, resolvedCallId, 0L, event.id,
                returnValue);
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

    /** Records an RPC boundary/span and an optional receiver-side owner. */
    public static void recordRpc(String direction, String transport,
                                 String correlationId, Object localOwner) {
        if (direction == null || transport == null
                || correlationId == null) {
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
        RuntimeTraceContext.View context = RuntimeTraceContext.rpc(direction,
                transport, correlationId, localOwner);
        RuntimeRegionPlanner.ProtocolEvent event =
                new RuntimeRegionPlanner.ProtocolEvent(id,
                        safe(direction).toUpperCase(), safe(transport),
                        safe(correlationId),
                        inferProcessName(method, thread.getName()),
                        thread.getName(), thread.getId(), method,
                        call == null ? 0L : call.callId,
                        site == null ? 0L : site.invocationId,
                        site == null ? "" : site.declaredCallee,
                        context.ownerId, context.laneId, context.spanId,
                        context.parentSpanId, context.remoteParentSpanId);
        synchronized (LOCK) {
            writeProtocolTraceLine(event);
        }
    }

    /**
     * Records only configured scalar leaves at a logical call boundary.
     * Reflection follows canonical declared fields and bounded reference-array
     * indices from the boundary value itself.  A traversal failure emits one
     * named gap and never a partial set of values for that declaration.
     */
    private static void emitBoundaryScalars(
            List<ProtocolBoundaryScalarConfig.Leaf> leaves, String side,
            String direction, String boundaryKind, String boundaryMethod,
            long callId, long invocationId, long boundaryEventSeq,
            Object root) {
        if (contextOnlyConcolicReplay || leaves == null || leaves.isEmpty()
                || boundaryEventSeq <= 0L) {
            return;
        }
        for (ProtocolBoundaryScalarConfig.Leaf leaf : leaves) {
            List<BoundaryScalarObservation> observations = new ArrayList<>();
            List<String> containerObservations = new ArrayList<>();
            BoundaryScalarGap gap = projectBoundaryScalar(leaf, root,
                    observations, containerObservations);
            if (gap != null) {
                writeBoundaryScalarGap(leaf, side, direction, boundaryKind,
                        boundaryMethod, callId, invocationId,
                        boundaryEventSeq, identity(root), gap,
                        containerObservations);
                continue;
            }
            for (BoundaryScalarObservation observation : observations) {
                writeBoundaryScalarValue(leaf, side, direction, boundaryKind,
                        boundaryMethod, callId, invocationId,
                        boundaryEventSeq, identity(root), observation,
                        observations.size(), containerObservations);
            }
        }
    }

    private static BoundaryScalarGap projectBoundaryScalar(
            ProtocolBoundaryScalarConfig.Leaf leaf, Object root,
            List<BoundaryScalarObservation> output,
            List<String> containerObservations) {
        List<BoundaryScalarObservation> staged = new ArrayList<>();
        BoundaryScalarGap gap = descendBoundaryScalar(leaf, root, 0,
                new ArrayList<Integer>(), 0, staged,
                containerObservations);
        if (gap == null && staged.isEmpty()
                && leaf.containerBound() > 0) {
            // Empty and heterogeneous arrays must still leave explicit
            // schema-4 evidence.  Otherwise a valid empty selection is
            // indistinguishable from a pre-migration trace.
            return new BoundaryScalarGap(
                    "NO_CONFIGURED_SCALAR_ELEMENTS", -1);
        }
        if (gap == null) output.addAll(staged);
        return gap;
    }

    private static BoundaryScalarGap descendBoundaryScalar(
            ProtocolBoundaryScalarConfig.Leaf leaf, Object value, int step,
            List<Integer> indices, int leafReceiverObjectId,
            List<BoundaryScalarObservation> output,
            List<String> containerObservations) {
        if (value == null) {
            return new BoundaryScalarGap("NULL_PATH_VALUE", -1);
        }
        List<String> path = leaf.declaredPath();
        if (step >= path.size()) {
            if (!boundaryScalarValue(leaf.javaType(), value)) {
                return new BoundaryScalarGap("SCALAR_TYPE_MISMATCH", -1);
            }
            output.add(new BoundaryScalarObservation(indices,
                    leafReceiverObjectId, identity(value),
                    String.valueOf(value), false));
            return null;
        }
        String pathStep = path.get(step);
        if (ProtocolBoundaryScalarConfig.ARRAY_ELEMENT.equals(pathStep)) {
            Class<?> type = value.getClass();
            if (!type.isArray() || type.getComponentType().isPrimitive()) {
                return new BoundaryScalarGap(
                        "REFERENCE_ARRAY_TYPE_MISMATCH", -1);
            }
            int length = Array.getLength(value);
            containerObservations.add(containerObservation(indices, length));
            if (length > leaf.containerBound()) {
                return new BoundaryScalarGap("CONTAINER_BOUND_INSUFFICIENT",
                        length);
            }
            for (int index = 0; index < length; index++) {
                Object element = Array.get(value, index);
                if (step + 1 < path.size()
                        && !ProtocolBoundaryScalarConfig.ARRAY_ELEMENT.equals(
                        path.get(step + 1))) {
                    FieldPathSpec.DeclaredField next =
                            FieldPathSpec.declaredField(path.get(step + 1));
                    if (element == null || next != null
                            && !declaresOwner(element.getClass(),
                            next.owner())) {
                        // A heterogeneous reference array can carry several
                        // declared variants.  A configured subclass field
                        // selects only elements of that declared variant.
                        continue;
                    }
                }
                List<Integer> nested = new ArrayList<>(indices);
                nested.add(index);
                BoundaryScalarGap gap = descendBoundaryScalar(leaf,
                        element, step + 1, nested,
                        leafReceiverObjectId, output,
                        containerObservations);
                if (gap != null) return gap;
            }
            return null;
        }

        FieldPathSpec.DeclaredField declared =
                FieldPathSpec.declaredField(pathStep);
        Field field = exactDeclaredField(value.getClass(), declared);
        if (field == null) {
            return new BoundaryScalarGap("DECLARED_FIELD_UNAVAILABLE", -1);
        }
        try {
            if (!field.isAccessible()) field.setAccessible(true);
            Object fieldValue = field.get(value);
            int receiver = identity(value);
            if (step == path.size() - 1 && fieldValue == null
                    && "java.lang.String".equals(leaf.javaType())) {
                output.add(new BoundaryScalarObservation(indices, receiver,
                        0, "", true));
                return null;
            }
            return descendBoundaryScalar(leaf, fieldValue, step + 1,
                    indices, receiver, output, containerObservations);
        } catch (RuntimeException | IllegalAccessException inaccessible) {
            return new BoundaryScalarGap("DECLARED_FIELD_UNAVAILABLE", -1);
        }
    }

    private static Field exactDeclaredField(
            Class<?> runtimeClass, FieldPathSpec.DeclaredField declared) {
        if (runtimeClass == null || declared == null) return null;
        for (Class<?> type = runtimeClass; type != null;
             type = type.getSuperclass()) {
            if (!declared.owner().equals(type.getName())) continue;
            try {
                Field field = type.getDeclaredField(declared.name());
                return fieldType(field.getType()).equals(declared.type())
                        ? field : null;
            } catch (NoSuchFieldException missing) {
                return null;
            }
        }
        return null;
    }

    private static boolean declaresOwner(Class<?> runtimeClass,
                                         String owner) {
        for (Class<?> type = runtimeClass; type != null;
             type = type.getSuperclass()) {
            if (safe(owner).equals(type.getName())) return true;
        }
        return false;
    }

    private static String containerObservation(List<Integer> prefix,
                                               int width) {
        StringBuilder encoded = new StringBuilder();
        if (prefix.isEmpty()) {
            encoded.append("ROOT");
        } else {
            for (int index = 0; index < prefix.size(); index++) {
                if (index > 0) encoded.append(',');
                encoded.append(prefix.get(index));
            }
        }
        return encoded.append('=').append(width).toString();
    }

    private static String fieldType(Class<?> type) {
        if (!type.isArray()) return type.getName();
        int dimensions = 0;
        Class<?> component = type;
        while (component.isArray()) {
            dimensions++;
            component = component.getComponentType();
        }
        StringBuilder result = new StringBuilder(component.getName());
        for (int index = 0; index < dimensions; index++) {
            result.append("[]");
        }
        return result.toString();
    }

    private static boolean boundaryScalarValue(String javaType,
                                               Object value) {
        if (value == null) return "java.lang.String".equals(javaType);
        if ("java.lang.String".equals(javaType)) {
            return value instanceof String;
        }
        if ("boolean".equals(javaType)) return value instanceof Boolean;
        if ("char".equals(javaType)) return value instanceof Character;
        return value instanceof Number;
    }

    private static void writeBoundaryScalarValue(
            ProtocolBoundaryScalarConfig.Leaf leaf, String side,
            String direction, String boundaryKind, String boundaryMethod,
            long callId, long invocationId, long boundaryEventSeq,
            int rootObjectId, BoundaryScalarObservation observation,
            int leafValueCount, List<String> containerObservations) {
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) return;
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 4,
                    "event", "RPC_BOUNDARY_SCALAR",
                    "seq", id,
                    "mappingId", leaf.mappingId(),
                    "leafId", leaf.leafId(),
                    "protocolDirection", direction,
                    "side", side,
                    "port", leaf.port(),
                    "boundaryKind", boundaryKind,
                    "boundaryMethod", boundaryMethod,
                    "callId", callId,
                    "invocationId", invocationId,
                    "boundaryEventSeq", boundaryEventSeq,
                    "boundaryRootObjectId", rootObjectId,
                    "leafReceiverObjectId",
                    observation.leafReceiverObjectId,
                    "valueObjectId", observation.valueObjectId,
                    "declaredPath", leaf.declaredPath(),
                    "arrayIndices", observation.indices,
                    "javaType", leaf.javaType(),
                    "primitiveValue", observation.primitiveValue,
                    "nullValue", observation.nullValue,
                    "containerBound", leaf.containerBound(),
                    "leafObservationComplete", true,
                    "leafValueCount", leafValueCount,
                    "containerObservations", containerObservations,
                    "valueAuthority",
                    ProtocolBoundaryScalarConfig.VALUE_AUTHORITY);
        }
    }

    private static void writeBoundaryScalarGap(
            ProtocolBoundaryScalarConfig.Leaf leaf, String side,
            String direction, String boundaryKind, String boundaryMethod,
            long callId, long invocationId, long boundaryEventSeq,
            int rootObjectId, BoundaryScalarGap gap,
            List<String> containerObservations) {
        long id = EVENT_COUNTER.incrementAndGet();
        if (id > maxEvents) return;
        synchronized (LOCK) {
            writeTraceRow(
                    "schemaVersion", 4,
                    "event", "RPC_BOUNDARY_SCALAR_GAP",
                    "seq", id,
                    "mappingId", leaf.mappingId(),
                    "leafId", leaf.leafId(),
                    "protocolDirection", direction,
                    "side", side,
                    "port", leaf.port(),
                    "boundaryKind", boundaryKind,
                    "boundaryMethod", boundaryMethod,
                    "callId", callId,
                    "invocationId", invocationId,
                    "boundaryEventSeq", boundaryEventSeq,
                    "boundaryRootObjectId", rootObjectId,
                    "declaredPath", leaf.declaredPath(),
                    "javaType", leaf.javaType(),
                    "containerBound", leaf.containerBound(),
                    "observedContainerWidth", gap.observedWidth,
                    "leafObservationComplete", true,
                    "leafValueCount", 0,
                    "containerObservations", containerObservations,
                    "gap", gap.reason,
                    "valueAuthority",
                    ProtocolBoundaryScalarConfig.GAP_AUTHORITY);
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
                ProtocolBoundaryScalarConfig configuredBoundaryScalars =
                        ProtocolBoundaryScalarConfig.fromConfiguration();
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
                    boundaryScalars = configuredBoundaryScalars;
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
                boundaryScalars = configuredBoundaryScalars;
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
            requireConfiguredBoundaryScalarEvidence(trace);
            long traceLoadMillis = elapsedMillis(traceLoadStart);
            Set<String> observedMethods = new LinkedHashSet<>();
            for (RuntimeRegionPlanner.MethodEvent event : trace.methods) {
                observedMethods.add(event.method);
            }
            RuntimeRegionPlanner.Result activationGraph =
                    RuntimeRegionPlanner.planSkeletonGraph(
                            selectedSkeletons, trace.methods);
            long refinementStart = System.nanoTime();
            RuntimeRefinedGraphBuilder.Result refinement =
                    RuntimeRefinedGraphBuilder.refine(candidateGraph,
                            selectedSkeletons,
                            activationGraph.runtimeInstances,
                            trace.methods, trace.execution,
                            trace.fields, trace.arrays, trace.protocol,
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
                    regionFile, regionEdgeFile,
                    observedMethods, activationGraph.runtimeInstances,
                    branchObservations(trace.execution));
            long candidatePlanningMillis =
                    elapsedMillis(candidatePlanningStart);
            long planBindingStart = System.nanoTime();
            for (Map<String, Object> row : closure.regions) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            for (Map<String, Object> row : closure.regionEdges) {
                RuntimeRefinedGraphBuilder.normalizeNumbersInPlace(row);
            }
            writeRuntimeRegionPlans(planOutputDirectory, refinedFlowIndex,
                    closure.regions, closure.regionEdges,
                    regionFile, regionEdgeFile, trace,
                    activationGraph.runtimeInstances);
            long planBindingMillis = elapsedMillis(planBindingStart);
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

    /** Compact, lossless BRANCH rows used to bind fatal sites to activations. */
    private static List<Map<String, Object>> branchObservations(
            Collection<RuntimeRegionPlanner.RuntimeEvent> events) {
        List<Map<String, Object>> result = new ArrayList<>();
        if (events == null) return result;
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
        Map<String, Set<String>> sourceRegionsByRegion =
                new LinkedHashMap<>();
        for (Map<String, Object> instance : runtimeInstances) {
            String region = String.valueOf(instance.get("regionId"));
            String root = String.valueOf(instance.get("rootMethod"));
            String previous = rootByRegion.putIfAbsent(region, root);
            if (previous != null && !previous.equals(root)) {
                throw new IOException("one region definition resolved to "
                        + "multiple execution-context roots: " + region);
            }
            activationCounts.merge(region, 1, Integer::sum);
            Set<String> sourceRegions = sourceRegionsByRegion
                    .computeIfAbsent(region,
                            ignored -> new LinkedHashSet<>());
            Object encodedRegions = instance.get("regionIds");
            if (encodedRegions instanceof Collection<?>) {
                for (Object sourceRegion
                        : (Collection<?>) encodedRegions) {
                    sourceRegions.add(String.valueOf(sourceRegion));
                }
            }
            if (sourceRegions.isEmpty()) {
                sourceRegions.add(region);
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
                Set<String> potentialMethods = new LinkedHashSet<>();
                // Coalescing several static regions into one activation
                // widens the region; its demanded scope has to widen with it,
                // or a guard contributed by one source would be judged
                // against another source's demand.
                Set<String> demandScope = new LinkedHashSet<>();
                boolean demandScopeKnown = true;
                for (String sourceRegion : sourceRegionsByRegion
                        .getOrDefault(region,
                                Collections.singleton(region))) {
                    JsonObject source = candidateByRegion.get(sourceRegion);
                    if (source == null) {
                        throw new IOException("runtime activation references "
                                + "unknown static region: " + sourceRegion);
                    }
                    for (JsonElement method
                            : source.getAsJsonArray("methods")) {
                        potentialMethods.add(method.getAsString());
                    }
                    JsonArray sourceScope = source.getAsJsonArray(
                            RuntimeSelectedRegionFinalizer.DEMAND_SCOPE);
                    if (sourceScope == null) {
                        demandScopeKnown = false;
                        continue;
                    }
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
     * Proves that every configured leaf at every observed logical boundary
     * has one complete schema-4 observation.  Completeness is per leaf and
     * occurrence: an unrelated row can never discharge a missing boundary.
     */
    private static void requireConfiguredBoundaryScalarEvidence(
            TraceData trace) throws IOException {
        requireConfiguredBoundaryScalarEvidenceForTests(trace.execution,
                trace.protocol);
    }

    static void requireConfiguredBoundaryScalarEvidenceForTests(
            List<RuntimeRegionPlanner.RuntimeEvent> execution,
            List<RuntimeRegionPlanner.ProtocolEvent> protocol)
            throws IOException {
        ProtocolBoundaryScalarConfig configured =
                ProtocolBoundaryScalarConfig.fromConfiguration();
        Map<String, ExpectedBoundaryLeaf> expected = new LinkedHashMap<>();
        for (RuntimeRegionPlanner.RuntimeEvent event : execution) {
            if ("CALL_ARGUMENT".equals(event.kind)) {
                addExpectedBoundaryLeaves(expected,
                        configured.clientLeaves(event.declaredCallee,
                                "REQUEST", event.argumentIndex),
                        "CLIENT", "CALL_ARGUMENT", event.declaredCallee,
                        event);
            } else if ("CALL_SITE_RETURN".equals(event.kind)) {
                addExpectedBoundaryLeaves(expected,
                        configured.clientLeaves(event.declaredCallee,
                                "RESPONSE", -1),
                        "CLIENT", "CALL_RETURN", event.declaredCallee,
                        event);
            } else if ("METHOD_ARGUMENT".equals(event.kind)) {
                addExpectedBoundaryLeaves(expected,
                        configured.serverLeaves(event.method,
                                "REQUEST", event.argumentIndex),
                        "SERVER", "METHOD_ARGUMENT", event.method, event);
            } else if ("METHOD_EXIT_NORMAL".equals(event.kind)) {
                addExpectedBoundaryLeaves(expected,
                        configured.serverLeaves(event.method,
                                "RESPONSE", -1),
                        "SERVER", "METHOD_RETURN", event.method, event);
            }
        }

        Map<String, List<RuntimeRegionPlanner.ProtocolEvent>> actual =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.ProtocolEvent event : protocol) {
            if (!("RPC_BOUNDARY_SCALAR".equals(event.direction)
                    || "RPC_BOUNDARY_SCALAR_GAP".equals(event.direction))) {
                continue;
            }
            String key = boundaryEvidenceKey(event.mappingId,
                    event.protocolDirection, event.side, event.port,
                    event.leafId, event.declaredPath, event.javaType,
                    event.containerBound, event.boundaryKind, event.method,
                    event.boundaryEventSeq, event.callId,
                    event.invocationId, event.boundaryRootObjectId);
            if (!expected.containsKey(key)) {
                throw new IOException("Unconfigured or misbound schema-4 "
                        + "boundary-scalar row at seq " + event.seq);
            }
            actual.computeIfAbsent(key,
                    ignored -> new ArrayList<>()).add(event);
        }
        for (Map.Entry<String, ExpectedBoundaryLeaf> entry
                : expected.entrySet()) {
            List<RuntimeRegionPlanner.ProtocolEvent> rows = actual.get(
                    entry.getKey());
            if (rows == null || rows.isEmpty()) {
                throw new IOException("Missing complete schema-4 boundary "
                        + "evidence for " + entry.getValue().description());
            }
            validateCompleteBoundaryLeaf(entry.getValue(), rows);
        }
    }

    private static void addExpectedBoundaryLeaves(
            Map<String, ExpectedBoundaryLeaf> expected,
            List<ProtocolBoundaryScalarConfig.Leaf> leaves,
            String side, String boundaryKind, String boundaryMethod,
            RuntimeRegionPlanner.RuntimeEvent event) throws IOException {
        for (ProtocolBoundaryScalarConfig.Leaf leaf : leaves) {
            ExpectedBoundaryLeaf value = new ExpectedBoundaryLeaf(leaf,
                    side, boundaryKind, boundaryMethod, event.seq,
                    event.callId, event.invocationId, event.objectId);
            String key = value.key();
            if (expected.putIfAbsent(key, value) != null) {
                throw new IOException("Duplicate configured boundary leaf "
                        + "occurrence: " + value.description());
            }
        }
    }

    private static void validateCompleteBoundaryLeaf(
            ExpectedBoundaryLeaf expected,
            List<RuntimeRegionPlanner.ProtocolEvent> rows)
            throws IOException {
        List<RuntimeRegionPlanner.ProtocolEvent> values = new ArrayList<>();
        List<RuntimeRegionPlanner.ProtocolEvent> gaps = new ArrayList<>();
        for (RuntimeRegionPlanner.ProtocolEvent row : rows) {
            if (!row.leafObservationComplete) {
                throw incompleteBoundaryEvidence(expected,
                        "completion marker absent");
            }
            if ("RPC_BOUNDARY_SCALAR_GAP".equals(row.direction)) {
                gaps.add(row);
            } else {
                values.add(row);
            }
        }
        if (!values.isEmpty() && !gaps.isEmpty()) {
            throw incompleteBoundaryEvidence(expected,
                    "value and gap rows are mixed");
        }
        if (!gaps.isEmpty()) {
            if (gaps.size() != 1) {
                throw incompleteBoundaryEvidence(expected,
                        "gap row is not unique");
            }
            RuntimeRegionPlanner.ProtocolEvent gap = gaps.get(0);
            if (!ProtocolBoundaryScalarConfig.GAP_AUTHORITY.equals(
                    gap.valueAuthority) || gap.gap.isEmpty()
                    || gap.leafValueCount != 0
                    || !gap.arrayIndices.isEmpty()) {
                throw incompleteBoundaryEvidence(expected,
                        "invalid gap authority or completion metadata");
            }
            validateContainerObservations(expected, gap, false);
            return;
        }
        if (values.isEmpty()) {
            throw incompleteBoundaryEvidence(expected, "no value rows");
        }
        List<String> completedContainers = null;
        Set<List<Integer>> indices = new LinkedHashSet<>();
        for (RuntimeRegionPlanner.ProtocolEvent value : values) {
            if (!ProtocolBoundaryScalarConfig.VALUE_AUTHORITY.equals(
                    value.valueAuthority)
                    || !value.gap.isEmpty()
                    || value.leafValueCount != values.size()
                    || value.leafReceiverObjectId <= 0) {
                throw incompleteBoundaryEvidence(expected,
                        "invalid value authority or count");
            }
            if (!indices.add(new ArrayList<>(value.arrayIndices))) {
                throw incompleteBoundaryEvidence(expected,
                        "duplicate array index tuple");
            }
            if (completedContainers == null) {
                completedContainers = value.containerObservations;
            } else if (!completedContainers.equals(
                    value.containerObservations)) {
                throw incompleteBoundaryEvidence(expected,
                        "inconsistent container completion metadata");
            }
            validateContainerObservations(expected, value, true);
        }
        if (expected.arrayDepth == 0
                && (values.size() != 1
                || !values.get(0).arrayIndices.isEmpty())) {
            throw incompleteBoundaryEvidence(expected,
                    "non-array leaf must have exactly one scalar row");
        }
    }

    private static void validateContainerObservations(
            ExpectedBoundaryLeaf expected,
            RuntimeRegionPlanner.ProtocolEvent row, boolean requireIndices)
            throws IOException {
        if (expected.arrayDepth == 0) {
            if (!row.containerObservations.isEmpty()) {
                throw incompleteBoundaryEvidence(expected,
                        "non-array leaf has container metadata");
            }
            return;
        }
        Map<String, Integer> widths = new LinkedHashMap<>();
        int overflowCount = 0;
        for (String observation : row.containerObservations) {
            int separator = observation.lastIndexOf('=');
            if (separator <= 0 || separator == observation.length() - 1) {
                throw incompleteBoundaryEvidence(expected,
                        "malformed container observation");
            }
            String prefix = observation.substring(0, separator);
            int width;
            try {
                width = Integer.parseInt(observation.substring(
                        separator + 1));
            } catch (NumberFormatException invalid) {
                throw incompleteBoundaryEvidence(expected,
                        "malformed container width");
            }
            if (width > expected.leaf.containerBound()) overflowCount++;
            boolean declaredOverflow = !requireIndices
                    && "CONTAINER_BOUND_INSUFFICIENT".equals(row.gap)
                    && width == row.observedContainerWidth;
            if (width < 0
                    || width > expected.leaf.containerBound()
                    && !declaredOverflow
                    || widths.put(prefix, width) != null) {
                throw incompleteBoundaryEvidence(expected,
                        "invalid or duplicate container width");
            }
        }
        if (!requireIndices
                && "CONTAINER_BOUND_INSUFFICIENT".equals(row.gap)
                && (overflowCount != 1 || row.observedContainerWidth
                <= expected.leaf.containerBound())) {
            throw incompleteBoundaryEvidence(expected,
                    "bound gap lacks one exact overflowing width");
        }
        if (!requireIndices) return;
        for (Integer index : row.arrayIndices) {
            if (index == null || index < 0) {
                throw incompleteBoundaryEvidence(expected,
                        "negative array index");
            }
        }
        if (row.arrayIndices.size() != expected.arrayDepth) {
            throw incompleteBoundaryEvidence(expected,
                    "array index depth mismatch");
        }
        for (int depth = 0; depth < expected.arrayDepth; depth++) {
            String prefix = containerPrefix(row.arrayIndices, depth);
            Integer width = widths.get(prefix);
            if (width == null || row.arrayIndices.get(depth) >= width) {
                throw incompleteBoundaryEvidence(expected,
                        "array index lacks completed container width");
            }
        }
    }

    private static String containerPrefix(List<Integer> indices, int depth) {
        if (depth == 0) return "ROOT";
        StringBuilder result = new StringBuilder();
        for (int index = 0; index < depth; index++) {
            if (index > 0) result.append(',');
            result.append(indices.get(index));
        }
        return result.toString();
    }

    private static IOException incompleteBoundaryEvidence(
            ExpectedBoundaryLeaf expected, String reason) {
        return new IOException("Incomplete schema-4 boundary evidence for "
                + expected.description() + ": " + reason);
    }

    private static String boundaryEvidenceKey(
            String mappingId, String direction, String side, String port,
            String leafId, List<String> path, String javaType, int bound,
            String boundaryKind, String method, long boundaryEventSeq,
            long callId, long invocationId, int boundaryRootObjectId) {
        return safe(mappingId) + '\n' + safe(direction) + '\n'
                + safe(side) + '\n' + safe(port) + '\n' + safe(leafId)
                + '\n' + path + '\n' + safe(javaType) + '\n' + bound
                + '\n' + safe(boundaryKind) + '\n' + safe(method) + '\n'
                + boundaryEventSeq + '\n' + callId + '\n' + invocationId
                + '\n' + boundaryRootObjectId;
    }

    private static final class ExpectedBoundaryLeaf {
        private final ProtocolBoundaryScalarConfig.Leaf leaf;
        private final String side;
        private final String boundaryKind;
        private final String boundaryMethod;
        private final long boundaryEventSeq;
        private final long callId;
        private final long invocationId;
        private final int boundaryRootObjectId;
        private final int arrayDepth;

        private ExpectedBoundaryLeaf(
                ProtocolBoundaryScalarConfig.Leaf leaf, String side,
                String boundaryKind, String boundaryMethod,
                long boundaryEventSeq, long callId, long invocationId,
                int eventObjectId) {
            this.leaf = leaf;
            this.side = side;
            this.boundaryKind = boundaryKind;
            this.boundaryMethod = boundaryMethod;
            this.boundaryEventSeq = boundaryEventSeq;
            this.callId = callId;
            this.invocationId = invocationId;
            this.boundaryRootObjectId = eventObjectId;
            int depth = 0;
            for (String step : leaf.declaredPath()) {
                if (ProtocolBoundaryScalarConfig.ARRAY_ELEMENT.equals(step)) {
                    depth++;
                }
            }
            this.arrayDepth = depth;
        }

        private String key() {
            return boundaryEvidenceKey(leaf.mappingId(), leaf.direction(),
                    side, leaf.port(), leaf.leafId(), leaf.declaredPath(),
                    leaf.javaType(), leaf.containerBound(), boundaryKind,
                    boundaryMethod, boundaryEventSeq, callId, invocationId,
                    boundaryRootObjectId);
        }

        private String description() {
            return leaf.mappingId() + "/" + leaf.leafId() + " " + side
                    + " " + boundaryKind + "@" + boundaryEventSeq;
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
        boundaryScalars = null;
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
            // The strict flat scanner refused the row; reproduce the exact
            // legacy diagnostics with the reference parser.
            final JsonObject parsed;
            try {
                JsonElement element = JsonParser.parseString(line);
                if (!element.isJsonObject()) {
                    throw new IllegalArgumentException(
                            "row is not an object");
                }
                parsed = element.getAsJsonObject();
            } catch (RuntimeException malformed) {
                throw new IOException("Malformed runtime trace row "
                        + lineNumber + " in " + file, malformed);
            }
            int schemaVersion = integer(parsed, "schemaVersion", -1);
            if (schemaVersion != 3 && schemaVersion != 4) {
                throw new IOException("Unsupported runtime trace row: "
                        + line);
            }
            row = FlatJsonRow.fromJsonObject(parsed, pool);
        }
        long schemaVersion = row.longValue("schemaVersion", -1L);
        if (schemaVersion != 3L && schemaVersion != 4L) {
            throw new IOException("Unsupported runtime trace row: " + line);
        }
        String eventKind = row.stringValue("event");
        if (schemaVersion == 3L
                && ("RPC_BOUNDARY_SCALAR".equals(eventKind)
                || "RPC_BOUNDARY_SCALAR_GAP".equals(eventKind))) {
            throw new IOException("Boundary-scalar runtime rows require "
                    + "schemaVersion 4: " + line);
        }
        if (schemaVersion == 4L
                && !("RPC_BOUNDARY_SCALAR".equals(eventKind)
                || "RPC_BOUNDARY_SCALAR_GAP".equals(eventKind))) {
            throw new IOException("Unsupported schema-4 runtime trace row: "
                    + line);
        }
        if ("METHOD_ENTER".equals(eventKind)) {
            String process = row.stringValue("process");
            if (process.isEmpty()) {
                throw new IOException("METHOD_ENTER has no process at "
                        + file + ":" + lineNumber);
            }
            long seq = row.longValue("seq", 0L);
            trace.methods.add(new RuntimeRegionPlanner.MethodEvent(
                    seq,
                    test,
                    process,
                    row.stringValue("threadName"),
                    row.longValue("tid", 0L),
                    row.stringValue("method"),
                    row.intValue("objectId", 0),
                    row.stringValue("receiverType"),
                    row.longValue("callId", seq),
                    row.longValue("parentCallId", 0L),
                    row.longValue("parentSiteId", 0L),
                    row.longValue("ownerId", 0L),
                    row.longValue("laneId", 0L),
                    row.longValue("spanId", 0L),
                    row.longValue("parentSpanId", 0L),
                    row.longValue("remoteParentSpanId", 0L)));
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
                    row.stringValue("process"),
                    row.stringValue("threadName"),
                    row.longValue("tid", 0L),
                    row.stringValue("method"),
                    row.longValue("callId", 0L),
                    row.longValue("invocationId", 0L),
                    row.stringValue("declaredCallee"),
                    row.longValue("ownerId", 0L),
                    row.longValue("laneId", 0L),
                    row.longValue("spanId", 0L),
                    row.longValue("parentSpanId", 0L),
                    row.longValue("remoteParentSpanId", 0L)));
        } else if (!skeletonOnly && ("RPC_BOUNDARY_SCALAR".equals(eventKind)
                || "RPC_BOUNDARY_SCALAR_GAP".equals(eventKind))) {
            trace.protocol.add(new RuntimeRegionPlanner.ProtocolEvent(
                    row.longValue("seq", 0L), eventKind,
                    row.stringValue("mappingId"),
                    row.stringValue("protocolDirection"),
                    row.stringValue("side"), row.stringValue("port"),
                    row.stringValue("leafId"),
                    row.stringValue("boundaryKind"),
                    row.stringValue("boundaryMethod"),
                    row.longValue("callId", 0L),
                    row.longValue("invocationId", 0L),
                    row.longValue("boundaryEventSeq", -1L),
                    row.intValue("boundaryRootObjectId", 0),
                    row.intValue("leafReceiverObjectId", 0),
                    row.intValue("valueObjectId", 0),
                    row.stringList("declaredPath"),
                    row.integerList("arrayIndices"),
                    row.stringValue("javaType"),
                    row.stringValue("primitiveValue"),
                    row.booleanValue("nullValue", false),
                    row.intValue("containerBound", 0),
                    row.intValue("observedContainerWidth", -1),
                    row.stringValue("valueAuthority"),
                    row.stringValue("gap"),
                    row.booleanValue("leafObservationComplete", false),
                    row.intValue("leafValueCount", -1),
                    row.stringList("containerObservations")));
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
                "parentSiteId", event.parentSiteId,
                "ownerId", event.ownerId,
                "laneId", event.laneId,
                "spanId", event.spanId,
                "parentSpanId", event.parentSpanId,
                "remoteParentSpanId", event.remoteParentSpanId);
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

    private static void writeProtocolTraceLine(
            RuntimeRegionPlanner.ProtocolEvent event) {
        writeTraceRow(
                "schemaVersion", 3,
                "event", "SEND".equals(event.direction)
                        ? "RPC_SEND" : "RPC_RECEIVE",
                "seq", event.seq,
                "transport", event.transport,
                "correlationId", event.correlationId,
                "process", event.process,
                "threadName", event.threadName,
                "tid", event.tid,
                "method", event.method,
                "callId", event.callId,
                "invocationId", event.invocationId,
                "declaredCallee", event.declaredCallee,
                "ownerId", event.ownerId,
                "laneId", event.laneId,
                "spanId", event.spanId,
                "parentSpanId", event.parentSpanId,
                "remoteParentSpanId", event.remoteParentSpanId);
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
            File directory, RuntimeRegionPlanner.RefinedFlowIndex flowIndex,
            List<Map<String, Object>> regions,
            List<Map<String, Object>> regionEdges,
            File regionFile, File regionEdgeFile, TraceData trace,
            Collection<Map<String, Object>> runtimeSeeds) throws IOException {
        RuntimeRegionPlanner.Result planned = RuntimeRegionPlanner.plan(
                regions, regionEdges, flowIndex, regionFile,
                regionEdgeFile, runtimeSeeds, trace.methods,
                trace.execution, trace.fields);
        writeRuntimePlanArtifacts(directory,
                planned.edgeValidationsJsonl(), planned.regionPlansJsonl());
    }

    private static void writeRuntimePlanArtifacts(
            File directory,
            String edgeValidations, String regionPlans)
            throws IOException {
        writeFile(new File(directory,
                        "runtime_region_edge_validation.jsonl"),
                edgeValidations);
        writeFile(new File(directory,
                        "concolic_region_plan.jsonl"),
                regionPlans);
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

    private static final class BoundaryScalarObservation {
        private final List<Integer> indices;
        private final int leafReceiverObjectId;
        private final int valueObjectId;
        private final String primitiveValue;
        private final boolean nullValue;

        private BoundaryScalarObservation(List<Integer> indices,
                                          int leafReceiverObjectId,
                                          int valueObjectId,
                                          String primitiveValue,
                                          boolean nullValue) {
            this.indices = Collections.unmodifiableList(
                    new ArrayList<>(indices));
            this.leafReceiverObjectId = leafReceiverObjectId;
            this.valueObjectId = valueObjectId;
            this.primitiveValue = safe(primitiveValue);
            this.nullValue = nullValue;
        }
    }

    private static final class BoundaryScalarGap {
        private final String reason;
        private final int observedWidth;

        private BoundaryScalarGap(String reason, int observedWidth) {
            this.reason = safe(reason);
            this.observedWidth = observedWidth;
        }
    }

    private static final class TraceData {
        private final List<RuntimeRegionPlanner.MethodEvent> methods =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.FieldAccessEvent> fields =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.ArrayAccessEvent> arrays =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.RuntimeEvent> execution =
                new ArrayList<>();
        private final List<RuntimeRegionPlanner.ProtocolEvent> protocol =
                new ArrayList<>();

        private void sort() {
            methods.sort((left, right) -> Long.compare(left.seq, right.seq));
            fields.sort((left, right) -> Long.compare(left.seq, right.seq));
            arrays.sort((left, right) -> Long.compare(left.seq, right.seq));
            execution.sort((left, right) ->
                    Long.compare(left.seq, right.seq));
            protocol.sort((left, right) -> Long.compare(left.seq, right.seq));
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

        private static FlatJsonRow fromJsonObject(
                JsonObject object, ConcurrentHashMap<String, String> pool) {
            List<String> keys = new ArrayList<>();
            List<Object> values = new ArrayList<>();
            for (Map.Entry<String, JsonElement> entry : object.entrySet()) {
                JsonElement value = entry.getValue();
                Object decoded;
                if (value == null || value.isJsonNull()) {
                    decoded = null;
                } else if (value.isJsonPrimitive()) {
                    if (value.getAsJsonPrimitive().isBoolean()) {
                        decoded = value.getAsBoolean();
                    } else if (value.getAsJsonPrimitive().isNumber()) {
                        String token = value.getAsString();
                        decoded = token.indexOf('.') >= 0
                                || token.indexOf('e') >= 0
                                || token.indexOf('E') >= 0
                                ? (Object) value.getAsDouble()
                                : (Object) value.getAsLong();
                    } else {
                        decoded = intern(pool, value.getAsString());
                    }
                } else {
                    // Boundary scalar rows deliberately carry two small
                    // arrays.  Preserve them for their dedicated accessors;
                    // ordinary scalar accessors still treat structure as
                    // absent, matching their legacy behavior.
                    decoded = value.deepCopy();
                }
                keys.add(intern(pool, entry.getKey()));
                values.add(decoded);
            }
            return new FlatJsonRow(keys.toArray(new String[0]),
                    values.toArray(), keys.size());
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
            if (value == MISSING || value == null
                    || value instanceof JsonElement) {
                return "";
            }
            return String.valueOf(value);
        }

        private long longValue(String key, long fallback) {
            Object value = find(key);
            if (value == MISSING || value == null
                    || value instanceof JsonElement) {
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
            if (value == MISSING || value == null
                    || value instanceof JsonElement) {
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
            if (value == MISSING || value == null
                    || value instanceof JsonElement) {
                return fallback;
            }
            if (value instanceof Boolean) {
                return (Boolean) value;
            }
            // JsonPrimitive.getAsBoolean parses any non-boolean primitive
            // with Boolean.parseBoolean.
            return Boolean.parseBoolean(String.valueOf(value));
        }

        private List<String> stringList(String key) {
            Object value = find(key);
            if (!(value instanceof JsonArray)) {
                return Collections.emptyList();
            }
            List<String> result = new ArrayList<>();
            for (JsonElement element : (JsonArray) value) {
                if (!element.isJsonPrimitive()) {
                    return Collections.emptyList();
                }
                result.add(element.getAsString());
            }
            return result;
        }

        private List<Integer> integerList(String key) {
            Object value = find(key);
            if (!(value instanceof JsonArray)) {
                return Collections.emptyList();
            }
            List<Integer> result = new ArrayList<>();
            for (JsonElement element : (JsonArray) value) {
                if (!element.isJsonPrimitive()
                        || !element.getAsJsonPrimitive().isNumber()) {
                    return Collections.emptyList();
                }
                result.add(element.getAsInt());
            }
            return result;
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
