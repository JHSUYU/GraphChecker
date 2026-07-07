package edu.uva.liftlab.graphchecker.runtime;

import java.io.BufferedWriter;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
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
    private static final int DEFAULT_MAX_EVENTS = 200000;
    private static final int DEFAULT_MAX_GRAPH_EDGES = 50000;
    private static final int DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE = 2000;

    private static volatile File outputDir;
    private static volatile File traceFile;
    private static volatile String testName;
    private static volatile int maxEvents;
    private static volatile int maxGraphEdges;
    private static volatile int maxContextPairsPerEdge;
    private static BufferedWriter traceWriter;

    private CausynthTraceRecorder() {
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
        Thread thread = Thread.currentThread();
        String threadName = thread.getName();
        long tid = thread.getId();
        int objectId = receiver == null ? 0 : System.identityHashCode(receiver);
        String process = inferProcessName(method, threadName);
        long timeNanos = System.nanoTime();
        TraceEvent event = new TraceEvent(id, testName, process, threadName, tid,
                method, objectId, timeNanos);
        synchronized (LOCK) {
            EVENTS.add(event);
            MethodContext context = CONTEXTS.get(event.contextKey());
            if (context == null) {
                context = new MethodContext(event);
                CONTEXTS.put(event.contextKey(), context);
            }
            context.observe(event);
            writeTraceLine(event);
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
        String process = inferProcessName(method, threadName);
        long timeNanos = System.nanoTime();
        FieldEvent event = new FieldEvent(id, testName, process, threadName, tid,
                method, methodObjectId, unitIndex, kind, field, receiverObjectId,
                valueObjectId, primitiveValue, timeNanos);
        synchronized (LOCK) {
            FIELD_EVENTS.add(event);
            String key = fieldEventKey(event.process, event.threadName, event.tid,
                    event.method, event.methodObjectId, event.unitIndex, event.field);
            FIELD_EVENTS_BY_CONTEXT_UNIT.put(key, event);
            writeFieldTraceLine(event);
        }
    }

    private static void initialize() {
        if (!INITIALIZED.compareAndSet(false, true)) {
            return;
        }
        testName = firstNonBlank(System.getProperty("causynth.trace.test"),
                System.getenv("CAUSYNTH_TRACE_TEST"), "unknown-test");
        maxEvents = parseInt(firstNonBlank(System.getProperty("causynth.trace.max.events"),
                System.getenv("CAUSYNTH_TRACE_MAX_EVENTS"),
                String.valueOf(DEFAULT_MAX_EVENTS)), DEFAULT_MAX_EVENTS);
        maxGraphEdges = parseInt(firstNonBlank(System.getProperty("causynth.trace.max.graph.edges"),
                System.getenv("CAUSYNTH_TRACE_MAX_GRAPH_EDGES"),
                String.valueOf(DEFAULT_MAX_GRAPH_EDGES)), DEFAULT_MAX_GRAPH_EDGES);
        maxContextPairsPerEdge = parseInt(firstNonBlank(
                System.getProperty("causynth.trace.max.context.pairs.per.edge"),
                System.getenv("CAUSYNTH_TRACE_MAX_CONTEXT_PAIRS_PER_EDGE"),
                String.valueOf(DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE)),
                DEFAULT_MAX_CONTEXT_PAIRS_PER_EDGE);
        outputDir = new File(firstNonBlank(System.getProperty("causynth.trace.output.dir"),
                System.getenv("CAUSYNTH_TRACE_OUTPUT_DIR"),
                "target/causynth-trace"));
        traceFile = new File(outputDir, "runtime_trace.jsonl");
        if (!outputDir.exists()) {
            outputDir.mkdirs();
        }
        try {
            traceWriter = new BufferedWriter(new FileWriter(traceFile, false));
        } catch (IOException ignored) {
            traceWriter = null;
        }
        Runtime.getRuntime().addShutdownHook(new Thread(new Runnable() {
            @Override
            public void run() {
                shutdown();
            }
        }, "causynth-trace-shutdown"));
    }

    private static void shutdown() {
        synchronized (LOCK) {
            if (traceWriter != null) {
                try {
                    traceWriter.flush();
                    traceWriter.close();
                } catch (IOException ignored) {
                }
                traceWriter = null;
            }
            try {
                if (aggregateOnShutdown()) {
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
                    addTraceEvent(new TraceEvent(
                            jsonLongField(line, "seq", 0L),
                            firstNonBlank(jsonField(line, "test"), testName),
                            jsonField(line, "process"),
                            jsonField(line, "threadName"),
                            jsonLongField(line, "tid", 0L),
                            jsonField(line, "method"),
                            jsonIntField(line, "objectId", 0),
                            jsonLongField(line, "timeNanos", 0L)));
                } else if ("FIELD_READ".equals(eventKind)
                        || "FIELD_WRITE".equals(eventKind)) {
                    addFieldEvent(new FieldEvent(
                            jsonLongField(line, "seq", 0L),
                            firstNonBlank(jsonField(line, "test"), testName),
                            jsonField(line, "process"),
                            jsonField(line, "threadName"),
                            jsonLongField(line, "tid", 0L),
                            jsonField(line, "method"),
                            jsonIntField(line, "objectId", 0),
                            jsonIntField(line, "unitIndex", -1),
                            eventKind,
                            jsonField(line, "field"),
                            jsonIntField(line, "fieldReceiverObjectId", 0),
                            jsonIntField(line, "valueObjectId", 0),
                            jsonField(line, "primitiveValue"),
                            jsonLongField(line, "timeNanos", 0L)));
                }
            }
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
                    "timeNanos", event.timeNanos));
            traceWriter.newLine();
        } catch (IOException ignored) {
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
                    "unitIndex", event.unitIndex,
                    "field", event.field,
                    "fieldReceiverObjectId", event.receiverObjectId,
                    "valueObjectId", event.valueObjectId,
                    "primitiveValue", event.primitiveValue,
                    "timeNanos", event.timeNanos));
            traceWriter.newLine();
        } catch (IOException ignored) {
        }
    }

    private static void writeInstantiatedGraph() {
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
        List<String> edgeJson = new ArrayList<>();
        Set<String> emittedNodes = new LinkedHashSet<>();
        Map<String, EdgeAccumulator> emittedEdges = new LinkedHashMap<>();
        List<String> roleNodeJson = new ArrayList<>();
        List<String> roleEdgeJson = new ArrayList<>();
        Set<String> emittedRoleNodes = new LinkedHashSet<>();
        Map<String, EdgeAccumulator> emittedRoleEdges = new LinkedHashMap<>();
        int mergedEdgeInputCount = 0;
        int mergedRoleEdgeInputCount = 0;
        int skippedGraphEdgeInstances = 0;
        int skippedRoleGraphEdgeInstances = 0;
        boolean truncated = false;
        boolean roleTruncated = false;
        for (StaticEdge edge : staticEdges) {
            List<InstantiatedContextPair> contexts = contextsForGraphEdge(edge,
                    contextsByMethod);
            for (InstantiatedContextPair context : contexts) {
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
        int edgeIndex = 0;
        for (EdgeAccumulator edge : emittedEdges.values()) {
            edgeJson.add(edge.toJson("DYN." + edgeIndex++));
        }
        int roleEdgeIndex = 0;
        for (EdgeAccumulator edge : emittedRoleEdges.values()) {
            roleEdgeJson.add(edge.toRoleJson("ROLE." + roleEdgeIndex++));
        }

        String summary = jsonObject(
                "test", testName,
                "traceFile", traceFile == null ? "" : traceFile.getPath(),
                "staticGraph", staticGraph.getPath(),
                "traceEventCount", EVENTS.size(),
                "fieldEventCount", FIELD_EVENTS.size(),
                "observedMethodContextCount", CONTEXTS.size(),
                "observedMethodCount", contextsByMethod.size(),
                "staticEdgeCount", staticEdges.size(),
                "instantiatedNodeCount", nodeJson.size(),
                "instantiatedEdgeCount", edgeJson.size(),
                "mergedEdgeInputCount", mergedEdgeInputCount,
                "roleMergedNodeCount", roleNodeJson.size(),
                "roleMergedEdgeCount", roleEdgeJson.size(),
                "mergedRoleEdgeInputCount", mergedRoleEdgeInputCount,
                "runtimeFieldBridgeInputCount", runtimeFieldBridgeStats.inputCount,
                "runtimeFieldBridgeMergedInputCount", runtimeFieldBridgeStats.mergedInputCount,
                "runtimeRoleFieldBridgeMergedInputCount", runtimeFieldBridgeStats.roleMergedInputCount,
                "skippedGraphEdgeInstances", skippedGraphEdgeInstances,
                "skippedRoleGraphEdgeInstances", skippedRoleGraphEdgeInstances,
                "skippedRuntimeFieldBridgeInstances", runtimeFieldBridgeStats.skippedGraphEdgeInstances,
                "skippedRuntimeRoleFieldBridgeInstances", runtimeFieldBridgeStats.skippedRoleGraphEdgeInstances,
                "truncated", truncated,
                "roleTruncated", roleTruncated,
                "maxEvents", maxEvents,
                "maxGraphEdges", maxGraphEdges,
                "maxContextPairsPerEdge", maxContextPairsPerEdge);
        String graph = "{"
                + "\"summary\":" + summary
                + ",\"nodes\":[" + join(nodeJson) + "]"
                + ",\"edges\":[" + join(edgeJson) + "]"
                + "}";
        String roleGraph = "{"
                + "\"summary\":" + summary
                + ",\"nodes\":[" + join(roleNodeJson) + "]"
                + ",\"edges\":[" + join(roleEdgeJson) + "]"
                + "}";
        writeFile(new File(outputDir, "unit_test_instantiated_graph.json"), graph);
        writeFile(new File(outputDir, "unit_test_role_merged_graph.json"), roleGraph);
        writeFile(new File(outputDir, "summary.json"), summary);
        writeSeedChainSummary(staticEdges);
        writeRuntimeValidationSummary(staticEdges, contextsByMethod);
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

    private static List<InstantiatedContextPair> contextsForGraphEdge(StaticEdge edge,
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
            return Collections.emptyList();
        }
        List<InstantiatedContextPair> pairs = new ArrayList<>();
        int limit = Math.max(1, maxContextPairsPerEdge);
        for (MethodContext context : contexts) {
            pairs.add(new InstantiatedContextPair(context, context));
            if (pairs.size() >= limit) {
                return pairs;
            }
        }
        return pairs;
    }

    private static List<InstantiatedContextPair> pairContexts(
            List<MethodContext> fromContexts, List<MethodContext> toContexts) {
        List<InstantiatedContextPair> pairs = new ArrayList<>();
        int limit = Math.max(1, maxContextPairsPerEdge);
        for (MethodContext fromContext : fromContexts) {
            for (MethodContext toContext : toContexts) {
                pairs.add(new InstantiatedContextPair(fromContext, toContext));
                if (pairs.size() >= limit) {
                    return pairs;
                }
            }
        }
        return pairs;
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
        return kind.contains("rpc") || kind.contains("hdfs_sasl");
    }

    private static String crossBoundaryRelation(String kind) {
        if (kind == null) {
            return "cross_boundary_mapping";
        }
        String lower = kind.toLowerCase(Locale.ROOT);
        if (lower.contains("rpc")) {
            return "rpc_field_mapping";
        }
        if (lower.contains("hdfs_sasl")) {
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

    private static final class TraceEvent {
        private final long id;
        private final String testName;
        private final String process;
        private final String threadName;
        private final long tid;
        private final String method;
        private final int objectId;
        private final long timeNanos;

        private TraceEvent(long id, String testName, String process, String threadName,
                           long tid, String method, int objectId, long timeNanos) {
            this.id = id;
            this.testName = testName;
            this.process = process;
            this.threadName = threadName;
            this.tid = tid;
            this.method = method;
            this.objectId = objectId;
            this.timeNanos = timeNanos;
        }

        private String contextKey() {
            return process + "|" + threadName + "|" + tid + "|" + objectId + "|" + method;
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
        private final long timeNanos;

        private FieldEvent(long id, String testName, String process, String threadName,
                           long tid, String method, int methodObjectId, int unitIndex,
                           String kind, String field, int receiverObjectId,
                           int valueObjectId, String primitiveValue, long timeNanos) {
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
            this.timeNanos = timeNanos;
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
            lastSeq = event.id;
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
