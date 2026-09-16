package edu.uva.liftlab.graphchecker.runtime;

import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.ToNumberPolicy;
import com.google.gson.reflect.TypeToken;
import edu.uva.liftlab.graphchecker.annotation.Debug;
import edu.uva.liftlab.graphchecker.causynth.MapFields;
import edu.uva.liftlab.graphchecker.smt.JsonFields;
import edu.uva.liftlab.graphchecker.causynth.StaticProgram;
import edu.uva.liftlab.graphchecker.smt.JavaContainerTypes;

import edu.uva.liftlab.graphchecker.plan.SiteId;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.lang.reflect.Type;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.function.Function;
import java.util.Map;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.zip.GZIPOutputStream;

import static edu.uva.liftlab.graphchecker.causynth.MapFields.longNumber;
import static edu.uva.liftlab.graphchecker.causynth.MapFields.stringValue;

/** Refines the cheap static candidate graph with one concrete REGION_STATE
 * execution. */
final class RuntimeRefinedGraphBuilder {
    static final String GRAPH_KIND = "RUNTIME_REFINED_DATAFLOW";
    static final String FIELD_ACCESS_AUTHORITY =
            "EXACT_RUNTIME_ACTIVATION_FIELD_ACCESS_V1";

    private static final Type ROW_TYPE =
            new TypeToken<Map<String, Object>>() { }.getType();
    private static final Gson GSON = new GsonBuilder()
            .setObjectToNumberStrategy(ToNumberPolicy.LONG_OR_DOUBLE)
            .create();

    private RuntimeRefinedGraphBuilder() {
    }

    static Result refine(File candidateGraph,
                         List<StaticProgram.RegionRow> selectedSkeletons,
                         Collection<Map<String, Object>> runtimeInstances,
                         List<RuntimeRegionPlanner.MethodEvent> methods,
                         List<RuntimeRegionPlanner.RuntimeEvent> runtime,
                         List<RuntimeRegionPlanner.FieldAccessEvent> fields,
                         Path output) throws IOException {
        if (candidateGraph == null || !candidateGraph.isFile()) {
            throw new IOException("candidate static graph not found: "
                    + candidateGraph);
        }
        SkeletonCatalog skeletons = SkeletonCatalog.of(selectedSkeletons);
        Set<String> selectedMethods = skeletons.methods;
        List<RuntimeRegionPlanner.MethodEvent> methodEvents = sortedMethods(
                methods);
        List<RuntimeRegionPlanner.RuntimeEvent> runtimeEvents = sortedRuntime(
                runtime);
        List<RuntimeRegionPlanner.FieldAccessEvent> fieldEvents = sortedFields(
                fields);
        Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>> runtimeByCall =
                groupRuntime(runtimeEvents);
        Map<Long, List<RuntimeRegionPlanner.FieldAccessEvent>> fieldsByCall =
                groupFields(fieldEvents);

        Map<StaticSite, List<RuntimeFieldBinding>> bindingsBySite =
                new LinkedHashMap<>();
        Map<AccessorSite, List<RuntimeAccessorBinding>> accessorBindingsBySite =
                new LinkedHashMap<>();
        List<Activation> activations = activations(runtimeInstances,
                skeletons, methodEvents);
        for (Activation activation : activations) {
                RuntimeRegionPlanner.MethodEvent root = activation.root;
                Set<Long> calls = activation.calls;
                List<RuntimeRegionPlanner.RuntimeEvent> activationRuntime =
                        eventsForCalls(calls, runtimeByCall);
                Map<Long, RuntimeRegionPlanner.RuntimeEvent>
                        completedCalls = completedCalls(activationRuntime);
                Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>>
                        callArguments = callArguments(activationRuntime);
                collectAccessorBindings(activation, activationRuntime,
                        accessorBindingsBySite);
                List<RuntimeRegionPlanner.FieldAccessEvent> activationFields =
                        eventsForCalls(calls, fieldsByCall);
                if (activationFields.isEmpty()) {
                    continue;
                }
                Map<Integer, List<RuntimeRegionPlanner.FieldAccessEvent>>
                        fieldsByValueObject = fieldsByValueObject(
                        activationFields);
                for (RuntimeRegionPlanner.FieldAccessEvent field
                        : activationFields) {
                    StaticSite site = new StaticSite(field.method,
                            field.unitIndex, field.kind, field.field);
                    List<RuntimeFieldPath> fieldPaths =
                            observedFieldPaths(field);
                    for (RuntimeFieldPath path : fieldPaths) {
                        bindingsBySite.computeIfAbsent(site,
                                ignored -> new ArrayList<>()).add(
                                new RuntimeFieldBinding(activation.regionId,
                                        root, field, path,
                                        "ACTIVATION_FIELD_ACCESS",
                                        FIELD_ACCESS_AUTHORITY));
                    }
                }
                for (RuntimeRegionPlanner.RuntimeEvent event
                        : activationRuntime) {
                    if (!"CALL_SITE_ENTER".equals(event.kind)
                            || event.objectId == 0) {
                        continue;
                    }
                    RuntimeRegionPlanner.RuntimeEvent completion =
                            completedCalls.get(event.invocationId);
                    if (completion == null || completion.seq <= event.seq) {
                        continue;
                    }
                    int unitIndex = SiteId.unitIndexOf(event.siteId);
                    if (unitIndex < 0) continue;
                    for (RuntimeRegionPlanner.FieldAccessEvent container
                            : latestContainerFields(
                            fieldsByValueObject.getOrDefault(event.objectId,
                                    Collections.<RuntimeRegionPlanner.FieldAccessEvent>
                                            emptyList()),
                            event.seq)) {
                        String field = container.field;
                        StaticSite site = new StaticSite(event.method,
                                unitIndex, "FIELD_WRITE", field);
                        List<RuntimeFieldPath> containerPaths =
                                observedFieldPaths(container);
                        for (RuntimeFieldPath path : containerPaths) {
                            RuntimeRegionPlanner.FieldAccessEvent mutation =
                                    new RuntimeRegionPlanner.FieldAccessEvent(
                                            completion.seq, "FIELD_WRITE",
                                            event.method, event.callId,
                                            unitIndex, event.siteId, field,
                                            container.receiverObjectId,
                                            event.objectId, "");
                            bindingsBySite.computeIfAbsent(site,
                                    ignored -> new ArrayList<>()).add(
                                    new RuntimeFieldBinding(
                                            activation.regionId, root,
                                            mutation, path,
                                            "CONTAINER_MUTATION",
                                            FIELD_ACCESS_AUTHORITY,
                                            container, event, completion));
                        }
                    }
                }
        }

        final List<Map<String, Object>> refined = new ArrayList<>();
        // The candidate graph can be multi-gigabyte.
        streamRows(candidateGraph, candidate -> {
            requireCandidateEdge(candidate, candidateGraph);
            String method = stringValue(candidate.get("method"));
            if (!selectedMethods.contains(method)) {
                return;
            }
            Map<String, Object> edge = new LinkedHashMap<>(candidate);
            edge.put("graphKind", GRAPH_KIND);

            String transfer = stringValue(edge.get("transferKind"));
            List<String> regionIds = new ArrayList<>(values(
                    skeletons.regionsByMethod.get(method)));
            edge.put("regionIds", regionIds);
            if (Boolean.TRUE.equals(edge.get("explicitSymbolicFault"))) {
                List<RuntimeAccessorBinding> bindings = values(
                        accessorBindingsBySite.get(AccessorSite.from(edge)));
                if (bindings.isEmpty()) {
                    edge.put("runtimeObserved", false);
                } else {
                    edge.put("runtimeExplicitFaultBindings",
                            encodeExplicitFaultBindings(bindings));
                    edge.put("runtimeObserved", true);
                }
            } else if ("accessor_field_return".equals(
                    stringValue(edge.get("kind")))) {
                List<RuntimeAccessorBinding> bindings = values(
                        accessorBindingsBySite.get(AccessorSite.from(edge)));
                if (bindings.isEmpty()) {
                    edge.put("runtimeObserved", false);
                } else {
                    edge.put("runtimeAccessorBindings",
                            encodeAccessorBindings(bindings, edge));
                    edge.put("runtimeObserved", true);
                }
            } else if ("HEAP_READ".equals(transfer)
                    || "HEAP_WRITE".equals(transfer)) {
                StaticSite site = StaticSite.from(edge);
                List<RuntimeFieldBinding> bindings = values(
                        bindingsBySite.get(site));
                if (!bindings.isEmpty()) {
                    List<Map<String, Object>> encoded = encodeBindings(
                            bindings);
                    edge.put("runtimeFieldBindings", encoded);
                    List<String> uniquePath = uniqueFieldPath(bindings,
                            RuntimeFieldPath::fieldNames);
                    List<String> uniqueDeclarations = uniqueFieldPath(
                            bindings, RuntimeFieldPath::fieldDeclarations);
                    if (!uniquePath.isEmpty()) {
                        edge.put("fieldPath", uniquePath);
                        edge.put("fieldPathDeclarations", uniqueDeclarations);
                    }
                    edge.put("runtimeObserved", true);
                } else {
                    edge.put("runtimeObserved", false);
                }
            } else {
                edge.put("runtimeObserved", true);
            }
            refined.add(edge);
        });

        writeRows(output, refined);
        // Normalize retained rows to the exact value domain a JSONL
        // round-trip would produce (integral numbers become Long), so the
        // in-memory graph handed to later passes is indistinguishable from
        // re-reading the file this method just wrote.
        for (Map<String, Object> row : refined) {
            normalizeNumbersInPlace(row);
        }
        return new Result(refined);
    }

    /** Receives rows strictly in file order. */
    private interface RowSink {
        void accept(Map<String, Object> row) throws IOException;
    }

    /** Streams JSONL rows in file order while parsing batches on background
     * threads. */
    private static void streamRows(File file, RowSink sink)
            throws IOException {
        int threads = Math.max(1, Math.min(8,
                Runtime.getRuntime().availableProcessors() - 2));
        final int workerCount = threads;
        ExecutorService executor = Executors.newFixedThreadPool(workerCount,
                runnable -> {
                    Thread thread = new Thread(runnable,
                            "causynth-candidate-parse");
                    thread.setDaemon(true);
                    return thread;
                });
        try (BufferedReader input = MapFields.rowReader(file)) {
            ArrayDeque<Future<List<Map<String, Object>>>> pending =
                    new ArrayDeque<>();
            int batchCapacity = 4096;
            List<String> batch = new ArrayList<>(batchCapacity);
            String line;
            while ((line = input.readLine()) != null) {
                if (line.trim().isEmpty()) {
                    continue;
                }
                batch.add(line);
                if (batch.size() >= batchCapacity) {
                    final List<String> submitted = batch;
                    pending.addLast(executor.submit(
                            () -> parseBatch(submitted, file)));
                    batch = new ArrayList<>(batchCapacity);
                    while (pending.size() > workerCount * 2) {
                        drainBatch(pending.removeFirst(), sink);
                    }
                }
            }
            if (!batch.isEmpty()) {
                final List<String> submitted = batch;
                pending.addLast(executor.submit(
                        () -> parseBatch(submitted, file)));
            }
            while (!pending.isEmpty()) {
                drainBatch(pending.removeFirst(), sink);
            }
        } finally {
            executor.shutdownNow();
        }
    }

    private static void drainBatch(
            Future<List<Map<String, Object>>> future, RowSink sink)
            throws IOException {
        for (Map<String, Object> row : joinBatch(future)) {
            sink.accept(row);
        }
    }

    private static List<Map<String, Object>> parseBatch(
            List<String> lines, File file) throws IOException {
        List<Map<String, Object>> result = new ArrayList<>(lines.size());
        for (String line : lines) {
            Map<String, Object> row = GSON.fromJson(line, ROW_TYPE);
            if (row == null) {
                throw new IOException("null JSON row in " + file);
            }
            result.add(row);
        }
        return result;
    }

    private static List<Map<String, Object>> joinBatch(
            Future<List<Map<String, Object>>> future) throws IOException {
        try {
            return future.get();
        } catch (InterruptedException interrupted) {
            Thread.currentThread().interrupt();
            throw new IOException("candidate parse interrupted",
                    interrupted);
        } catch (ExecutionException failure) {
            Throwable cause = failure.getCause();
            if (cause instanceof IOException) {
                throw (IOException) cause;
            }
            if (cause instanceof RuntimeException) {
                throw (RuntimeException) cause;
            }
            throw new IOException("candidate parse failed", cause);
        }
    }

    /** Rewrites integral boxed numbers to Long in place, which is exactly the
     * value domain produced by writing with {@link JsonFields#WRITER} and parsing
     * with the LONG_OR_DOUBLE strategy. */
    @SuppressWarnings("unchecked")
    static void normalizeNumbersInPlace(Object value) {
        if (value instanceof Map<?, ?>) {
            Map<String, Object> map = (Map<String, Object>) value;
            for (Map.Entry<String, Object> entry : map.entrySet()) {
                Object entryValue = entry.getValue();
                Object normalized = normalizeScalar(entryValue);
                if (normalized != entryValue) {
                    entry.setValue(normalized);
                } else {
                    normalizeNumbersInPlace(entryValue);
                }
            }
        } else if (value instanceof List<?>) {
            List<Object> list = (List<Object>) value;
            for (int index = 0; index < list.size(); index++) {
                Object item = list.get(index);
                Object normalized = normalizeScalar(item);
                if (normalized != item) {
                    list.set(index, normalized);
                } else {
                    normalizeNumbersInPlace(item);
                }
            }
        }
    }

    /** The one integral/floating boxed domain a JSONL round-trip produces;
     * shared with the planner's deep copy so both state it once. */
    static Object normalizeScalar(Object value) {
        if (value instanceof Integer || value instanceof Short
                || value instanceof Byte) {
            return ((Number) value).longValue();
        }
        if (value instanceof Float) {
            return ((Number) value).doubleValue();
        }
        return value;
    }

    private static Map<Long, RuntimeRegionPlanner.RuntimeEvent>
            completedCalls(List<RuntimeRegionPlanner.RuntimeEvent> events) {
        Map<Long, RuntimeRegionPlanner.RuntimeEvent> result =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.RuntimeEvent event : events) {
            if ("CALL_SITE_RETURN".equals(event.kind)
                    && event.invocationId > 0L) {
                result.put(event.invocationId, event);
            }
        }
        return result;
    }

    private static Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>>
            callArguments(List<RuntimeRegionPlanner.RuntimeEvent> events) {
        Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>> result =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.RuntimeEvent event : events) {
            if ("CALL_ARGUMENT".equals(event.kind)
                    && event.invocationId > 0L
                    && event.argumentIndex >= 0) {
                result.computeIfAbsent(event.invocationId,
                        ignored -> new ArrayList<>()).add(event);
            }
        }
        return result;
    }

    private static void collectAccessorBindings(
            Activation activation,
            List<RuntimeRegionPlanner.RuntimeEvent> events,
            Map<AccessorSite, List<RuntimeAccessorBinding>> destination) {
        Map<Long, AccessorInvocation> entered = new LinkedHashMap<>();
        Map<AccessorSite, Integer> occurrences = new LinkedHashMap<>();
        for (RuntimeRegionPlanner.RuntimeEvent event : events) {
            AccessorSite site = AccessorSite.from(event);
            if (site == null) continue;
            if ("CALL_SITE_ENTER".equals(event.kind)
                    && event.invocationId > 0L
                    && (event.objectId != 0
                    || Debug.isBooleanMarkerSignature(
                    event.declaredCallee))) {
                int occurrence = occurrences.getOrDefault(site, 0) + 1;
                occurrences.put(site, occurrence);
                entered.put(event.invocationId,
                        new AccessorInvocation(site, event, occurrence));
            } else if ("CALL_SITE_RETURN".equals(event.kind)
                    && (!event.primitiveValue.isEmpty()
                    || event.objectId != 0)) {
                AccessorInvocation invocation = entered.remove(
                        event.invocationId);
                if (invocation == null || !invocation.site.equals(site)) {
                    continue;
                }
                destination.computeIfAbsent(site,
                        ignored -> new ArrayList<>()).add(
                        new RuntimeAccessorBinding(activation,
                                invocation.enter, event,
                                invocation.occurrence));
            }
        }
    }

    private static List<Activation> activations(
            Collection<Map<String, Object>> runtimeInstances,
            SkeletonCatalog skeletons,
            List<RuntimeRegionPlanner.MethodEvent> methods)
            throws IOException {
        Map<Long, RuntimeRegionPlanner.MethodEvent> methodByCall =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.MethodEvent method : methods) {
            methodByCall.put(method.callId, method);
        }
        List<Activation> result = new ArrayList<>();
        for (Map<String, Object> instance : runtimeInstances == null
                ? Collections.<Map<String, Object>>emptyList()
                : runtimeInstances) {
            if (!"RUNTIME_REGION_ACTIVATION".equals(
                    stringValue(instance.get("kind")))) {
                throw new IOException("invalid runtime activation supplied "
                        + "to refinement");
            }
            String regionId = stringValue(instance.get("regionId"));
            long rootCallId = longNumber(instance.get("rootCallId"), -1L);
            RuntimeRegionPlanner.MethodEvent root =
                    methodByCall.get(rootCallId);
            if (!skeletons.regions.contains(regionId) || root == null) {
                throw new IOException("runtime activation cannot be bound to "
                        + "selected skeleton: " + regionId + "#call"
                        + rootCallId);
            }
            Set<Long> calls = MapFields.longValues(instance.get("callIds"));
            if (calls.isEmpty() || !calls.contains(rootCallId)) {
                throw new IOException("runtime activation has no rooted call "
                        + "subtree: " + regionId + "#call" + rootCallId);
            }
            result.add(new Activation(regionId, root, calls));
        }
        if (result.isEmpty()) {
            throw new IOException("runtime refinement requires selected "
                    + "region activations");
        }
        return result;
    }

    private static Map<Integer, List<RuntimeRegionPlanner.FieldAccessEvent>>
            fieldsByValueObject(
            List<RuntimeRegionPlanner.FieldAccessEvent> fields) {
        Map<Integer, List<RuntimeRegionPlanner.FieldAccessEvent>> result =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.FieldAccessEvent event : fields) {
            if (event.valueObjectId != 0) {
                result.computeIfAbsent(event.valueObjectId,
                        ignored -> new ArrayList<>()).add(event);
            }
        }
        return result;
    }

    private static List<RuntimeRegionPlanner.FieldAccessEvent>
            latestContainerFields(
            List<RuntimeRegionPlanner.FieldAccessEvent> fields,
            long beforeSeq) {
        Map<String, RuntimeRegionPlanner.FieldAccessEvent> selected =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.FieldAccessEvent event : fields) {
            if (event.seq > beforeSeq) {
                continue;
            }
            String identity = event.field + "\n" + event.receiverObjectId;
            RuntimeRegionPlanner.FieldAccessEvent previous =
                    selected.get(identity);
            if (previous == null || event.seq > previous.seq) {
                selected.put(identity, event);
            }
        }
        return new ArrayList<>(selected.values());
    }

    private static List<RuntimeFieldPath> observedFieldPaths(
            RuntimeRegionPlanner.FieldAccessEvent event) {
        RuntimeRoot root = new RuntimeRoot("OBSERVED_FIELD_RECEIVER",
                event.method, event.siteId + ".fieldReceiver", -1,
                event.receiverObjectId);
        RuntimeFieldPath path = RuntimeFieldPath.root(root).append(
                event.field, event.receiverObjectId, event.valueObjectId);
        return path == null ? Collections.emptyList()
                : Collections.singletonList(path);
    }

    private static void requireCandidateEdge(Map<String, Object> edge,
                                             File source)
            throws IOException {
        if (integer(edge.get("schemaVersion"), -1) != 3) {
            throw new IOException("invalid candidate graph row in " + source
                    + "; run the schema-3 static analysis again");
        }
    }

    private static List<Map<String, Object>> encodeBindings(
            Collection<RuntimeFieldBinding> bindings) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RuntimeFieldBinding binding : bindings) {
            unique.put(JsonFields.WRITER.toJson(binding.toMap()), binding.toMap());
        }
        return new ArrayList<>(unique.values());
    }

    private static List<Map<String, Object>> encodeAccessorBindings(
            Collection<RuntimeAccessorBinding> bindings,
            Map<String, Object> edge) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RuntimeAccessorBinding binding : bindings) {
            Map<String, Object> encoded = binding.toMap(edge);
            unique.put(JsonFields.WRITER.toJson(encoded), encoded);
        }
        return new ArrayList<>(unique.values());
    }

    private static List<Map<String, Object>> encodeExplicitFaultBindings(
            Collection<RuntimeAccessorBinding> bindings) {
        Map<String, Map<String, Object>> unique = new LinkedHashMap<>();
        for (RuntimeAccessorBinding binding : bindings) {
            Map<String, Object> encoded = binding.toMap(
                    Collections.<String, Object>emptyMap());
            encoded.remove("receiverObjectId");
            encoded.remove("receiverRuntimeType");
            encoded.remove("declaredFieldSignature");
            encoded.remove("accessorImplementationMethod");
            encoded.put("authority",
                    "EXACT_RUNTIME_EXPLICIT_FAULT_RETURN_V1");
            unique.put(JsonFields.WRITER.toJson(encoded), encoded);
        }
        return new ArrayList<>(unique.values());
    }

    /**
     * The one field path every binding of an edge states, read through
     * {@code spelling}; no path at all when two bindings disagree, because
     * an edge that two accesses spell differently has no single path.
     */
    private static List<String> uniqueFieldPath(
            Collection<RuntimeFieldBinding> bindings,
            Function<RuntimeFieldPath, List<String>> spelling) {
        List<String> selected = null;
        for (RuntimeFieldBinding binding : bindings) {
            List<String> path = spelling.apply(binding.path);
            if (selected == null) {
                selected = path;
            } else if (!selected.equals(path)) {
                return Collections.emptyList();
            }
        }
        return selected == null ? Collections.emptyList() : selected;
    }

    private static Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>>
    groupRuntime(List<RuntimeRegionPlanner.RuntimeEvent> events) {
        Map<Long, List<RuntimeRegionPlanner.RuntimeEvent>> result =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.RuntimeEvent event : events) {
            result.computeIfAbsent(event.callId,
                    ignored -> new ArrayList<>()).add(event);
        }
        return result;
    }

    private static Map<Long, List<RuntimeRegionPlanner.FieldAccessEvent>>
    groupFields(List<RuntimeRegionPlanner.FieldAccessEvent> events) {
        Map<Long, List<RuntimeRegionPlanner.FieldAccessEvent>> result =
                new LinkedHashMap<>();
        for (RuntimeRegionPlanner.FieldAccessEvent event : events) {
            result.computeIfAbsent(event.callId,
                    ignored -> new ArrayList<>()).add(event);
        }
        return result;
    }

    private static <T> List<T> eventsForCalls(Set<Long> calls,
                                               Map<Long, List<T>> byCall) {
        List<T> result = new ArrayList<>();
        for (Long call : calls) {
            result.addAll(values(byCall.get(call)));
        }
        result.sort(Comparator.comparingLong(RuntimeRefinedGraphBuilder::seq));
        return result;
    }


    private static long seq(Object event) {
        if (event instanceof RuntimeRegionPlanner.RuntimeEvent) {
            return ((RuntimeRegionPlanner.RuntimeEvent) event).seq;
        }
        return ((RuntimeRegionPlanner.FieldAccessEvent) event).seq;
    }

    private static List<RuntimeRegionPlanner.MethodEvent> sortedMethods(
            Collection<RuntimeRegionPlanner.MethodEvent> events) {
        List<RuntimeRegionPlanner.MethodEvent> result = new ArrayList<>(
                events == null ? Collections.emptyList() : events);
        result.sort(Comparator.comparingLong(value -> value.seq));
        return result;
    }

    private static List<RuntimeRegionPlanner.RuntimeEvent> sortedRuntime(
            Collection<RuntimeRegionPlanner.RuntimeEvent> events) {
        List<RuntimeRegionPlanner.RuntimeEvent> result = new ArrayList<>(
                events == null ? Collections.emptyList() : events);
        result.sort(Comparator.comparingLong(value -> value.seq));
        return result;
    }

    private static List<RuntimeRegionPlanner.FieldAccessEvent> sortedFields(
            Collection<RuntimeRegionPlanner.FieldAccessEvent> events) {
        List<RuntimeRegionPlanner.FieldAccessEvent> result = new ArrayList<>(
                events == null ? Collections.emptyList() : events);
        result.sort(Comparator.comparingLong(value -> value.seq));
        return result;
    }

    private static void writeRows(Path output,
                                  Collection<Map<String, Object>> rows)
            throws IOException {
        Path parent = output.getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        OutputStream stream = Files.newOutputStream(output);
        try {
            if (output.getFileName().toString().endsWith(".gz")) {
                stream = new GZIPOutputStream(stream);
            }
        } catch (IOException failure) {
            stream.close();
            throw failure;
        }
        try (BufferedWriter writer = new BufferedWriter(
                new OutputStreamWriter(stream, StandardCharsets.UTF_8))) {
            for (Map<String, Object> row : rows) {
                writer.write(JsonFields.WRITER.toJson(row));
                writer.write('\n');
            }
        }
        String name = output.getFileName().toString();
        if (name.endsWith(".gz")) {
            Files.deleteIfExists(output.resolveSibling(
                    name.substring(0, name.length() - 3)));
        }
    }

    private static String fieldName(String declaration) {
        if (declaration == null || declaration.length() < 5
                || declaration.charAt(0) != '<'
                || declaration.charAt(declaration.length() - 1) != '>') {
            return "";
        }
        int colon = declaration.indexOf(':');
        int end = declaration.length() - 1;
        int separator = declaration.lastIndexOf(' ', end - 1);
        if (colon <= 1 || separator <= colon
                || declaration.indexOf('(', colon) >= 0
                || separator + 1 >= end) {
            return "";
        }
        return declaration.substring(separator + 1, end);
    }

    private static int integer(Object value, int fallback) {
        if (value instanceof Number) {
            return ((Number) value).intValue();
        }
        try {
            return Integer.parseInt(stringValue(value));
        } catch (RuntimeException ignored) {
            return fallback;
        }
    }



    private static <T> List<T> values(List<T> values) {
        return values == null ? Collections.emptyList() : values;
    }

    static final class Result {
        /** Refined rows, normalized to the exact JSONL round-trip domain. */
        final List<Map<String, Object>> rows;

        private Result(List<Map<String, Object>> rows) {
            this.rows = rows;
        }
    }

    /** The two method indexes refinement needs, over the decoded skeletons. */
    private static final class SkeletonCatalog {
        private final Set<String> methods = new LinkedHashSet<>();
        private final Set<String> regions = new LinkedHashSet<>();
        private final Map<String, List<String>> regionsByMethod =
                new LinkedHashMap<>();

        private static SkeletonCatalog of(
                List<StaticProgram.RegionRow> skeletons) throws IOException {
            SkeletonCatalog result = new SkeletonCatalog();
            for (StaticProgram.RegionRow skeleton : skeletons) {
                result.regions.add(skeleton.regionId);
                for (String method : skeleton.methods) {
                    result.methods.add(method);
                    result.regionsByMethod.computeIfAbsent(method,
                            ignored -> new ArrayList<>())
                            .add(skeleton.regionId);
                }
            }
            if (result.methods.isEmpty()) {
                throw new IOException("selected skeletons contain no methods");
            }
            return result;
        }
    }

    private static final class Activation {
        private final String regionId;
        private final RuntimeRegionPlanner.MethodEvent root;
        private final Set<Long> calls;
        private Activation(String regionId,
                           RuntimeRegionPlanner.MethodEvent root,
                           Set<Long> calls) {
            this.regionId = regionId;
            this.root = root;
            this.calls = calls;
        }
    }

    private static final class StaticSite {
        private final String method;
        private final int unitIndex;
        private final String operation;
        private final String field;

        private StaticSite(String method, int unitIndex, String operation,
                           String field) {
            this.method = stringValue(method);
            this.unitIndex = unitIndex;
            this.operation = stringValue(operation);
            this.field = stringValue(field);
        }

        private static StaticSite from(Map<String, Object> edge) {
            String transfer = stringValue(edge.get("transferKind"));
            boolean read = "HEAP_READ".equals(transfer);
            return new StaticSite(stringValue(edge.get("method")),
                    integer(edge.get("unitIndex"), -1),
                    read ? "FIELD_READ" : "FIELD_WRITE",
                    read ? stringValue(edge.get("fromCell"))
                            : stringValue(edge.get("toCell")));
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof StaticSite)) {
                return false;
            }
            StaticSite site = (StaticSite) other;
            return unitIndex == site.unitIndex && method.equals(site.method)
                    && operation.equals(site.operation)
                    && field.equals(site.field);
        }

        @Override
        public int hashCode() {
            int result = method.hashCode();
            result = 31 * result + unitIndex;
            result = 31 * result + operation.hashCode();
            return 31 * result + field.hashCode();
        }
    }

    private static final class AccessorSite {
        private final String method;
        private final String siteId;
        private final String declaredCallee;

        private AccessorSite(String method, String siteId,
                             String declaredCallee) {
            this.method = stringValue(method);
            this.siteId = stringValue(siteId);
            this.declaredCallee = stringValue(declaredCallee);
        }

        private static AccessorSite from(Map<String, Object> edge) {
            return new AccessorSite(stringValue(edge.get("method")),
                    stringValue(edge.get("siteId")),
                    stringValue(edge.get("invoke")));
        }

        private static AccessorSite from(
                RuntimeRegionPlanner.RuntimeEvent event) {
            if (event == null
                    || !("CALL_SITE_ENTER".equals(event.kind)
                    || "CALL_SITE_RETURN".equals(event.kind))
                    || event.method.isEmpty() || event.siteId.isEmpty()
                    || event.declaredCallee.isEmpty()) {
                return null;
            }
            return new AccessorSite(event.method, event.siteId,
                    event.declaredCallee);
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof AccessorSite)) return false;
            AccessorSite site = (AccessorSite) other;
            return method.equals(site.method) && siteId.equals(site.siteId)
                    && declaredCallee.equals(site.declaredCallee);
        }

        @Override
        public int hashCode() {
            int result = method.hashCode();
            result = 31 * result + siteId.hashCode();
            return 31 * result + declaredCallee.hashCode();
        }
    }

    private static final class AccessorInvocation {
        private final AccessorSite site;
        private final RuntimeRegionPlanner.RuntimeEvent enter;
        private final int occurrence;

        private AccessorInvocation(AccessorSite site,
                                   RuntimeRegionPlanner.RuntimeEvent enter,
                                   int occurrence) {
            this.site = site;
            this.enter = enter;
            this.occurrence = occurrence;
        }
    }

    private static final class RuntimeAccessorBinding {
        private final Activation activation;
        private final RuntimeRegionPlanner.RuntimeEvent enter;
        private final RuntimeRegionPlanner.RuntimeEvent returned;
        private final int occurrence;

        private RuntimeAccessorBinding(
                Activation activation,
                RuntimeRegionPlanner.RuntimeEvent enter,
                RuntimeRegionPlanner.RuntimeEvent returned,
                int occurrence) {
            this.activation = activation;
            this.enter = enter;
            this.returned = returned;
            this.occurrence = occurrence;
        }

        private Map<String, Object> toMap(Map<String, Object> edge) {
            Map<String, Object> result = new LinkedHashMap<>();
            result.put("regionId", activation.regionId);
            result.put("rootCallId", activation.root.callId);
            result.put("callId", enter.callId);
            result.put("invocationId", enter.invocationId);
            result.put("callerMethod", enter.method);
            result.put("unitIndex", SiteId.unitIndexOf(enter.siteId));
            result.put("siteId", enter.siteId);
            result.put("eventSeq", returned.seq);
            result.put("receiverObjectId", enter.objectId);
            result.put("receiverRuntimeType", enter.runtimeType);
            result.put("primitiveValue", returned.primitiveValue);
            if (returned.objectId != 0) {
                result.put("valueObjectId", returned.objectId);
            }
            result.put("accessorOccurrence", occurrence);
            result.put("declaredCallee", enter.declaredCallee);
            result.put("declaredFieldSignature",
                    edge.get("declaredFieldSignature"));
            result.put("accessorImplementationMethod",
                    edge.get("accessorImplementationMethod"));
            result.put("sourceKey", activation.root.sourceKey);
            result.put("authority",
                    "EXACT_RUNTIME_ACCESSOR_RECEIVER_RETURN_V1");
            return result;
        }
    }

    private static final class RuntimeFieldBinding {
        private final String regionId;
        private final RuntimeRegionPlanner.MethodEvent root;
        private final RuntimeRegionPlanner.FieldAccessEvent event;
        private final RuntimeFieldPath path;

        private final String bindingKind;
        private final String authority;
        private final RuntimeRegionPlanner.FieldAccessEvent containerRead;
        private final RuntimeRegionPlanner.RuntimeEvent mutationEnter;
        private final RuntimeRegionPlanner.RuntimeEvent mutationCompletion;

        private RuntimeFieldBinding(String regionId,
                                    RuntimeRegionPlanner.MethodEvent root,
                                    RuntimeRegionPlanner.FieldAccessEvent event,
                                    RuntimeFieldPath path,
                                    String bindingKind,
                                    String authority) {
            this(regionId, root, event, path, bindingKind, authority,
                    null, null, null);
        }

        private RuntimeFieldBinding(String regionId,
                                    RuntimeRegionPlanner.MethodEvent root,
                                    RuntimeRegionPlanner.FieldAccessEvent event,
                                    RuntimeFieldPath path,
                                    String bindingKind,
                                    String authority,
                                    RuntimeRegionPlanner.FieldAccessEvent containerRead,
                                    RuntimeRegionPlanner.RuntimeEvent mutationEnter,
                                    RuntimeRegionPlanner.RuntimeEvent mutationCompletion) {
            this.regionId = regionId;
            this.root = root;
            this.event = event;
            this.path = path;
            this.bindingKind = bindingKind;
            this.authority = authority;
            this.containerRead = containerRead;
            this.mutationEnter = mutationEnter;
            this.mutationCompletion = mutationCompletion;
        }

        private Map<String, Object> toMap() {
            Map<String, Object> result = new LinkedHashMap<>();
            result.put("regionId", regionId);
            result.put("rootCallId", root.callId);
            result.put("callId", event.callId);
            result.put("siteId", event.siteId);
            result.put("eventSeq", event.seq);
            result.put("rootKind", path.root.kind);
            result.put("rootMethod", path.root.method);
            result.put("sourceKey", root.sourceKey);
            result.put("rootCell", path.root.cell);
            if (path.root.parameterIndex >= 0) {
                result.put("rootParameterIndex", path.root.parameterIndex);
            }
            result.put("rootObjectId", path.root.objectId);
            result.put("fieldReceiverObjectId", event.receiverObjectId);
            result.put("valueObjectId", event.valueObjectId);
            result.put("primitiveValue", event.primitiveValue);
            result.put("fieldPath", path.fieldNames());
            result.put("fieldPathDeclarations", path.fieldDeclarations());
            result.put("authority", authority);
            result.put("bindingKind", bindingKind);
            if (containerRead != null && mutationEnter != null
                    && mutationCompletion != null) {
                result.put("writerFieldReadSeq", containerRead.seq);
                result.put("mutatorEnterSeq", mutationEnter.seq);
                result.put("mutationCompletionSeq", mutationCompletion.seq);
                result.put("mutationInvocationId",
                        mutationEnter.invocationId);
                result.put("mutatorDeclaredCallee",
                        mutationEnter.declaredCallee);
            }
            return result;
        }

    }

    private static final class RuntimeRoot {
        private final String kind;
        private final String method;
        private final String cell;
        private final int parameterIndex;
        private final int objectId;

        private RuntimeRoot(String kind, String method, String cell,
                            int parameterIndex, int objectId) {
            this.kind = kind;
            this.method = method;
            this.cell = cell;
            this.parameterIndex = parameterIndex;
            this.objectId = objectId;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof RuntimeRoot)) {
                return false;
            }
            RuntimeRoot root = (RuntimeRoot) other;
            return parameterIndex == root.parameterIndex
                    && objectId == root.objectId && kind.equals(root.kind)
                    && method.equals(root.method) && cell.equals(root.cell);
        }

        @Override
        public int hashCode() {
            int result = kind.hashCode();
            result = 31 * result + method.hashCode();
            result = 31 * result + cell.hashCode();
            result = 31 * result + parameterIndex;
            return 31 * result + objectId;
        }
    }

    private static final class RuntimeFieldPath {
        private final RuntimeRoot root;
        private final List<String> fields;
        private final Set<Integer> objectIds;

        private RuntimeFieldPath(RuntimeRoot root, List<String> fields,
                                 Set<Integer> objectIds) {
            this.root = root;
            this.fields = fields;
            this.objectIds = objectIds;
        }

        private static RuntimeFieldPath root(RuntimeRoot root) {
            Set<Integer> ids = new LinkedHashSet<>();
            ids.add(root.objectId);
            return new RuntimeFieldPath(root, Collections.emptyList(), ids);
        }

        private RuntimeFieldPath append(String field, int receiverObjectId,
                                        int valueObjectId) {
            if (fieldName(field).isEmpty()
                    || !objectIds.contains(receiverObjectId)
                    || valueObjectId != 0 && objectIds.contains(valueObjectId)) {
                return null;
            }
            List<String> nextFields = new ArrayList<>(fields);
            nextFields.add(field);
            Set<Integer> nextIds = new LinkedHashSet<>(objectIds);
            if (valueObjectId != 0) {
                nextIds.add(valueObjectId);
            }
            return new RuntimeFieldPath(root, nextFields, nextIds);
        }

        private List<String> fieldNames() {
            List<String> result = new ArrayList<>();
            for (String field : fields) {
                result.add(fieldName(field));
            }
            return result;
        }

        private List<String> fieldDeclarations() {
            return new ArrayList<>(fields);
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof RuntimeFieldPath)) {
                return false;
            }
            RuntimeFieldPath path = (RuntimeFieldPath) other;
            return root.equals(path.root) && fields.equals(path.fields);
        }

        @Override
        public int hashCode() {
            return 31 * root.hashCode() + fields.hashCode();
        }
    }
}
